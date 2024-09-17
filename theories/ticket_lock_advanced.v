From iris.algebra Require Import auth excl gset numbers.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.

(* ################################################################# *)
(** * Case Study: Ticket Lock Advanced *)

(**
  The implementation, resource algebra, and representation predicates
  are identical to the original Ticket Lock chapter. Only the proofs
  differ.
*)

(* ================================================================= *)
(** ** Implementation *)

Definition mk_lock : val :=
  λ: <>, (ref #0, ref #0).

Definition wait : val :=
  rec: "wait" "n" "l" :=
  let: "o" := !(Fst "l") in
  if: "o" = "n" then #() else "wait" "n" "l".

Definition acquire : val :=
  rec: "acquire" "l" :=
  let: "n" := !(Snd "l") in
  if: CAS (Snd "l") "n" ("n" + #1) then
    wait "n" "l"
  else
    "acquire" "l".

Definition release : val :=
  λ: "l", Fst "l" <- ! (Fst "l") + #1.

(* ================================================================= *)
(** ** Representation Predicates *)

Definition RA : cmra :=
  authR (prodUR (optionUR (exclR natO)) (gset_disjR nat)).

Section proofs.
Context `{!heapGS Σ, !inG Σ RA}.
Let N := nroot .@ "ticket_lock".

Definition locked_by (γ : gname) (o : nat) : iProp Σ :=
  own γ (◯ (Excl' o, GSet ∅)).

Definition locked (γ : gname) : iProp Σ :=
  ∃ o, locked_by γ o.

Lemma locked_excl γ : locked γ -∗ locked γ -∗ False.
Proof.
  iIntros "[%o1 H1] [%o2 H2]".
  iDestruct (own_valid_2 with "H1 H2") as %[]%auth_frag_valid_1; done.
Qed.

Definition issued (γ : gname) (x : nat) : iProp Σ :=
  own γ (◯ (ε : option (excl nat), GSet {[x]})).

Definition lock_inv (γ : gname) (lo ln : loc) (P : iProp Σ) : iProp Σ :=
  ∃ o n : nat, lo ↦ #o ∗ ln ↦ #n ∗
  own γ (● (Excl' o, GSet (set_seq 0 n))) ∗
  (
    (locked_by γ o ∗ P) ∨
    issued γ o
  ).

Definition is_lock (γ : gname) (l : val) (P : iProp Σ) : iProp Σ :=
  ∃ lo ln : loc, ⌜l = (#lo, #ln)%V⌝ ∗ inv N (lock_inv γ lo ln P).

(* ================================================================= *)
(** ** Specifications *)

Lemma mk_lock_spec P :
  {{{ P }}} mk_lock #() {{{ γ l, RET l; is_lock γ l P }}}.
Proof.
  iIntros "%Φ HP HΦ".
  wp_lam.
  wp_alloc lo; wp_alloc ln.
  wp_pures.
  iMod (own_alloc (● (Excl' 0, GSet ∅) ⋅ ◯ (Excl' 0, GSet ∅))) as "(%γ & Hγ & Ho)".
  { by apply auth_both_valid_discrete. }
  iApply ("HΦ" $! γ).
  iExists _, _; iSplitR; first done.
  iApply inv_alloc; iExists 0, 0; eauto with iFrame.
Qed.

Lemma wait_spec γ l P x :
  {{{ is_lock γ l P ∗ issued γ x }}}
    wait #x l
  {{{ RET #(); locked γ ∗ P }}}.
Proof.
  iIntros "%Φ [(%lo & %ln & -> & #I) Hx] HΦ".
  iLöb as "IH".
  wp_rec.
  wp_pures.
  wp_bind (! _)%E.
  iInv "I" as "(%o & %n & Hlo & Hln & Hγ)".
  wp_load.
  destruct (decide (o = x)) as [->|].
  - iDestruct "Hγ" as "[Hγ [[Hexcl HP]|Ho]]".
    + iSplitL "Hlo Hln Hγ Hx"; first by iExists _, _; iFrame.
      iModIntro.
      wp_pures.
      rewrite bool_decide_eq_true_2 //.
      wp_pures.
      by iApply "HΦ"; iFrame.
    + iDestruct (own_valid_2 with "Hx Ho") as
        %[_ Hvl%gset_disj_valid_op]%auth_frag_valid_1;
        set_solver.
  - iSplitL "Hlo Hln Hγ"; first by iExists _, _; iFrame.
    iModIntro.
    wp_pures.
    rewrite bool_decide_eq_false_2; last naive_solver.
    wp_pures.
    iApply ("IH" with "Hx HΦ").
Qed.

Lemma acquire_spec γ l P :
  {{{ is_lock γ l P }}} acquire l {{{ RET #(); locked γ ∗ P }}}.
Proof.
  iIntros "%Φ (%lo & %ln & -> & #I) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_pures.
  wp_bind (! _)%E.
  iInv "I" as "(%o & %n & Hlo & Hln & Hγ)".
  wp_load.
  iSplitL "Hlo Hln Hγ"; first by iExists _, _; iFrame.
  clear o.
  iModIntro.
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  iInv "I" as "(%o & %n' & Hlo & Hln & Hγ)".
  destruct (decide (n' = n)) as [->|].
  - wp_cmpxchg_suc.
    rewrite Z.add_comm -(Nat2Z.inj_add 1) /=.
    iDestruct "Hγ" as "[Hγ Hγ']".
    iMod (own_update _ _ (● (Excl' o, GSet (set_seq 0 (S n))) ⋅ ◯ (ε, GSet {[n]})) with "Hγ") as "[Hγ Hn]".
    {
      apply auth_update_alloc, prod_local_update_2.
      rewrite set_seq_S_end_union_L /=.
      apply gset_disj_alloc_empty_local_update; apply (set_seq_S_end_disjoint 0).
    }
    iSplitL "Hlo Hln Hγ Hγ'"; first by iExists _, _; iFrame.
    iModIntro.
    wp_pures.
    wp_apply (wait_spec with "[I $Hn]"); first iExists _, _; eauto.
  - wp_cmpxchg_fail; first naive_solver.
    iModIntro.
    iSplitL "Hlo Hln Hγ"; first by iExists _, _; iFrame.
    wp_pures.
    by iApply "IH".
Qed.

Lemma release_spec γ l P :
  {{{ is_lock γ l P ∗ locked γ ∗ P }}} release l {{{ RET #(); True }}}.
Proof.
  iIntros "%Φ ((%lo & %ln & -> & #I) & [%o Hexcl] & HP) HΦ".
  wp_lam.
  wp_pures.
  wp_bind (! _)%E.
  iInv "I" as "(%o' & %n & Hlo & Hln & [Hγ [[>Hexcl' _]|Ho]])".
  { by iDestruct (own_valid_2 with "Hexcl Hexcl'") as %[]%auth_frag_valid_1. }
  wp_load.
  iDestruct (own_valid_2 with "Hγ Hexcl") as
    %[[<-%Excl_included%leibniz_equiv _]%pair_included _]%auth_both_valid_discrete.
  iModIntro.
  iSplitL "Hlo Hln Hγ Ho"; first by iFrame.
  clear n.
  wp_pures.
  rewrite Z.add_comm -(Nat2Z.inj_add 1) /=.
  iInv "I" as "(%o' & %n & Hlo & Hln & [Hγ [[>Hexcl' _]|Ho]])".
  { by iDestruct (own_valid_2 with "Hexcl Hexcl'") as %[]%auth_frag_valid. }
  wp_store.
  iDestruct (own_valid_2 with "Hγ Hexcl") as
    %[[<-%Excl_included%leibniz_equiv _]%pair_included _]%auth_both_valid_discrete.
  iCombine "Hγ Hexcl" as "Hγ".
  iMod (own_update _ _ (● (Excl' (S o), GSet (set_seq 0 n)) ⋅ ◯ (Excl' (S o), ε)) with "Hγ") as "[Hγ Hexcl]".
  { by apply auth_update, prod_local_update_1, option_local_update, exclusive_local_update. }
  iModIntro.
  iSplitR "HΦ"; last by iApply "HΦ".
  iExists _, _; eauto with iFrame.
Qed.

End proofs.
