From iris.algebra Require Import auth excl gset numbers.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.

(**
  Let's look at another implementation of a lock, namely a ticket
  lock. Instead of having every thread fight to acquire the lock. The
  ticket lock makes them wait in line. It does this by maintaining two
  counters representing queue positions. The first counter is the
  position next in line to access the critical region. While the
  second counter is the end of the line.
  A thread can acquire the lock by incrementing the second counter and
  keeping its previous value as a ticket for it's position in the
  queue. When the first counter reachest this ticket value, the thread
  gains access to the critical region. The thread can then release the
  lock by incrementing the first counter.
*)
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

(**
  As a ticket lock is a lock. So we expect it to satisfy the same
  specification as the spin lick. This time you have to find the
  necessary resource and lock invariant by your self.
*)

Definition RA : cmra
(* BEGIN SOLUTION *)
  (**
    We will use a finite set of numbers to represent the tickets that
    have been issued. This becomes a camera by using the disjoint
    union as operation.
    For the first counter we will use an exclusive camera. By wraping
    them both in an authoratative camera, we can use the authoratative
    fragment to bind the values of our counters to the ghost state.
  *)
  := authR (prodUR (optionUR (exclR natO)) (gset_disjR nat)).
(* END SOLUTION BEGIN TEMPLATE
  (* := insert your definition here *). Admitted.
END TEMPLATE *)

Section proofs.
Context `{!heapGS Σ, !inG Σ RA}.
Let N := nroot .@ "ticket_lock".

Definition lock_inv (γ : gname) (lo ln : loc) (P : iProp Σ) : iProp Σ
(* BEGIN SOLUTION *)
  (**
    Our invariant will firstly link the authoratative fragment to the
    counters. For the second counter this means that all tickets prior
    to its current value must have been issued.
    Secondly the lock either contains the current ticket, or access to
    the critical area, as well as ownership of the value of the first
    counter.
  *)
  := ∃ o n : nat, lo ↦ #o ∗ ln ↦ #n ∗
  own γ (● (Excl' o, GSet (set_seq 0 n))) ∗
  (
    (own γ (◯ (Excl' o, GSet ∅)) ∗ P) ∨
    own γ (◯ (ε : option (excl nat), GSet {[o]}))
  ).
(* END SOLUTION BEGIN TEMPLATE
  (* := insert your definition here *). Admitted.
END TEMPLATE *)

Definition is_lock (γ : gname) (l : val) (P : iProp Σ) : iProp Σ :=
  ∃ lo ln : loc, ⌜l = (#lo, #ln)%V⌝ ∗ inv N (lock_inv γ lo ln P).

Definition locked (γ : gname) : iProp Σ
(* BEGIN SOLUTION *)
  (**
    The lock will be locked when the ownership of the first counters
    value is not in the invariant.
  *)
  := ∃ o, own γ (◯ (Excl' o, GSet ∅)).
(* END SOLUTION BEGIN TEMPLATE
  (* := insert your definition here *). Admitted.
END TEMPLATE *)

Definition issued (γ : gname) (x : nat) : iProp Σ
(* BEGIN SOLUTION *)
  (** A ticket is simply the singleton set over its index. *)
  := own γ (◯ (ε : option (excl nat), GSet {[x]})).
(* END SOLUTION BEGIN TEMPLATE
  (* := insert your definition here *). Admitted.
END TEMPLATE *)

Lemma locked_excl γ : locked γ -∗ locked γ -∗ False.
(* SOLUTION *) Proof.
  iIntros "[%o1 H1] [%o2 H2]".
  iPoseProof (own_valid_2 with "H1 H2") as "%H".
  rewrite auth_frag_valid /= in H.
  rewrite pair_valid /= in H.
  by destruct H as [H _].
Qed.

Lemma mk_lock_spec P : {{{ P }}} mk_lock #() {{{ γ l, RET l; is_lock γ l P }}}.
(* SOLUTION *) Proof.
  iIntros "%Φ HP HΦ".
  wp_lam.
  wp_alloc ln as "Hln".
  wp_alloc lo as "Hlo".
  wp_pures.
  iMod (own_alloc (● (Excl' 0, GSet ∅) ⋅ ◯ (Excl' 0, GSet ∅))) as "(%γ & Hγ & Ho)".
  { by apply auth_both_valid_discrete. }
  iApply ("HΦ" $! γ).
  iExists lo, ln.
  iSplitR; first done.
  iApply inv_alloc.
  iNext.
  iExists 0, 0.
  iFrame.
  iLeft.
  iFrame.
Qed.

Lemma wait_spec γ l P x : {{{ is_lock γ l P ∗ issued γ x }}} wait #x l {{{ RET #(); locked γ ∗ P }}}.
(* SOLUTION *) Proof.
  iIntros "%Φ [(%lo & %ln & -> & #I) Hx] HΦ".
  iLöb as "IH".
  wp_rec.
  wp_pures.
  wp_bind (! _)%E.
  iInv "I" as "(%o & %n & Hlo & Hln & Hγ)".
  wp_load.
  destruct (decide (#o = #x)).
  - injection e as e.
    apply (inj Z.of_nat) in e.
    subst x.
    iDestruct "Hγ" as "[Hγ [[Hexcl HP]|Ho]]".
    + iSplitL "Hlo Hln Hγ Hx".
      { iIntros "!> !>". iExists o, n. iFrame. }
      iModIntro.
      wp_pures.
      rewrite bool_decide_eq_true_2 //.
      wp_pures.
      iApply "HΦ".
      iFrame.
      by iExists o.
    + iPoseProof (own_valid_2 with "Hx Ho") as "%H".
      rewrite auth_frag_valid /= in H.
      rewrite pair_valid /= in H.
      destruct H as [_ H].
      apply gset_disj_valid_op in H.
      by rewrite disjoint_singleton_l elem_of_singleton in H.
  - iSplitL "Hlo Hln Hγ".
    { iIntros "!> !>". iExists o, n. iFrame. }
    iModIntro.
    wp_pures.
    rewrite bool_decide_eq_false_2 //.
    wp_pures.
    iApply ("IH" with "Hx HΦ").
Qed.

Lemma acquire_spec γ l P : {{{ is_lock γ l P }}} acquire l {{{ RET #(); locked γ ∗ P }}}.
(* SOLUTION *) Proof.
  iIntros "%Φ (%lo & %ln & -> & #I) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_pures.
  wp_bind (! _)%E.
  iInv "I" as "(%o & %n & Hlo & Hln & Hγ)".
  wp_load.
  iSplitL "Hlo Hln Hγ".
  { iIntros "!> !>". iExists o, n. iFrame. }
  clear o.
  iModIntro.
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  iInv "I" as "(%o & %n' & Hlo & Hln & Hγ)".
  destruct (decide (#n' = #n)).
  - injection e as e.
    apply (inj Z.of_nat) in e.
    subst n'.
    wp_cmpxchg_suc.
    rewrite Z.add_comm -(Nat2Z.inj_add 1) /=.
    iDestruct "Hγ" as "[Hγ Hγ']".
    iMod (own_update _ _ (● (Excl' o, GSet (set_seq 0 (S n))) ⋅ ◯ (ε, GSet {[n]})) with "Hγ") as "[Hγ Hn]".
    {
      apply auth_update_alloc.
      apply prod_local_update_2.
      rewrite set_seq_S_end_union_L.
      rewrite -gset_disj_union.
      2: { apply set_seq_S_end_disjoint. }
      rewrite -{2}(ucmra_unit_right_id (GSet {[n]})).
      apply gset_disj_alloc_op_local_update.
      apply (set_seq_S_end_disjoint 0).
    }
    iSplitL "Hlo Hln Hγ Hγ'".
    { iIntros "!> !>". iExists o, (S n). iFrame. }
    iModIntro.
    wp_pures.
    wp_apply (wait_spec with "[I $Hn]").
    + iExists lo, ln.
      by iFrame "I".
    + done.
  - wp_cmpxchg_fail.
    iModIntro.
    iSplitL "Hlo Hln Hγ".
    { iNext. iExists o, n'. iFrame. }
    wp_pures.
    by iApply "IH".
Qed.

Lemma release_spec γ l P : {{{ is_lock γ l P ∗ locked γ ∗ P }}} release l {{{ RET #(); True }}}.
(* SOLUTION *) Proof.
  iIntros "%Φ ((%lo & %ln & -> & #I) & [%o Hexcl] & HP) HΦ".
  wp_lam.
  wp_pures.
  wp_bind (! _)%E.
  iInv "I" as "(%o' & %n & Hlo & Hln & [Hγ [[>Hexcl' _]|Ho]])".
  {
    iPoseProof (own_valid_2 with "Hexcl Hexcl'") as "%H".
    rewrite auth_frag_valid /= in H.
    rewrite pair_valid /= in H.
    by destruct H as [H _].
  }
  wp_load.
  iPoseProof (own_valid_2 with "Hγ Hexcl") as "%H".
  rewrite auth_both_valid_discrete /= in H.
  destruct H as [H _].
  rewrite pair_included in H.
  destruct H as [H _].
  rewrite Excl_included in H.
  destruct H.
  iModIntro.
  iSplitL "Hlo Hln Hγ Ho".
  { iExists o, n. iFrame. }
  clear n.
  wp_pures.
  rewrite Z.add_comm -(Nat2Z.inj_add 1) /=.
  iInv "I" as "(%o' & %n & Hlo & Hln & [Hγ [[>Hexcl' _]|Ho]])".
  {
    iPoseProof (own_valid_2 with "Hexcl Hexcl'") as "%H".
    rewrite auth_frag_valid /= in H.
    rewrite pair_valid /= in H.
    by destruct H as [H _].
  }
  wp_store.
  iPoseProof (own_valid_2 with "Hγ Hexcl") as "%H".
  rewrite auth_both_valid_discrete /= in H.
  destruct H as [H _].
  rewrite pair_included in H.
  destruct H as [H _].
  rewrite Excl_included in H.
  destruct H.
  iCombine "Hγ Hexcl" as "Hγ".
  iMod (own_update _ _ (● (Excl' (S o), GSet (set_seq 0 n)) ⋅ ◯ (Excl' (S o), ε)) with "Hγ") as "[Hγ Hexcl]".
  {
    apply auth_update.
    apply prod_local_update_1.
    apply option_local_update.
    by apply exclusive_local_update.
  }
  iModIntro.
  iSplitR "HΦ".
  - iNext.
    iExists (S o), n.
    iFrame.
    iLeft.
    iFrame.
  - by iApply "HΦ".
Qed.

End proofs.
