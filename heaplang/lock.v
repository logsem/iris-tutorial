From iris.algebra Require Export auth excl frac gset numbers.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation par.
From iris_tutorial.logic Require Import key.

(*
  Let us define a specification for locks. Our specification will
  capture 3 functions.
*)
Record lock `{!heapGS Σ} := Lock {
  (* A constructor for making new locks *)
  mk_lock : val;
  (* A function for locking *)
  acquire : val;
  (* A function for unlocking *)
  release : val;
  (*
    We associate a name to each lock so we can describe it's state in
    multiple peaces.
  *)
  name : Type;
  (*
    We associate the name with the lock value as well as the
    knowledge the lock is protecting
  *)
  is_lock (γ : name) (lock : val) (P : iProp Σ) : iProp Σ;
  (* Lockes should be shareable, so we need `is_lock` to be persistent *)
  is_lock_persistent γ lock P : Persistent (is_lock γ lock P);
  (* In order to know when a lock is locked we define a proposition *)
  locked (γ : name) : iProp Σ;
  (* And as a lock can only be locked once, we require that the knowledge be exclusive *)
  locked_excl γ : locked γ -∗ locked γ -∗ False;
  (*
    In order to make a new lock, we have to give up the knowledge it
    should protect. As such we place `P` in the precondition.
  *)
  mk_lock_spec P : {{{ P }}} mk_lock #() {{{ γ v, RET v; is_lock γ v P }}};
  (*
    When we acquire the lock, we gain the knowledge that it protects
    as well as the knowledge that it is now locked.
  *)
  acquire_spec γ v P : {{{ is_lock γ v P }}} acquire v {{{ RET #(); locked γ ∗ P }}};
  (*
    In order to release a lock we have to know that the lock is in
    fact locked, as well as reestablish its invariant.
  *)
  release_spec γ v P : {{{ is_lock γ v P ∗ locked γ ∗ P }}} release v {{{ RET #(); True }}};
}.

(*
  With this specification in hand, let us implement a simple spin-lock
  and show that it satisfies the specification.
*)
Module spin_lock.

Definition mk_lock : val :=
  λ: <>, ref #false.
Definition acquire : val :=
  rec: "acquire" "l" :=
  if: CAS "l" #false #true then
    #()
  else
    "acquire" "l".
Definition release : val :=
  λ: "l", "l" <- #false.

Section spin_lock.
Context `{!heapGS Σ, !keyG Σ}.
Let N := nroot .@ "spin_lock".

Definition is_lock (γ : gname) (v : val) (P : iProp Σ) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ inv N (∃ b : bool, l ↦ #b ∗ if b then True else key γ (DfracOwn 1) ∗ P).

Definition locked (γ : gname) : iProp Σ :=
  key γ (DfracOwn 1).

Global Instance is_lock_persistent γ v P : Persistent (is_lock γ v P) := _.

Lemma locked_excl γ : locked γ -∗ locked γ -∗ False.
Proof. apply key_1_excl_l. Qed.

Lemma mk_lock_spec P : {{{ P }}} mk_lock #() {{{ γ v, RET v; is_lock γ v P }}}.
Proof.
  iIntros "%Φ P HΦ".
  wp_lam.
  wp_alloc l as "Hl".
  iMod key_alloc as "[%γ Hγ]".
  iApply "HΦ".
  iExists l.
  iSplitR; first done.
  iApply inv_alloc.
  iNext.
  iExists false.
  iFrame.
Qed.

Lemma acquire_spec γ v P : {{{ is_lock γ v P }}} acquire v {{{ RET #(); locked γ ∗ P }}}.
Proof.
  iIntros "%Φ (%l & -> & #I) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (CmpXchg _ _ _).
  iInv "I" as ([]) "[Hl H]".
  - wp_cmpxchg_fail.
    iModIntro.
    iSplitL "Hl".
    {
      iNext.
      iExists true.
      by iFrame.
    }
    wp_pures.
    by iApply "IH".
  - wp_cmpxchg_suc.
    iModIntro.
    iSplitL "Hl".
    {
      iNext.
      iExists true.
      by iFrame.
    }
    wp_pures.
    by iApply "HΦ".
Qed.

Lemma release_spec γ v P : {{{ is_lock γ v P ∗ locked γ ∗ P }}} release v {{{ RET #(); True }}}.
Proof.
  iIntros "%Φ ((%l & -> & #I) & Hγ & HP) HΦ".
  wp_lam.
  iInv "I" as ([]) "[Hl H]".
  - wp_store.
    iModIntro.
    iSplitL "Hγ Hl HP".
    {
      iNext.
      iExists false.
      by iFrame.
    }
    by iApply "HΦ".
  - iDestruct "H" as "[>H _]".
    iDestruct (key_1_excl_l with "Hγ H") as "[]".
Qed.

End spin_lock.
End spin_lock.

Definition spin_lock `{!heapGS Σ, !keyG Σ} := {|
  mk_lock := spin_lock.mk_lock;
  acquire := spin_lock.acquire;
  release := spin_lock.release;
  is_lock := spin_lock.is_lock;
  locked := spin_lock.locked;
  locked_excl := spin_lock.locked_excl;
  mk_lock_spec := spin_lock.mk_lock_spec;
  acquire_spec := spin_lock.acquire_spec;
  release_spec := spin_lock.release_spec;
|}.

Module ticket_lock.
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

Section proofs.
Context `{!heapGS Σ, !inG Σ (auth (option (excl nat) * gset_disj nat))%type}.
Let N := nroot .@ "ticket_lock".

Definition lock_inv (γ : gname) (lo ln : loc) (P : iProp Σ) : iProp Σ :=
  ∃ o n : nat, lo ↦ #o ∗ ln ↦ #n ∗
  own γ (● (Excl' o, GSet (set_seq 0 n))) ∗
  (
    (own γ (◯ (Excl' o, GSet ∅)) ∗ P) ∨
    own γ (◯ (ε : option (excl nat), GSet {[o]}))
  ).

Definition is_lock (γ : gname) (l : val) (P : iProp Σ) : iProp Σ :=
  ∃ lo ln : loc, ⌜l = (#lo, #ln)%V⌝ ∗ inv N (lock_inv γ lo ln P).

Definition locked (γ : gname) : iProp Σ :=
  ∃ o, own γ (◯ (Excl' o, GSet ∅)).

Definition issued (γ : gname) (x : nat) : iProp Σ :=
  own γ (◯ (ε : option (excl nat), GSet {[x]})).

Global Instance is_lock_persistent γ l P : Persistent (is_lock γ l P) := _.

Lemma locked_excl γ : locked γ -∗ locked γ -∗ False.
Proof.
  iIntros "[%o1 H1] [%o2 H2]".
  iCombine "H1 H2" gives "%H".
  rewrite auth_frag_valid /= in H.
  rewrite pair_valid /= in H.
  by destruct H as [H _].
Qed.

Lemma mk_lock_spec P : {{{ P }}} mk_lock #() {{{ γ l, RET l; is_lock γ l P }}}.
Proof.
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
Proof.
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
    + iCombine "Hx Ho" gives "%H".
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
Proof.
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
    rewrite (comm Z.add) -(Nat2Z.inj_add 1) /=.
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
Proof.
  iIntros "%Φ ((%lo & %ln & -> & #I) & [%o Hexcl] & HP) HΦ".
  wp_lam.
  wp_pures.
  wp_bind (! _)%E.
  iInv "I" as "(%o' & %n & Hlo & Hln & [Hγ [[>Hexcl' _]|Ho]])".
  {
    iCombine "Hexcl Hexcl'" gives "%H".
    rewrite auth_frag_valid /= in H.
    rewrite pair_valid /= in H.
    by destruct H as [H _].
  }
  wp_load.
  iCombine "Hγ Hexcl" gives "%H".
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
  rewrite (comm Z.add) -(Nat2Z.inj_add 1) /=.
  iInv "I" as "(%o' & %n & Hlo & Hln & [Hγ [[>Hexcl' _]|Ho]])".
  {
    iCombine "Hexcl Hexcl'" gives "%H".
    rewrite auth_frag_valid /= in H.
    rewrite pair_valid /= in H.
    by destruct H as [H _].
  }
  wp_store.
  iCombine "Hγ Hexcl" gives "%H".
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
End ticket_lock.

Definition ticket_lock `{!heapGS Σ, !inG Σ (auth (option (excl nat) * gset_disj nat))%type} := {|
  mk_lock := ticket_lock.mk_lock;
  acquire := ticket_lock.acquire;
  release := ticket_lock.release;
  is_lock := ticket_lock.is_lock;
  locked := ticket_lock.locked;
  locked_excl := ticket_lock.locked_excl;
  mk_lock_spec := ticket_lock.mk_lock_spec;
  acquire_spec := ticket_lock.acquire_spec;
  release_spec := ticket_lock.release_spec;
|}.
