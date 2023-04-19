From iris.algebra Require Export auth frac numbers.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation par.
From iris_tutorial.logic Require Import key.

(*
  Let us define a simple counter module. A counter has 3 functions, a
  constructor, an incr, and a read. The counter is initialized as 0,
  and incr increments the counter while returning the old value. While
  read simply returns the current value of the counter. Further more
  we want the counter to be shareable across multiple threads.
*)

Definition mk_counter : val :=
  λ: <>, ref #0.
Definition incr : val :=
  rec: "incr" "c" :=
  let: "n" := !"c" in
  let: "m" := "n" + #1 in
  if: CAS "c" "n" "m" then "n" else "incr" "c".
Definition read : val :=
  λ: "c", !"c".

Module spec1.
Section spec1.
Context `{heapGS Σ}.

(*
  We are going to keep the fact that our counter is build on a pointer
  as an implementation detail. Instead we will define a predicate
  describing when a value is a counter.
*)

Definition is_counter1 (v : val) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ l ↦ #n.

(*
  This description is however not persistent, so our value would not
  be shareable across threads. To fix this we can put the knowledge
  into an invariant.
*)

Let N := nroot .@ "counter".
Definition is_counter2 (v : val) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ inv N (l ↦ #n).

(*
  However with this definition we have locked the value of the pointer
  to always be n. To fix this we could abstract the value and instead
  only specify its lower bound.
*)

Definition is_counter3 (v : val) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ inv N (∃ m : nat, l ↦ #m ∗ ⌜n ≤ m⌝).

(*
  Now we can change the what the pointer mapsto, but we still can't
  refine the lowerbound.

  The final step is to use ghost state. The idea is to link n and m to
  peaces of ghost state in such a way that validity of their composit
  is n ≤ m.

  To achieve this we can use the camera `auth A`. This camera is has 2
  peaces:
  - `● x` called an authoratative element.
  - `◯ y` called a fragment.
  
  The idea of the authoratative camera is as follows. The authoratative
  element represents the whole of the resource, while the fragments
  acts as the peaces. To achive this the authoratative element acts
  like the exclusive camera, while the fragment inherits all the
  operations of A. Furthermore validity of `● x ⋅ ◯ y` is defined as
  `✓ x ∧ y ≼ x`.

  With this we can use the max_nat camera whose operation is just the
  maximum.
*)
Context `{!inG Σ (auth max_nat)}.

Definition is_counter (v : val) (γ : gname) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ own γ (◯ MaxNat n) ∗ inv N (∃ m : nat, l ↦ #m ∗ own γ (● MaxNat m)).

Global Instance is_counter_persistent v γ n : Persistent (is_counter v γ n) := _.

Lemma mk_counter_spec : {{{ True }}} mk_counter #() {{{ c γ, RET c; is_counter c γ 0}}}.
Proof.
  iIntros "%Φ _ HΦ".
  wp_lam.
  wp_alloc l as "Hl".
  iMod (own_alloc (● MaxNat 0 ⋅ ◯ MaxNat 0)) as "(%γ & Hγ & Hγ')".
  { by apply auth_both_valid. }
  iApply "HΦ".
  iExists l.
  iSplitR; first done.
  iFrame.
  iApply inv_alloc.
  iNext.
  iExists 0.
  iFrame.
Qed.

Lemma read_spec c γ n : {{{ is_counter c γ n }}} read c {{{ (u : nat), RET #u; ⌜n ≤ u⌝ }}}.
Proof.
  iIntros "%Φ (%l & -> & #Hγ' & #HI) HΦ".
  wp_lam.
  iInv "HI" as "(%m & Hl & Hγ)".
  wp_load.
  iCombine "Hγ Hγ'" gives "%H".
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  rewrite max_nat_included /= in H.
  iModIntro.
  iSplitL "Hl Hγ".
  {
    iExists m.
    iFrame.
  }
  by iApply "HΦ".
Qed.

Lemma incr_spec c γ n : {{{ is_counter c γ n }}} incr c {{{ (u : nat), RET #u; ⌜n ≤ u⌝ ∗ is_counter c γ (S n) }}}.
Proof.
  iIntros "%Φ (%l & -> & #Hγ' & #HI) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (! _)%E.
  iInv "HI" as "(%m & Hl & Hγ)".
  wp_load.
  iModIntro.
  iSplitL "Hl Hγ".
  { iExists m. iFrame. }
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  iInv "HI" as "(%m' & Hl & Hγ)".
  destruct (decide (#m = #m')) as [e | ne].
  - wp_cmpxchg_suc.
    injection e as e.
    apply (inj Z.of_nat) in e.
    subst m'.
    rewrite (comm Z.add m 1%Z) -(Nat2Z.inj_add 1) /=.
    iCombine "Hγ Hγ'" gives "%H".
    apply auth_both_valid_discrete in H.
    destruct H as [H _].
    rewrite max_nat_included /= in H.
    iClear "Hγ'".
    iMod (own_update _ _ (● MaxNat (S m) ⋅ ◯ MaxNat (S m)) with "Hγ") as "[Hγ Hγ']".
    {
      apply auth_update_alloc.
      apply max_nat_local_update=>/=.
      by apply le_S.
    }
    iModIntro.
    iSplitL "Hl Hγ".
    { iExists (S m). iFrame. }
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iSplitR; first done.
    iExists l.
    iSplitR; first done.
    rewrite -(max_l (S m) (S n)); last by apply le_n_S.
    by iDestruct "Hγ'" as "[_ $]".
  - wp_cmpxchg_fail.
    iModIntro.
    iSplitL "Hl Hγ".
    { iExists m'. iFrame. }
    wp_pures.
    by wp_apply "IH".
Qed.

Context `{!spawnG Σ}.

Lemma par_incr :
  {{{ True }}}
    let: "c" := mk_counter #() in
    (incr "c" ||| incr "c");;
    read "c"
  {{{ n, RET #(S n); True }}}.
Proof.
  iIntros "%Φ _ HΦ".
  wp_apply mk_counter_spec; first done.
  iIntros "%c %γ #Hγ".
  wp_pures.
  wp_apply (wp_par (λ _, is_counter c γ 1) (λ _, is_counter c γ 1)).
  1, 2: iApply (incr_spec with "Hγ").
  1, 2: iIntros "!> %n [_ $]".
  iClear "Hγ".
  iIntros "%v1 %v2 [#Hγ _] !>".
  wp_pures.
  wp_apply (read_spec with "Hγ").
  iIntros ([|n] H); first inversion H.
  by iApply "HΦ".
Qed.

End spec1.
End spec1.

(*
  Our first specification only allowed us to find a lower bound for
  the value in par_incr. Any solution to this problem has to be
  non-persistent, as we need to agregate the knowledge to conclude
  the total value.

  As we've seen before, we can use fractions to keep track of peaces
  of knowledge. So we will use the camera
  `auth (option (frac * nat))`.
*)

Module spec2.
Section spec2.
Context `{!heapGS Σ, !inG Σ (auth (option (frac * nat)))}.

Let N := nroot .@ "counter".

Definition is_counter (v : val) (γ : gname) (n : nat) (q : Qp) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ own γ (◯ Some (q, n)) ∗ inv N (∃ m : nat, l ↦ #m ∗ own γ (● Some (1%Qp, m))).

Lemma is_counter_add (c : val) (γ : gname) (n m : nat) (p q : Qp) :
  is_counter c γ (n + m) (p + q) ⊣⊢ is_counter c γ n p ∗ is_counter c γ m q.
Proof.
  iSplit.
  - iIntros "(%l & -> & [Hγ1 Hγ2] & #I)".
    iSplitL "Hγ1".
    + iExists l.
      iSplitR; first done.
      by iFrame.
    + iExists l.
      iSplitR; first done.
      by iFrame.
  - iIntros "[(%l & -> & Hγ1 & I) (%l' & %H & Hγ2 & _)]".
    injection H as <-.
    iExists l.
    iSplitR; first done.
    iCombine "Hγ1 Hγ2" as "Hγ".
    iFrame.
Qed.

Lemma mk_counter_spec :
  {{{ True }}} mk_counter #() {{{ c γ, RET c; is_counter c γ 0 1}}}.
Proof.
  iIntros "%Φ _ HΦ".
  wp_lam.
  wp_alloc l as "Hl".
  iMod (own_alloc (● (Some (1%Qp, 0)) ⋅ ◯ (Some (1%Qp, 0)))) as "(%γ & Hγ & Hγ')".
  {
    apply auth_both_valid_discrete.
    split.
    - reflexivity.
    - done.
  }
  iApply "HΦ".
  iExists l.
  iSplitR; first done.
  iFrame.
  iApply inv_alloc.
  iExists 0.
  iFrame.
Qed.

Lemma read_spec (c : val) (γ : gname) (n : nat) (q : Qp) :
  {{{ is_counter c γ n q }}} read c {{{ (u : nat), RET #u; is_counter c γ n q ∗ ⌜n ≤ u⌝ }}}.
Proof.
  iIntros "%Φ (%l & -> & Hγ' & #I) HΦ".
  wp_lam.
  iInv "I" as "(%m & Hl & Hγ)".
  wp_load.
  iCombine "Hγ Hγ'" gives "%H".
  iModIntro.
  iSplitL "Hl Hγ".
  { iExists m. iFrame. }
  iApply "HΦ".
  iSplitL.
  { iExists l. by iFrame "Hγ' I". }
  iPureIntro.
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  apply Some_pair_included in H.
  destruct H as [_ H].
  rewrite Some_included_total in H.
  by apply nat_included.
Qed.

Lemma read_spec_full (c : val) (γ : gname) (n : nat) :
  {{{ is_counter c γ n 1 }}} read c {{{ RET #n; is_counter c γ n 1 }}}.
Proof.
  iIntros "%Φ (%l & -> & Hγ' & #I) HΦ".
  wp_lam.
  iInv "I" as "(%m & Hl & Hγ)".
  wp_load.
  iCombine "Hγ Hγ'" gives "%H".
  iModIntro.
  iSplitL "Hl Hγ".
  { iExists m. iFrame. }
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  apply (Some_included_exclusive _) in H; last done.
  destruct H as [_ H]; cbn in H.
  apply leibniz_equiv in H.
  subst m.
  iApply "HΦ".
  iExists l.
  iSplitR; first done.
  by iFrame.
Qed.

Lemma incr_spec (c : val) (γ : gname) (n : nat) (q : Qp) :
  {{{ is_counter c γ n q }}} incr c {{{ (u : nat), RET #u; ⌜n ≤ u⌝ ∗ is_counter c γ (S n) q }}}.
Proof.
  iIntros "%Φ (%l & -> & Hγ' & #I) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (! _)%E.
  iInv "I" as "(%m & Hl & Hγ)".
  wp_load.
  iModIntro.
  iSplitL "Hl Hγ".
  { iExists m. iFrame. }
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  iInv "I" as "(%m' & Hl & Hγ)".
  destruct (decide (# m = # m')).
  - injection e as e.
    apply (inj Z.of_nat) in e.
    subst m'.
    wp_cmpxchg_suc.
    rewrite (comm Z.add) -(Nat2Z.inj_add 1) /=.
    iCombine "Hγ Hγ'" as "Hγ" gives "%H".
    apply auth_both_valid_discrete in H.
    destruct H as [H _].
    apply Some_pair_included in H.
    destruct H as [_ H].
    rewrite Some_included_total in H.
    apply nat_included in H.
    iMod (own_update _ _ (● Some (1%Qp, S m) ⋅ ◯ Some (q, S n)) with "Hγ") as "[Hγ Hγ']".
    {
      apply auth_update.
      apply option_local_update.
      apply prod_local_update_2.
      by apply (op_local_update_discrete _ _ 1).
    }
    iModIntro.
    iSplitL "Hl Hγ".
    { iExists (S m). iFrame. }
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iSplitR; first done.
    iExists l.
    iSplitR; first done.
    by iFrame.
  - wp_cmpxchg_fail.
    iModIntro.
    iSplitL "Hl Hγ".
    { iExists m'. iFrame. }
    wp_pures.
    wp_apply ("IH" with "Hγ' HΦ").
Qed.

End spec2.
End spec2.

