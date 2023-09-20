From iris.algebra Require Export auth excl frac numbers.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation par.

(**
  Let us define a simple counter module. A counter has 3 functions, a
  constructor, an incr, and a read. The counter is initialized as 0,
  and incr increments the counter while returning the old value. While
  read simply returns the current value of the counter. Furthermore,
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

(**
  We are going to keep the fact that our counter is built on a pointer
  as an implementation detail. Instead, we will define a predicate
  describing when a value is a counter.
*)

Definition is_counter1 (v : val) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ l ↦ #n.

(**
  This description is however not persistent, so our value would not
  be shareable across threads. To fix this we can put the knowledge
  into an invariant.
*)

Let N := nroot .@ "counter".
Definition is_counter2 (v : val) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ inv N (l ↦ #n).

(**
  However with this definition we have locked the value of the pointer
  to always be n. To fix this we could abstract the value and instead
  only specify its lower bound.
*)

Definition is_counter3 (v : val) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ inv N (∃ m : nat, l ↦ #m ∗ ⌜n ≤ m⌝).

(**
  Now we can change the what the pointer mapsto, but we still can't
  refine the lower bound.

  The final step is to use ghost state. The idea is to link n and m to
  pieces of ghost state in such a way that the validity of their
  composite is [n ≤ m].

  To achieve this we can use the camera [auth A]. This camera has 2
  pieces:
  - [● x] called an authoritative element.
  - [◯ y] called a fragment.
  
  The idea of the authoritative camera is as follows. The authoritative
  element represents the whole of the resource, while the fragments
  act as the pieces. To achieve this the authoritative element acts
  like the exclusive camera, while the fragment inherits all the
  operations of A. Furthermore, validity of [● x ⋅ ◯ y] is defined as
  [✓ x ∧ y ≼ x].

  With this we can use the max_nat camera whose operation is just the
  maximum.
*)
Context `{!inG Σ (authR max_natUR)}.

Definition is_counter (v : val) (γ : gname) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ own γ (◯ MaxNat n) ∗ inv N (∃ m : nat, l ↦ #m ∗ own γ (● MaxNat m)).

Global Instance is_counter_persistent v γ n : Persistent (is_counter v γ n) := _.

(**
  Before we start proving the specifications. Let's prove some useful
  lemmas about our ghost state. For starters, we need to know that we
  can allocate the initial state we need.
*)
Lemma alloc_initial_state : ⊢ |==> ∃ γ, own γ (● MaxNat 0) ∗ own γ (◯ MaxNat 0).
Proof.
  (**
    Ownership of multiple fragments of state composes into ownership of
    their composite. So we can simply the goal a little.
  *)
  setoid_rewrite <-own_op.
  (** Now the goal is on the form expected by own_alloc. *)
  apply own_alloc.
  (**
    However, we are only allowed to allocate valid states. So we must
    prove that our desired state is a valid one.

    The validity of auth says that the fragment must be included in
    the authoritative element and the authoritative element must be
    valid.
  *)
  apply auth_both_valid_discrete.
  split.
  - (** Inclusion for max_nat turns out to be the natural ordering. *)
    apply max_nat_included; simpl.
    reflexivity.
  - (** All elements of max_nat are valid. *)
    cbv.
    done.
Qed.

Lemma state_valid γ n m : own γ (● MaxNat n) -∗ own γ (◯ MaxNat m) -∗ ⌜ m ≤ n ⌝.
Proof.
  iIntros "Hγ Hγ'".
  iPoseProof (own_valid_2 with "Hγ Hγ'") as "%H".
  iPureIntro.
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  apply max_nat_included in H; cbn in H.
  done.
Qed.

Lemma update_state γ n : own γ (● MaxNat n) ==∗ own γ (● MaxNat (S n)) ∗ own γ (◯ MaxNat (S n)).
Proof.
  iIntros "H".
  rewrite -own_op.
  (**
    [own] can be updated using frame-preserving updates. These are
    updates that will not invalidate any other own that could possibly
    exist.
  *)
  iApply (own_update with "H").
  (**
    [auth] has its own special version of these called local updates,
    as we know what the whole of the state is.
  *)
  apply auth_update_alloc.
  apply max_nat_local_update; cbn.
  by apply le_S.
Qed.

Lemma mk_counter_spec : {{{ True }}} mk_counter #() {{{ c γ, RET c; is_counter c γ 0}}}.
(* SOLUTION *) Proof.
  iIntros "%Φ _ HΦ".
  wp_lam.
  wp_alloc l as "Hl".
  iMod alloc_initial_state as "(%γ & Hγ & Hγ')".
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
(* SOLUTION *) Proof.
  iIntros "%Φ (%l & -> & #Hγ' & #HI) HΦ".
  wp_lam.
  iInv "HI" as "(%m & Hl & Hγ)".
  wp_load.
  iPoseProof (state_valid with "Hγ Hγ'") as "%H".
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
    (* BEGIN SOLUTION *)
    rewrite Z.add_comm -(Nat2Z.inj_add 1) /=.
    iPoseProof (state_valid with "Hγ Hγ'") as "%H".
    iClear "Hγ'".
    iMod (update_state with "Hγ") as "[Hγ #Hγ']".
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
(* END SOLUTION BEGIN TEMPLATE
    (* exercise *)
Admitted.
END TEMPLATE *)

Context `{!spawnG Σ}.

Lemma par_incr :
  {{{ True }}}
    let: "c" := mk_counter #() in
    (incr "c" ||| incr "c");;
    read "c"
  {{{ n, RET #(S n); True }}}.
(* SOLUTION *) Proof.
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

(**
  Our first specification only allowed us to find a lower bound for
  the value in par_incr. Any solution to this problem has to be
  non-persistent, as we need to aggregate the knowledge to conclude
  the total value.

  As we've seen before, we can use fractions to keep track of pieces
  of knowledge. So we will use the camera
  [auth (option (frac * nat))].
*)

Module spec2.
Section spec2.
Context `{!heapGS Σ, !inG Σ (authR (optionUR (prodR fracR natR)))}.

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

Lemma alloc_initial_state : ⊢ |==> ∃ γ, own γ (● Some (1%Qp, 0)) ∗ own γ (◯ Some (1%Qp, 0)).
Proof.
  setoid_rewrite <-own_op.
  apply own_alloc.
  apply auth_both_valid_discrete.
  split.
  - reflexivity.
  - apply Some_valid.
    apply pair_valid.
    split.
    + apply frac_valid.
      reflexivity.
    + cbv.
      done.
Qed.

Lemma state_valid γ (n m : nat) (q : Qp) : own γ (● Some (1%Qp, n)) -∗ own γ (◯ Some (q, m)) -∗ ⌜m ≤ n⌝.
Proof.
  iIntros "Hγ Hγ'".
  iPoseProof (own_valid_2 with "Hγ Hγ'") as "%H".
  iPureIntro.
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  apply Some_pair_included in H.
  destruct H as [_ H].
  rewrite Some_included_total in H.
  apply nat_included in H.
  done.
Qed.

Lemma state_valid_full γ (n m : nat) : own γ (● Some (1%Qp, n)) -∗ own γ (◯ Some (1%Qp, m)) -∗ ⌜m = n⌝.
Proof.
  iIntros "Hγ Hγ'".
  iPoseProof (own_valid_2 with "Hγ Hγ'") as "%H".
  iPureIntro.
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  apply Some_included_exclusive in H.
  - destruct H as [_ H]; cbn in H.
    apply leibniz_equiv in H.
    done.
  - apply _.
  - done.
Qed.

Lemma update_state γ n m (q : Qp) : own γ (● Some (1%Qp, n)) ∗ own γ (◯ Some (q, m)) ==∗ own γ (● Some (1%Qp, S n)) ∗ own γ (◯ Some (q, S m)).
Proof.
  iIntros "H".
  rewrite -!own_op.
  iApply (own_update with "H").
  apply auth_update.
  apply option_local_update.
  apply prod_local_update_2.
  apply (op_local_update_discrete _ _ 1).
  done.
Qed.

Lemma mk_counter_spec :
  {{{ True }}} mk_counter #() {{{ c γ, RET c; is_counter c γ 0 1}}}.
(* SOLUTION *) Proof.
  iIntros "%Φ _ HΦ".
  wp_lam.
  wp_alloc l as "Hl".
  iMod alloc_initial_state as "(%γ & Hγ & Hγ')".
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
(* SOLUTION *) Proof.
  iIntros "%Φ (%l & -> & Hγ' & #I) HΦ".
  wp_lam.
  iInv "I" as "(%m & Hl & Hγ)".
  wp_load.
  iPoseProof (state_valid with "Hγ Hγ'") as "%H".
  iModIntro.
  iSplitL "Hl Hγ".
  { iExists m. iFrame. }
  iApply "HΦ".
  iSplitL.
  - iExists l.
    by iFrame "Hγ' I".
  - done.
Qed.

Lemma read_spec_full (c : val) (γ : gname) (n : nat) :
  {{{ is_counter c γ n 1 }}} read c {{{ RET #n; is_counter c γ n 1 }}}.
(* SOLUTION *) Proof.
  iIntros "%Φ (%l & -> & Hγ' & #I) HΦ".
  wp_lam.
  iInv "I" as "(%m & Hl & Hγ)".
  wp_load.
  iPoseProof (state_valid_full with "Hγ Hγ'") as "#<-".
  iModIntro.
  iSplitL "Hl Hγ".
  { iExists n. iFrame. }
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
(* BEGIN SOLUTION *)
    rewrite Z.add_comm -(Nat2Z.inj_add 1) /=.
    iPoseProof (state_valid with "Hγ Hγ'") as "%H".
    iMod (update_state with "[$Hγ $Hγ']") as "[Hγ Hγ']".
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
(* END SOLUTION BEGIN TEMPLATE
    (* exercise *)
Admitted.
END TEMPLATE *)

End spec2.
End spec2.
