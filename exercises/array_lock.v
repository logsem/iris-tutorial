From iris.algebra Require Import auth excl gset numbers.
From iris.heap_lang Require Import lang proofmode notation par.

Lemma lookup_array `{!heapGS_gen hlc Σ} l dq vs off v :
  vs !! off = Some v → l ↦∗{dq} vs -∗ (l +ₗ Z.of_nat off) ↦{dq} v ∗
    ((l +ₗ off) ↦{dq} v -∗ l ↦∗{dq} vs).
Proof.
  iIntros "%H H".
  iPoseProof (update_array with "H") as "[$ H]"; first done.
  iIntros "Hv".
  iSpecialize ("H" with "Hv").
  by rewrite list_insert_id.
Qed.

Definition mk_lock : val :=
  λ: "cap",
  let: "array" := AllocN "cap" #false in
  "array" +ₗ #0 <- #true;;
  ("array", ref #0, "cap").

Definition wait : val :=
  rec: "wait" "l" "ticket" :=
  let: "array" := Fst (Fst "l") in
  let: "cap" := Snd "l" in
  let: "i" := "ticket" `rem` "cap" in
  if: !("array" +ₗ "i") then #() else "wait" "l" "ticket".

Definition acquire : val :=
  λ: "l",
  let: "next" := Snd (Fst "l") in
  let: "ticket" := FAA "next" #1 in
  wait "l" "ticket";;
  "ticket".

Definition release : val :=
  λ: "l" "o",
  let: "array" := Fst (Fst "l") in
  let: "cap" := Snd "l" in
  "array" +ₗ ("o" `rem` "cap") <- #false;;
  "array" +ₗ (("o" + #1) `rem` "cap") <- #true.

Section proofs.
Context `{
  !heapGS Σ,
  !inG Σ (authR (prodUR (optionUR (exclR natO)) (gset_disjUR nat))),
  !inG Σ (authR natUR),
  !inG Σ (exclR unitO)
}.
Let N := nroot .@ "lock".

Record name := mk_name {
  name_ticket : gname;
  name_invitation : gname;
  name_left : gname;
  name_right : gname;
}.

Definition left (γ : name) := own (name_left γ) (Excl ()).
Definition right (γ : name) := own (name_right γ) (Excl ()).

Definition locked (γ : name) (o : nat) : iProp Σ :=
  own (name_ticket γ) (◯ (Excl' o, GSet ∅)) ∗ right γ.
Definition issued (γ : name) (t : nat) : iProp Σ :=
  own (A:=auth (option (excl nat) * gset_disj nat)) (name_ticket γ) (◯ (None, GSet {[ t ]})).

Definition invitation (γ : name) (n : nat) : iProp Σ := own (name_invitation γ) (◯ n).

Definition state (γ : name) (cap o : nat) (R : iProp Σ) (xs : list val) : iProp Σ :=
  (own (name_ticket γ) (◯ (Excl' o, GSet ∅)) ∗ R ∗ left γ ∗ right γ ∗ ⌜xs = <[o `mod` cap := #true]> (replicate cap #false)⌝) ∨
  (issued γ o ∗ right γ ∗ ⌜xs = replicate cap #false⌝) ∨
  (issued γ o ∗ left γ ∗ ⌜xs = <[o `mod` cap := #true]> (replicate cap #false)⌝).

Definition lock_inv (γ : name) (a n : loc) (cap : nat) (R : iProp Σ) : iProp Σ :=
  ∃ (o i : nat) xs,
    n ↦ #(o + i) ∗ a ↦∗ xs ∗
    own (name_invitation γ) (● cap ⋅ ◯ i) ∗
    own (name_ticket γ) (● (Excl' o, GSet (set_seq o i))) ∗
    state γ cap o R xs.

Definition is_lock (γ : name) (l : val) (cap : nat) (R : iProp Σ) : iProp Σ :=
  ∃ a n : loc, ⌜l = (#a, #n, #cap)%V⌝ ∗ ⌜0 < cap⌝ ∗ inv N (lock_inv γ a n cap R).

Global Instance is_locked_persistent γ l n R : Persistent (is_lock γ l n R) := _.

Lemma rem_of_nat (x y : nat) : Z.of_nat (x `mod` y) = (x `rem` y)%Z.
Proof.
  destruct y.
  { by rewrite Z.rem_0_r_ext. }
  rewrite Z.rem_mod_nonneg.
  - apply Nat2Z.inj_mod.
  - apply Zle_0_nat.
  - apply (inj_lt 0), le_n_S, le_0_n.
Qed.

Lemma mod_eq a b n : a `mod` n = b `mod` n ↔ (∃ d, a = n * d + b) ∨ (∃ d, b = n * d + a).
Proof.
  destruct (decide (n = 0)) as [->|Hn].
  {
    cbn.
    setoid_rewrite (Nat.eq_sym_iff b a).
    rewrite or_idemp.
    split.
    - by exists 0.
    - by intros [].
  }
  split.
  - intros H.
    apply (f_equal (λ x, x + (n * b `div` n + n * a `div` n))) in H.
    rewrite {1}(comm _ (_ * _)) in H.
    rewrite !assoc !(comm _ (_ `mod` _)) in H.
    rewrite -!Nat.div_mod // in H.
    destruct (Nat.le_ge_cases (n * b `div` n) (n * a `div` n)) as [Hle|Hle].
    + left.
      exists (a `div` n - b `div` n).
      rewrite (comm Nat.add) Nat.mul_sub_distr_l.
      apply Nat.add_cancel_r with (n * b `div` n).
      by rewrite -assoc Nat.sub_add.
    + right.
      exists (b `div` n - a `div` n).
      rewrite (comm Nat.add) Nat.mul_sub_distr_l.
      apply Nat.add_cancel_r with (n * a `div` n).
      by rewrite -assoc Nat.sub_add.
  - intros [[d ->]|[d ->]].
    all: rewrite (comm Nat.add) Nat.mul_comm.
    2: symmetry.
    all: by apply Nat.mod_add.
Qed.

Lemma invitation_add (γ : name) (n m : nat) : invitation γ (n + m) ⊣⊢ invitation γ n ∗ invitation γ m.
Proof.
  rewrite /invitation.
  rewrite auth_frag_op.
  apply own_op.
Qed.

Lemma mk_lock_spec (cap : nat) (R : iProp Σ) :
  {{{ R ∗ ⌜0 < cap⌝ }}}
    mk_lock #cap
  {{{ γ l, RET l; is_lock γ l cap R ∗ invitation γ cap }}}.
Proof.
  iIntros "%Φ [HR %Hcap] HΦ".
  wp_lam.
  wp_alloc a as "Ha".
  { by apply (inj_lt 0). }
  wp_pures.
  iPoseProof (update_array _ _ _ 0 (#false) with "Ha") as "[H0 Ha]".
  {
    apply lookup_replicate.
    split; first done.
    by rewrite Nat2Z.id.
  }
  wp_store.
  iSpecialize ("Ha" with "H0").
  wp_alloc n as "Hn".
  wp_pures.
  iMod (own_alloc (● (Excl' 0, GSet ∅) ⋅ ◯ (Excl' 0, GSet ∅))) as "(%γ & Hγ & Hγ')".
  { by apply auth_both_valid_discrete. }
  iMod (own_alloc (● cap ⋅ ◯ cap)) as "(%ι & Hι & Hι')".
  { by apply auth_both_valid_discrete. }
  iMod (own_alloc (Excl ())) as "[%κ1 Hκ1]"; first done.
  iMod (own_alloc (Excl ())) as "[%κ2 Hκ2]"; first done.
  iApply ("HΦ" $! (mk_name γ ι κ1 κ2)).
  iFrame.
  iExists a, n.
  iSplitR; first done.
  iSplitR; first done.
  iApply inv_alloc.
  iNext.
  iExists 0, 0, _.
  rewrite (right_id ε (⋅)).
  iFrame "Ha Hn Hγ Hι".
  iLeft.
  iFrame.
  rewrite Nat2Z.id Nat.mod_0_l.
  - done.
  - by apply Nat.lt_neq in Hcap.
Qed.

Lemma wait_spec (γ : name) (l : val) (t cap : nat) (R : iProp Σ) :
  {{{ is_lock γ l cap R ∗ issued γ t }}}
    wait l #t
  {{{ RET #(); R ∗ locked γ t }}}.
Proof.
  iIntros "%Φ [(%a & %n & -> & %Hcap & #I) Hγ'] HΦ".
  iLöb as "IH".
  wp_rec.
  wp_pures.
  wp_bind (!_)%E.
  rewrite -rem_of_nat.
  iInv "I" as "(%o & %i & %xs & >Hn & >Ha & >Hι & >Hγ & [
    (>Hγ'' & HR & >Hl & Hr & >->)|[
    (>Hγ'' & >Hl & >->)|
    (>Hγ'' & >Hr & >->)
  ]])".
  - destruct (decide (o = t)) as [->|H].
    + iPoseProof (lookup_array _ _ _ (t `mod` cap) #true with "Ha") as "[Ht Ha]".
      {
        apply list_lookup_insert.
        rewrite replicate_length.
        apply Nat.mod_upper_bound.
        by apply Nat.lt_neq in Hcap.
      }
      wp_load.
      iModIntro.
      iSpecialize ("Ha" with "Ht").
      iSplitL "Hγ' Hn Hι Hγ Ha Hl".
      {
        iNext.
        iExists t, i, _.
        iFrame "Hn Ha Hι Hγ".
        iRight; iRight.
        by iFrame.
      }
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iFrame.
    + iPoseProof (own_valid with "Hι") as "%Hi".
      apply auth_both_valid_discrete in Hi.
      destruct Hi as [Hi _].
      apply nat_included in Hi.
      iPoseProof (own_valid_2 with "Hγ Hγ'") as "%Hv".
      apply auth_both_valid_discrete in Hv.
      destruct Hv as [Hv _].
      apply pair_included in Hv.
      destruct Hv as [_ Hv].
      apply gset_disj_included in Hv.
      apply singleton_subseteq_l in Hv.
      apply elem_of_set_seq in Hv.
      destruct Hv as [Ho Ht].
      assert (o `mod` cap ≠ t `mod` cap) as H'.
      {
        intros e.
        apply mod_eq in e.
        destruct e as [[d ->]|[d ->]].
        - apply Nat.le_add_le_sub_r in Ho.
          rewrite Nat.sub_diag in Ho.
          apply Nat.le_0_r in Ho.
          apply Nat.eq_mul_0_r in Ho.
          2: by apply Nat.lt_neq in Hcap.
          subst d.
          by rewrite Nat.mul_0_r in H.
        - rewrite (comm _ o) in Ht.
          apply Nat.le_lt_add_lt in Ht; last done.
          destruct d.
          { by rewrite Nat.mul_0_r in H. }
          rewrite -mult_n_Sm Nat.lt_nge in Ht.
          contradict Ht.
          trans cap; first done.
          apply Nat.le_add_l.
      }
      iPoseProof (lookup_array _ _ _ (t `mod` cap) #false with "Ha") as "[Ht Ha]".
      {
        rewrite list_lookup_insert_ne //.
        apply lookup_replicate_2, Nat.mod_upper_bound.
        by apply Nat.lt_neq in Hcap.
      }
      wp_load.
      iModIntro.
      iSpecialize ("Ha" with "Ht").
      iSplitL "Hγ'' Hn Hι Hγ Ha Hl Hr HR".
      {
        iNext.
        iExists o, i, _.
        iFrame "Hn Ha Hι Hγ".
        iLeft.
        by iFrame.
      }
      wp_pures.
      iApply ("IH" with "Hγ' HΦ").
  - iPoseProof (update_array _ _ _ (t `mod` cap) #false with "Ha") as "[Ht Ha]".
    {
      apply lookup_replicate_2, Nat.mod_upper_bound.
      by apply Nat.lt_neq in Hcap.
    }
    wp_load.
    iModIntro.
    iSpecialize ("Ha" with "Ht").
    iSplitL "Hn Ha Hι Hγ Hγ'' Hl".
    {
      iNext.
      rewrite insert_replicate.
      iExists o, i, _.
      iFrame "Hn Ha Hι Hγ".
      iRight; iLeft.
      by iFrame.
    }
    wp_pures.
    iApply ("IH" with "Hγ' HΦ").
  - destruct (decide (o = t)) as [->|H].
    + iPoseProof (own_valid_2 (A:=authR (option (excl nat) * gset_disj nat)%type) with "Hγ' Hγ''") as "%Hv".
      rewrite -auth_frag_op -pair_op in Hv.
      rewrite auth_frag_valid pair_valid in Hv.
      destruct Hv as [_ Hv].
      rewrite gset_disj_valid_op elem_of_disjoint in Hv.
      specialize (Hv t).
      rewrite elem_of_singleton in Hv.
      by destruct Hv.
    + iPoseProof (own_valid with "Hι") as "%Hi".
      apply auth_both_valid_discrete in Hi.
      destruct Hi as [Hi _].
      apply nat_included in Hi.
      iPoseProof (own_valid_2 with "Hγ Hγ'") as "%Hv".
      apply auth_both_valid_discrete in Hv.
      destruct Hv as [Hv _].
      apply pair_included in Hv.
      destruct Hv as [_ Hv].
      apply gset_disj_included in Hv.
      apply singleton_subseteq_l in Hv.
      apply elem_of_set_seq in Hv.
      destruct Hv as [Ho Ht].
      assert (o `mod` cap ≠ t `mod` cap) as H'.
      {
        intros e.
        apply mod_eq in e.
        destruct e as [[d ->]|[d ->]].
        - apply Nat.le_add_le_sub_r in Ho.
          rewrite Nat.sub_diag in Ho.
          apply Nat.le_0_r in Ho.
          apply Nat.eq_mul_0_r in Ho.
          2: by apply Nat.lt_neq in Hcap.
          subst d.
          by rewrite Nat.mul_0_r in H.
        - rewrite (comm _ o) in Ht.
          apply Nat.le_lt_add_lt in Ht; last done.
          destruct d.
          { by rewrite Nat.mul_0_r in H. }
          rewrite -mult_n_Sm Nat.lt_nge in Ht.
          contradict Ht.
          trans cap; first done.
          apply Nat.le_add_l.
      }
      iPoseProof (lookup_array _ _ _ (t `mod` cap) #false with "Ha") as "[Ht Ha]".
      {
        rewrite list_lookup_insert_ne //.
        apply lookup_replicate_2, Nat.mod_upper_bound.
        by apply Nat.lt_neq in Hcap.
      }
      wp_load.
      iModIntro.
      iSpecialize ("Ha" with "Ht").
      iSplitL "Hγ'' Hn Hι Hγ Ha Hr".
      {
        iNext.
        iExists o, i, _.
        iFrame "Hn Ha Hι Hγ".
        iRight; iRight.
        by iFrame.
      }
      wp_pures.
      iApply ("IH" with "Hγ' HΦ").
Qed.

Lemma acquire_spec (γ : name) (l : val) (cap : nat) (R : iProp Σ) :
  {{{ is_lock γ l cap R ∗ invitation γ 1 }}}
    acquire l
  {{{ (o : nat), RET #o; R ∗ locked γ o }}}.
Proof.
  iIntros "%Φ [(%a & %n & -> & %Hcap & #I) Hι'] HΦ".
  rewrite /invitation.
  wp_lam.
  wp_pures.
  wp_bind (FAA _ _).
  iInv "I" as "(%o & %i & %xs & >Hn & >Ha & >Hι & >Hγ & H)".
  iCombine "Hι Hι'" as "Hι".
  rewrite -assoc -auth_frag_op (comm _ i 1).
  iMod (own_update _ _ (● (Excl' o, GSet (set_seq o (S i))) ⋅ ◯ (None, GSet {[o + i]})) with "Hγ") as "[Hγ Hγ']".
  {
    apply auth_update_alloc, prod_local_update_2.
    rewrite -(right_id ε (⋅) (GSet {[_]})).
    rewrite set_seq_S_end_union_L -gset_disj_union.
    - apply op_local_update_discrete.
      intros _.
      apply gset_disj_valid_op.
      apply set_seq_S_end_disjoint.
    - apply set_seq_S_end_disjoint.
  }
  wp_faa.
  iModIntro.
  iSplitL "Hn Ha Hι Hγ H".
  {
    iNext.
    iExists o, (S i), _.
    change 1%Z with (Z.of_nat 1).
    rewrite -!Nat2Z.inj_add.
    rewrite -Nat.add_assoc (Nat.add_comm i 1).
    iFrame "Hn Ha Hι Hγ H".
  }
  wp_pures.
  rewrite -Nat2Z.inj_add.
  wp_apply (wait_spec with "[I $Hγ']").
  {
    iExists a, n.
    by iFrame "I".
  }
  iIntros "Hγ".
  wp_pures.
  iApply ("HΦ" with "Hγ").
Qed.

Lemma release_spec (γ : name) (l : val) (o cap : nat) (R : iProp Σ) :
  {{{ is_lock γ l cap R ∗ R ∗ locked γ o }}}
    release l #o
  {{{ RET #(); invitation γ 1 }}}.
Proof.
  iIntros "%Φ ((%a & %n & -> & %Hcap & #I) & HR & Hγ' & Hr) HΦ".
  wp_lam.
  wp_pures.
  rewrite -rem_of_nat.
  wp_bind (_ <- _)%E.
  iInv "I" as "(%o' & %i & %xs & >Hn & >Ha & >Hι & >Hγ & [
    (_ & _ & _ & >Hr' & _) |[
    (_ & >Hr' & _) |
    (Hγ'' & Hl & >->)
  ]])".
  { by iPoseProof (own_valid_2 with "Hr Hr'") as "%H". }
  { by iPoseProof (own_valid_2 with "Hr Hr'") as "%H". }
  iPoseProof (own_valid_2 with "Hγ Hγ'") as "%H".
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  apply pair_included in H.
  destruct H as [H _].
  apply Excl_included, leibniz_equiv in H.
  subst o'.
  iPoseProof (update_array _ _ _ (o `mod` cap) #true with "Ha") as "[Ht Ha]".
  {
    apply list_lookup_insert.
    rewrite replicate_length.
    apply Nat.mod_upper_bound.
    by apply Nat.lt_neq in Hcap.
  }
  wp_store.
  iModIntro.
  iSpecialize ("Ha" with "Ht").
  iSplitL "Hn Hι Hγ Hr Ha Hγ''".
  {
    iNext.
    rewrite list_insert_insert insert_replicate.
    iExists o, i, _.
    iFrame "Hn Ha Hι Hγ".
    iRight; iLeft.
    by iFrame.
  }
  clear i.
  wp_pures.
  iInv "I" as "(%o' & %i & %xs & >Hn & >Ha & >Hι & >Hγ & [
    (_ & _ & >Hl' & _) |[
    (>Hγ'' & >Hr & >->) |
    (_ & >Hl' & _)
  ]])".
  change 1%Z with (Z.of_nat 1).
  - by iPoseProof (own_valid_2 with "Hl Hl'") as "%H".
  - rewrite /issued.
    iPoseProof (own_valid_2 with "Hγ Hγ'") as "%H".
    rewrite auth_both_valid_discrete pair_included in H.
    destruct H as [[H _] _].
    apply Excl_included, leibniz_equiv in H.
    subst o'.
    destruct i; simpl.
    {
      iPoseProof (own_valid_2 with "Hγ Hγ''") as "%H".
      rewrite auth_both_valid_discrete pair_included in H.
      destruct H as [[_ H] _].
      apply gset_disj_included in H.
      apply elem_of_subseteq_singleton in H.
      by apply not_elem_of_empty in H.
    }
    change (S i) with (1 ⋅ i) at 2.
    rewrite (comm (⋅) 1) auth_frag_op assoc.
    iDestruct "Hι" as "[Hι Hι']".
    iCombine "Hγ Hγ' Hγ''" as "Hγ".
    rewrite -auth_frag_op -pair_op.
    rewrite left_id_L right_id_L.
    rewrite -gset_disj_union.
    2: apply set_seq_S_start_disjoint.
    iMod ((own_update _ _ (● (Excl' (S o), GSet (set_seq (S o) i)) ⋅ (◯ (Excl' (S o), GSet ∅) ⋅ ◯ (None, GSet ∅)))) with "Hγ") as "(Hγ & Hγ' & Hγ'')".
    {
      rewrite -auth_frag_op -pair_op.
      rewrite left_id_L right_id_L.
      apply (auth_update (Excl' o, GSet {[o]} ⋅ GSet (set_seq (S o) i))).
      apply prod_local_update'.
      - apply option_local_update.
        by apply exclusive_local_update.
      - apply gset_disj_dealloc_empty_local_update.
    }
    change 1%Z with (Z.of_nat 1).
    rewrite -!Nat2Z.inj_add (Nat.add_comm _ 1) /=.
    rewrite -rem_of_nat.
    iPoseProof (update_array _ _ _ (S o `mod` cap) #false with "Ha") as "[Ht Ha]".
    {
      apply lookup_replicate.
      split; first done.
      apply Nat.mod_upper_bound.
      by apply Nat.lt_neq in Hcap.
    }
    wp_store.
    iModIntro.
    iSplitR "HΦ Hι'".
    {
      iNext.
      iExists (S o), i.
      rewrite -Nat2Z.inj_add Nat.add_succ_comm.
      iSpecialize ("Ha" with "Ht").
      iExists _.
      iFrame.
      iLeft.
      by iFrame.
    }
    iApply ("HΦ" with "Hι'").
  - by iPoseProof (own_valid_2 with "Hl Hl'") as "%H".
Qed.

End proofs.
