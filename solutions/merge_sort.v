From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import array lang proofmode notation par.

(*
  Let us implement a simple multitheaded merge sort on arrays. Merge
  sort consists of splitting the array in half until we are left with
  pieces of size 0 or 1. Then each pair of pieces are merged into a
  new sorted array.
*)

(*
  We merge two arrays a1 and a2 of lengths n1 and n2 into an array b
  of length n1 + n2.
*)
Definition merge_inner : val :=
  rec: "merge" "a1" "n1" "a2" "n2" "b" :=
  (* If a1 is empty, we simply copy the second a2 into b *)
  if: "n1" = #0 then
    array_copy_to "b" "a2" "n2"
  (* Likewise if a2 is empty instead *)
  else if: "n2" = #0 then
    array_copy_to "b" "a1" "n1"
  else
  (*
    Otherwise we compare the first elements of a1 and a2. The least is
    removed and written to b. Rince and repeat.
  *)
    let: "x1" := !"a1" in
    let: "x2" := !"a2" in
    if: "x1" ≤ "x2" then
      "b" <- "x1";;
      "merge" ("a1" +ₗ #1) ("n1" - #1) "a2" "n2" ("b" +ₗ #1)
    else
      "b" <- "x2";;
      "merge" "a1" "n1" ("a2" +ₗ #1) ("n2" - #1) ("b" +ₗ #1).

(*
  Heaplang recuires array allocations to contain atleast 1 element. So
  in the case that either of the peaces is empty, we simply return the
  other.
*)
Definition merge : val :=
  λ: "a1" "n1" "a2" "n2",
  if: "n1" = #0 then
    "a2"
  else if: "n2" = #0 then
    "a1"
  else
    let: "b" := AllocN ("n1" + "n2") #() in
    merge_inner "a1" "n1" "a2" "n2" "b";;
    "b".

(*
  To sort we simply split the array in half. Sort them on seperate
  threads. Then the results are merged together.
*)
Definition merge_sort : val :=
  rec: "merge_sort" "a" "n" :=
  if: "n" ≤ #1 then
    "a"
  else
    let: "n1" := "n" `quot` #2 in
    let: "n2" := "n" - "n1" in
    let: "p" := ("merge_sort" "a" "n1" ||| "merge_sort" ("a" +ₗ "n1") "n2") in
    merge (Fst "p") "n1" (Snd "p") "n2".

(*
  Our desired specification will be that sort produces a new sorted
  array that's a permutation of the input.

  We define sorting as follows:
*)
Inductive sorted : list Z → Prop :=
  | sorted_nil : sorted []
  | sorted_singleton x : sorted [x]
  | sorted_cons_cons x y l : (x ≤ y)%Z → sorted (y :: l) → sorted (x :: y :: l).

(*
  Alternatively a list is sorted if all ordered pairs of indecies
  corresponds to orderered values.
*)
Lemma sorted_alt l : sorted l ↔ ∀ i j x y, l !! i = Some x → l !! j = Some y → i ≤ j → (x ≤ y)%Z.
Proof.
  split.
  - induction 1 as [|x|x y l H Hl IH].
    + intros i j x y H.
      done.
    + intros i j y z Hi Hj _.
      apply list_lookup_singleton_Some in Hi.
      apply list_lookup_singleton_Some in Hj.
      destruct Hi as [-> <-].
      destruct Hj as [-> <-].
      done.
    + intros i j z w Hi Hj Hle.
      destruct i, j; cbn in Hi, Hj.
      -- injection Hi as <-.
        injection Hj as <-.
        done.
      -- injection Hi as <-.
        trans y=>//.
        apply (IH 0 j)=>//.
        apply le_0_n.
      -- inversion Hle.
      -- by apply (IH i j), le_S_n.
  - intros H.
    induction l as [|x [|y l] IH].
    all: constructor.
    + apply (H 0 1)=>//.
      by constructor.
    + apply IH => i j z w Hi Hj Hle.
      by apply (H (S i) (S j)), le_n_S.
Qed.

Lemma sorted_cons x l : sorted (x :: l) ↔ sorted l ∧ ∀ y, y ∈ l → (x ≤ y)%Z.
Proof.
  rewrite !sorted_alt.
  split.
  - intros H.
    split.
    + intros i j y z Hi Hj Hle.
      by apply (H (S i) (S j)), le_n_S.
    + intros y Hy.
      apply elem_of_list_lookup in Hy.
      destruct Hy as [i Hi].
      by apply (H 0 (S i)), le_0_n.
  - intros [H H0] i j y z Hi Hj Hle.
    destruct i, j; cbn in *.
    + injection Hi as <-.
      injection Hj as <-.
      done.
    + injection Hi as <-.
      apply H0, elem_of_list_lookup.
      by exists j.
    + inversion Hle.
    + by apply (H i j), le_S_n.
Qed.

Lemma sorted_le_1 l : length l ≤ 1 → sorted l.
Proof.
  intros H.
  destruct l as [|x [|y l]].
  - apply sorted_nil.
  - apply sorted_singleton.
  - contradict H.
    apply Nat.lt_nge=>/=.
    apply le_n_S, le_n_S, le_0_n.
Qed.

Section proofs.
Context `{!heapGS Σ, !spawnG Σ}.

(*
  To merge to arrays a1 and a2, we require that they are both already
  sorted. Furthermore we need the result array b to have enough space,
  though we don't care what it contains.
*)
Lemma merge_inner_spec (a1 a2 b : loc) (l1 l2 : list Z) (l : list val) :
  {{{a1 ↦∗ ((λ x : Z, #x) <$> l1) ∗ a2 ↦∗ ((λ x : Z, #x) <$> l2) ∗ b ↦∗ l ∗ ⌜sorted l1⌝ ∗ ⌜sorted l2⌝ ∗ ⌜length l = (length l1 + length l2)%nat⌝}}}
    merge_inner #a1 #(length l1) #a2 #(length l2) #b
  {{{(l : list Z), RET #(); b ↦∗ ((λ x : Z, #x) <$> l) ∗ ⌜sorted l⌝ ∗ ⌜l1 ++ l2 ≡ₚ l⌝}}}.
Proof.
  iIntros "%Φ (Ha1 & Ha2 & Hb & %Hl1 & %Hl2 & %H) HΦ".
  iLöb as "IH" forall (a1 a2 b l1 l2 l Hl1 Hl2 H).
  wp_rec.
  wp_pures.
  destruct l1 as [|x1 l1].
  {
    rewrite nil_length Nat.add_0_l in H.
    wp_pures.
    iApply (wp_array_copy_to with "[$Hb $Ha2]").
    - by rewrite H.
    - by rewrite fmap_length.
    - iIntros "!> [Hb Ha2]".
      iApply "HΦ".
      by iFrame.
  }
  destruct l2 as [|x2 l2].
  {
    rewrite nil_length Nat.add_0_r in H.
    wp_pures.
    iApply (wp_array_copy_to with "[$Hb $Ha1]").
    - by rewrite H.
    - by rewrite fmap_length.
    - iIntros "!> [Hb Ha1]".
      iApply "HΦ".
      iFrame.
      by rewrite app_nil_r.
  }
  wp_pures.
  rewrite !cons_length Nat.add_succ_l Nat.add_succ_r in H.
  destruct l as [|y l]=>//.
  cbn in H.
  injection H as H.
  rewrite !fmap_cons !array_cons.
  iDestruct "Ha1" as "[Hx1 Ha1]".
  iDestruct "Ha2" as "[Hx2 Ha2]".
  iDestruct "Hb" as "[Hy Hb]".
  wp_load.
  wp_load.
  wp_pures.
  destruct (bool_decide_reflect (x1 ≤ x2)%Z) as [Hx|Hx].
  - wp_pures.
    wp_store.
    wp_pures.
    rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    iApply ("IH" $! (a1 +ₗ 1) a2 (b +ₗ 1) l1 (x2 :: l2) l with "[] [] [] Ha1 [Hx2 Ha2] Hb").
    + iPureIntro.
      by eapply sorted_cons.
    + done.
    + iPureIntro.
      cbn.
      by rewrite Nat.add_succ_r.
    + rewrite fmap_cons array_cons.
      iFrame.
    + iIntros "!> %l3 (Hb & %Hl3 & %Hp)".
      iApply ("HΦ" $! (x1 :: l3)).
      rewrite fmap_cons array_cons.
      iFrame.
      iPureIntro.
      split.
      -- apply sorted_cons.
        split=>// z Hz.
        rewrite -Hp elem_of_app elem_of_cons in Hz.
        destruct Hz as [Hz|[->|Hz]].
        ++ by apply sorted_cons with l1.
        ++ done.
        ++ trans x2=>//.
          by apply sorted_cons with l2.
      -- by apply Permutation_skip.
  - apply Z.nle_gt, Z.lt_le_incl in Hx.
    wp_pures.
    wp_store.
    wp_pures.
    rewrite (Nat2Z.inj_succ (length l2)) Z.sub_1_r Z.pred_succ.
    iApply ("IH" $! a1 (a2 +ₗ 1) (b +ₗ 1) (x1 :: l1) l2 l with "[] [] [] [Hx1 Ha1] Ha2 Hb").
    + done.
    + iPureIntro.
      by eapply sorted_cons.
    + done.
    + rewrite fmap_cons array_cons.
      iFrame.
    + iIntros "!> %l3 (Hb & %Hl3 & %Hp)".
      iApply ("HΦ" $! (x2 :: l3)).
      rewrite fmap_cons array_cons.
      iFrame.
      iPureIntro.
      split.
      -- apply sorted_cons.
        split=>// z Hz.
        rewrite -Hp elem_of_app elem_of_cons in Hz.
        destruct Hz as [[->|Hz]|Hz].
        ++ done.
        ++ trans x1=>//.
          by apply sorted_cons with l1.
        ++ by apply sorted_cons with l2.
      -- by apply (Permutation_elt _ l2 [] l3 x2).
Qed.

Lemma merge_spec (a1 a2 : loc) (l1 l2 : list Z) :
  {{{a1 ↦∗ ((λ x : Z, #x) <$> l1) ∗ a2 ↦∗ ((λ x : Z, #x) <$> l2) ∗ ⌜sorted l1⌝ ∗ ⌜sorted l2⌝}}}
    merge #a1 #(length l1) #a2 #(length l2)
  {{{(b : loc) (l : list Z), RET #b; b ↦∗ ((λ x : Z, #x) <$> l) ∗ ⌜sorted l⌝ ∗ ⌜l1 ++ l2 ≡ₚ l⌝}}}.
Proof.
  iIntros "%Φ (Ha1 & Ha2 & Hl1 & Hl2) HΦ".
  wp_lam.
  wp_pures.
  destruct (bool_decide_reflect (#(length l1) = #0)) as [H1|H1].
  {
    change 0%Z with (Z.of_nat 0) in H1.
    injection H1 as H1.
    destruct l1=>//.
    wp_pures.
    iApply "HΦ".
    iModIntro.
    by iFrame "Ha2 Hl2".
  }
  wp_pures.
  destruct (bool_decide_reflect (#(length l2) = #0)) as [H2|H2].
  {
    change 0%Z with (Z.of_nat 0) in H2.
    injection H2 as H2.
    destruct l2=>//.
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iFrame "Ha1 Hl1".
    by rewrite app_nil_r.
  }
  wp_pures.
  wp_alloc b as "Hb".
  {
    change 0%Z with (Z.of_nat 0).
    rewrite -Nat2Z.inj_add.
    apply inj_lt.
    destruct l1=>//=.
    apply le_n_S, le_0_n.
  }
  wp_pures.
  wp_apply (merge_inner_spec with "[$Ha1 $Ha2 $Hb $Hl1 $Hl2]").
  {
    iPureIntro.
    rewrite -Nat2Z.inj_add Nat2Z.id.
    apply replicate_length.
  }
  iIntros "%l H".
  wp_pures.
  iApply ("HΦ" with "H").
Qed.

(*
  With this we can finally prove that sort actually sorts the output.
*)
Lemma merge_sort_spec (a : loc) (l : list Z) :
  {{{a ↦∗ ((λ x : Z, #x) <$> l)}}}
    merge_sort #a #(length l)
  {{{(b : loc) (l' : list Z), RET #b; b ↦∗ ((λ x : Z, #x) <$> l') ∗ ⌜sorted l'⌝ ∗ ⌜l ≡ₚ l'⌝}}}.
Proof.
  iIntros "%Φ Ha HΦ".
  iLöb as "IH" forall (a l Φ).
  wp_rec.
  wp_pures.
  destruct (bool_decide_reflect (length l ≤ 1)%Z) as [H|H].
  {
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame.
    iSplitL=>//.
    iPureIntro.
    apply sorted_le_1, Nat2Z.inj_le, H.
  }
  apply Z.nle_gt, (Nat2Z.inj_lt 1) in H.
  wp_pures.
  rewrite Z.quot_div_nonneg //; last apply Nat2Z.is_nonneg.
  change 2%Z with (Z.of_nat 2).
  rewrite -Nat2Z.inj_div.
  assert (length l `div` 2 ≤ length l).
  {
    apply Nat.lt_le_incl, Nat.div_lt.
    - eapply Nat.lt_trans=>//.
      apply Nat.lt_0_1.
    - apply Nat.lt_1_2.
  }
  rewrite -Nat2Z.inj_sub //.
  assert (∃ l1 l2, l1 ++ l2 = l ∧ length l1 = length l `div` 2) as (l1 & l2 & <- & <-).
  {
    exists (take (length l `div` 2) l), (drop (length l `div` 2) l).
    split.
    - apply take_drop.
    - by apply firstn_length_le.
  }
  clear H0.
  rewrite app_length in H.
  rewrite app_length Nat.sub_add'.
  rewrite fmap_app array_app fmap_length.
  iDestruct "Ha" as "[Ha1 Ha2]".
  wp_apply (par_spec
    (λ v, ∃ (b : loc) l', ⌜#b = v⌝ ∗ b ↦∗ ((λ x : Z, #x) <$> l') ∗ ⌜sorted l'⌝ ∗ ⌜l1 ≡ₚ l'⌝)%I
    (λ v, ∃ (b : loc) l', ⌜#b = v⌝ ∗ b ↦∗ ((λ x : Z, #x) <$> l') ∗ ⌜sorted l'⌝ ∗ ⌜l2 ≡ₚ l'⌝)%I
    with "[Ha1] [Ha2]"
  ).
  - wp_pures.
    wp_apply ("IH" with "Ha1").
    iIntros "%b %l' H".
    iExists b, l'.
    by iFrame.
  - wp_pures.
    wp_apply ("IH" with "Ha2").
    iIntros "%b %l' H".
    iExists b, l'.
    by iFrame.
  - iIntros (? ?) "[
      (%b1 & %l1' & <- & Hb1 & %Hl1 & %H1)
      (%b2 & %l2' & <- & Hb2 & %Hl2 & %H2)
    ] !>".
    wp_pures.
    rewrite (Permutation_length H1) (Permutation_length H2).
    wp_apply (merge_spec with "[$Hb1 $Hb2]")=>//.
    iIntros "%b %l (Hb & Hl & %Hl)".
    iApply "HΦ".
    iFrame.
    iPureIntro.
    by rewrite H1 H2.
Qed.

End proofs.
