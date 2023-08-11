From stdpp Require Export sorting.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import array lang proofmode notation par.

(**
  Let us implement a simple multitheaded merge sort on arrays. Merge
  sort consists of splitting the array in half until we are left with
  pieces of size 0 or 1. Then each pair of pieces are merged into a
  new sorted array.
*)

(**
  We merge two arrays a1 and a2 of lengths n1 and n2 into an array b
  of length n1 + n2.
*)
Definition merge : val :=
  rec: "merge" "a1" "n1" "a2" "n2" "b" :=
  (** If a1 is empty, we simply copy the second a2 into b *)
  if: "n1" = #0 then
    array_copy_to "b" "a2" "n2"
  (** Likewise if a2 is empty instead *)
  else if: "n2" = #0 then
    array_copy_to "b" "a1" "n1"
  else
  (**
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

(**
  To sort we simply split the array in half. Sort them on seperate
  threads. Then the results are merged together and copied back into the array.
*)
Definition merge_sort_inner : val :=
  rec: "merge_sort_inner" "a" "b" "n" :=
  if: "n" ≤ #1 then #()
  else
    let: "n1" := "n" `quot` #2 in
    let: "n2" := "n" - "n1" in
    ("merge_sort_inner" "b" "a" "n1" ||| "merge_sort_inner" ("b" +ₗ "n1") ("a" +ₗ "n1") "n2");;
    merge "b" "n1" ("b" +ₗ "n1") "n2" "a".

(**
  Heaplang recuires array allocations to contain atleast 1 element. So
  we need to treat this case seperatly.
*)
Definition merge_sort : val :=
  λ: "a" "n",
  if: "n" = #0 then #()
  else
    let: "b" := AllocN "n" #() in
    array_copy_to "b" "a" "n";;
    merge_sort_inner "a" "b" "n".

(**
  Our desired specification will be that sort produces a new sorted
  array that's a permutation of the input.
*)

Section proofs.
Context `{!heapGS Σ, !spawnG Σ}.

(**
  To merge to arrays a1 and a2, we require that they are both already
  sorted. Furthermore we need the result array b to have enough space,
  though we don't care what it contains.
*)
Lemma merge_spec (a1 a2 b : loc) (l1 l2 : list Z) (l : list val) :
  {{{
    a1 ↦∗ ((λ x : Z, #x) <$> l1) ∗
    a2 ↦∗ ((λ x : Z, #x) <$> l2) ∗ b ↦∗ l ∗
    ⌜StronglySorted Z.le l1⌝ ∗
    ⌜StronglySorted Z.le l2⌝ ∗
    ⌜length l = (length l1 + length l2)%nat⌝
  }}}
    merge #a1 #(length l1) #a2 #(length l2) #b
  {{{(l : list Z), RET #();
    a1 ↦∗ ((λ x : Z, #x) <$> l1) ∗
    a2 ↦∗ ((λ x : Z, #x) <$> l2) ∗
    b ↦∗ ((λ x : Z, #x) <$> l) ∗
    ⌜StronglySorted Z.le l⌝ ∗
    ⌜l1 ++ l2 ≡ₚ l⌝
  }}}.
Proof.
  (* Exercise start *)
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
  apply StronglySorted_inv in Hl1 as [H1 Hl1].
  apply StronglySorted_inv in Hl2 as [H2 Hl2].
  wp_pures.
  rewrite !cons_length Nat.add_succ_l Nat.add_succ_r in H.
  destruct l as [|y l]=>//.
  cbn in H.
  injection H as H.
  rewrite !fmap_cons.
  setoid_rewrite array_cons.
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
    + done.
    + iPureIntro.
      by apply SSorted_cons.
    + iPureIntro.
      cbn.
      by rewrite Nat.add_succ_r.
    + rewrite fmap_cons array_cons.
      iFrame.
    + iIntros "!> %l3 (Ha1 & Ha2 & Hb & %Hl3 & %Hp)".
      iApply ("HΦ" $! (x1 :: l3)).
      rewrite fmap_cons array_cons.
      iFrame.
      iPureIntro.
      split.
      -- apply SSorted_cons=>//.
        rewrite -Hp.
        rewrite Forall_app Forall_cons.
        split_and!=>//.
        eapply Forall_impl=>//.
        intros z Hz.
        by etrans.
      -- by apply Permutation_skip.
  - apply Z.nle_gt, Z.lt_le_incl in Hx.
    wp_pures.
    wp_store.
    wp_pures.
    rewrite (Nat2Z.inj_succ (length l2)) Z.sub_1_r Z.pred_succ.
    iApply ("IH" $! a1 (a2 +ₗ 1) (b +ₗ 1) (x1 :: l1) l2 l with "[] [] [] [Hx1 Ha1] Ha2 Hb").
    + iPureIntro.
      by apply SSorted_cons.
    + done.
    + done.
    + rewrite fmap_cons array_cons.
      iFrame.
    + iIntros "!> %l3 (Ha1 & Ha2 & Hb & %Hl3 & %Hp)".
      iApply ("HΦ" $! (x2 :: l3)).
      rewrite fmap_cons array_cons.
      iFrame.
      iPureIntro.
      split.
      -- apply SSorted_cons=>//.
        rewrite -Hp /=.
        rewrite Forall_cons Forall_app.
        split_and!=>//.
        eapply Forall_impl=>//.
        intros z Hz.
        by etrans.
      -- by apply (Permutation_elt _ l2 [] l3 x2).
Qed.

(**
  With this we can prove that sort actually sorts the output.
*)
Lemma merge_sort_inner_spec (a b : loc) (l : list Z) :
  {{{
    a ↦∗ ((λ x : Z, #x) <$> l) ∗
    b ↦∗ ((λ x : Z, #x) <$> l)
  }}}
    merge_sort_inner #a #b #(length l)
  {{{(l' : list Z) vs, RET #();
    a ↦∗ ((λ x : Z, #x) <$> l') ∗
    b ↦∗ vs ∗ ⌜StronglySorted Z.le l'⌝ ∗
    ⌜l ≡ₚ l'⌝ ∗
    ⌜length vs = length l'⌝
  }}}.
Proof.
  (* Exercise start *)
  iIntros "%Φ (Ha & Hb) HΦ".
  iLöb as "IH" forall (a b l Φ).
  wp_rec.
  wp_pures.
  destruct (bool_decide_reflect (length l ≤ 1)%Z) as [Hlen|Hlen].
  {
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    rewrite fmap_length.
    split; last done.
    apply (Nat2Z.inj_le _ 1) in Hlen.
    destruct l as [|i1 [|i2 l]].
    - apply SSorted_nil.
    - apply SSorted_cons=>//.
      apply SSorted_nil.
    - contradict Hlen=>/=. lia.
  }
  apply Z.nle_gt, (Nat2Z.inj_lt 1) in Hlen.
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
  clear H.
  rewrite app_length in Hlen.
  rewrite app_length Nat.sub_add'.
  rewrite fmap_app !array_app fmap_length.
  iDestruct "Ha" as "[Ha1 Ha2]".
  iDestruct "Hb" as "[Hb1 Hb2]".
  wp_apply (par_spec
    (λ v, ∃ l' vs, a ↦∗ vs ∗ b ↦∗ ((λ x : Z, #x) <$> l') ∗ ⌜StronglySorted Z.le l'⌝ ∗ ⌜l1 ≡ₚ l'⌝ ∗ ⌜length vs = length l'⌝)%I
    (λ v, ∃ l' vs, (a +ₗ length l1) ↦∗ vs ∗ (b +ₗ length l1) ↦∗ ((λ x : Z, #x) <$> l') ∗ ⌜StronglySorted Z.le l'⌝ ∗ ⌜l2 ≡ₚ l'⌝ ∗ ⌜length vs = length l'⌝)%I
    with "[Ha1 Hb1] [Ha2 Hb2]"
  ).
  - wp_pures.
    wp_apply ("IH" with "Hb1 Ha1").
    iIntros "%l' %vs (Ha & Hb & H)".
    iExists l', vs.
    iFrame.
  - wp_pures.
    wp_apply ("IH" with "Hb2 Ha2").
    iIntros "%l' %vs (Ha & Hb & H)".
    iExists l', vs.
    iFrame.
  - iIntros (? ?) "[
      (%l1' & %vs1 & Ha1 & Hb1 & %H1 & %Hl1 & %Hvs1)
      (%l2' & %vs2 & Ha2 & Hb2 & %H2 & %Hl2 & %Hvs2)
    ] !>".
    wp_pures.
    rewrite (Permutation_length Hl1) (Permutation_length Hl2) -{1}Hvs1.
    iCombine "Ha1 Ha2" as "Ha".
    rewrite -array_app.
    wp_apply (merge_spec with "[$Hb1 $Hb2 $Ha]").
    {
      iPureIntro.
      split_and!; [done..|].
      rewrite app_length.
      by f_equal.
    }
    iIntros "%l (Hb1 & Hb2 & Ha & Hl & %Hl)".
    iCombine "Hb1 Hb2" as "Hb".
    erewrite <-fmap_length, <-array_app, <-fmap_app.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    split.
    + by rewrite Hl1 Hl2.
    + rewrite fmap_length.
      by apply Permutation_length.
Qed.

Lemma merge_sort_spec (a : loc) (l : list Z) :
  {{{a ↦∗ ((λ x : Z, #x) <$> l)}}}
    merge_sort #a #(length l)
  {{{(l' : list Z), RET #();
    a ↦∗ ((λ x : Z, #x) <$> l') ∗
    ⌜StronglySorted Z.le l'⌝ ∗
    ⌜l ≡ₚ l'⌝
  }}}.
Proof.
  (* Exercise start *)
  iIntros "%Φ Ha HΦ".
  wp_lam.
  wp_pures.
  destruct (bool_decide_reflect (#(length l) = #0)).
  {
    injection e as e.
    apply (inj Z.of_nat _ 0), nil_length_inv in e as ->.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    split; last done.
    apply SSorted_nil.
  }
  wp_pures.
  wp_alloc b as "Hb".
  {
    apply Z.nle_gt.
    contradict n.
    by apply (Nat2Z.inj_le _ 0), Nat.le_0_r in n as ->.
  }
  rewrite Nat2Z.id.
  wp_pures.
  wp_apply (wp_array_copy_to with "[$Hb $Ha]").
  { by rewrite replicate_length. }
  { by rewrite fmap_length. }
  iIntros "[Hb Ha]".
  wp_pures.
  wp_apply (merge_sort_inner_spec with "[$Ha $Hb]").
  iIntros "%l' %vs (Ha & Hb & H & Hl & _)".
  iApply "HΦ".
  iFrame.
Qed.

End proofs.
