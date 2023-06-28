From iris.heap_lang Require Import lang proofmode notation.

Section proofs.
Context `{heapGS Σ}.

(*
  Thus far we've looked at linked lists as our main list
  implementation. However heaplang also supports arrays. `AllocN n v`
  allocates n contiguous copies of v and returns the location of the
  first element. Then to access a values we can perform offsets
  `l +ₗ i` and then perform a load.

  To see arrays in action, let's implement a function that copies an
  array, while keeping the origional intact.
*)

Definition copy_to : val :=
  rec: "copy_to" "src" "dst" "len" :=
  if: "len" = #0 then #()
  else
    "dst" <- !"src";;
    "copy_to" ("src" +ₗ #1) ("dst" +ₗ #1) ("len" - #1).

Definition copy : val :=
  λ: "src" "len",
  let: "dst" := AllocN "len" #() in
  copy_to "src" "dst" "len";;
  "dst".

(*
  Just as with is_list, arrays have a predicate we can use written
  l ↦∗ vs. Where l is the location of the first element in the array,
  and vs is a list of the values currently stored at each location.
*)

Lemma copy_to_spec a1 a2 l1 l2 :
  {{{a1 ↦∗ l1 ∗ a2 ↦∗ l2 ∗ ⌜length l1 = length l2⌝}}}
    copy_to #a1 #a2 #(length l1)
  {{{RET #(); a1 ↦∗ l1 ∗ a2 ↦∗ l1}}}.
Proof.
  iIntros "%Φ (H1 & H2 & %H) HΦ".
  iLöb as "IH" forall (a1 a2 l1 l2 H).
  destruct l1 as [|v1 l1], l2 as [|v2 l2]=>//.
  - wp_rec; wp_pures.
    (*
      The empty array predicate is trivial, as it says nothing about
      the values on the heap. So we can use array_nil to rewrite them
      into emp, which in Iris is just a synonym for True.
    *)
    rewrite !array_nil.
    iModIntro.
    by iApply "HΦ".
  - wp_rec; wp_pures.
    (*
      For the cons case we can use array_cons to split the array into
      a mapsto on the first location, with the remaining array
      starting at the next location.
    *)
    rewrite !array_cons.
    iDestruct "H1" as "[H1 Hl1]".
    iDestruct "H2" as "[H2 Hl2]".
    wp_load.
    wp_store.
    wp_pures.
    rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    wp_apply ("IH" with "[] Hl1 Hl2").
    { by injection H. }
    iIntros "[Hl1 Hl2]".
    iApply "HΦ".
    iFrame.
Qed.

(*
  When allocating arrays, heaplang requires the size be greater than
  zero. So we add this to our precondition.
*)
Lemma copy_spec a l :
  {{{a ↦∗ l ∗ ⌜0 < length l⌝}}}
    copy #a #(length l)
  {{{(a' : loc), RET #a'; a ↦∗ l ∗ a' ↦∗ l}}}.
Proof.
  iIntros "%Φ [Ha %H] HΦ".
  wp_lam; wp_pures.
  wp_alloc a' as "Ha'".
  { apply (Nat2Z.inj_lt 0), H. }
  rewrite Nat2Z.id.
  wp_pures.
  wp_apply (copy_to_spec with "[$Ha $Ha']").
  {
    iPureIntro.
    symmetry.
    apply replicate_length.
  }
  iIntros "[Ha Ha']".
  wp_pures.
  iApply "HΦ".
  by iFrame.
Qed.

(*
  Now let's reimplement some of the functions we use for linked lists.
*)
Definition inc : val :=
  rec: "inc" "arr" "len" :=
  if: "len" = #0 then #()
  else
    "arr" <- !"arr" + #1;;
    "inc" ("arr" +ₗ #1) ("len" - #1).

Lemma inc_spec a l :
  {{{a ↦∗ ((λ i : Z, #i) <$> l)}}}
    inc #a #(length l)
  {{{RET #(); a ↦∗ ((λ i : Z, #(i + 1)) <$> l)}}}.
Proof.
  iIntros "%Φ Ha HΦ".
  iInduction l as [|i l] "IH" forall (a).
  - wp_rec.
    wp_pures.
    iApply "HΦ".
    done.
  - rewrite !fmap_cons !array_cons.
    iDestruct "Ha" as "[Hi Ha]".
    wp_rec.
    wp_pures.
    wp_load.
    wp_pures.
    wp_store.
    wp_pures.
    rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    wp_apply ("IH" with "Ha").
    iIntros "Ha".
    iApply "HΦ".
    iFrame.
Qed.

(*
  To reverse an array, we will swap the first and last value. Then
  we'll recursively repeat this process on the remaining array.
*)
Definition reverse : val :=
  rec: "reverse" "arr" "len" :=
  if: "len" ≤ #1 then #()
  else
    let: "last" := "arr" +ₗ ("len" - #1) in
    let: "tmp" := !"arr" in
    "arr" <- !"last";;
    "last" <- "tmp";;
    "reverse" ("arr" +ₗ #1) ("len" - #2).

(*
  Notice we are not following structural induction on the list of
  values as we remove elements from both the front and the back. As
  such you need to use either löb induction or strong induction on the
  size of the list.
*)
Lemma reverse_spec a l :
  {{{a ↦∗ l}}}
    reverse #a #(length l)
  {{{RET #(); a ↦∗ rev l}}}.
Proof.
  iIntros "%Φ Ha HΦ".
  iLöb as "IH" forall (a l).
  wp_rec.
  wp_pures.
  destruct (bool_decide_reflect (length l ≤ 1)%Z) as [H|H].
  - apply (Nat2Z.inj_le _ 1) in H.
    wp_pures.
    iApply "HΦ".
    destruct l as [|v1 [|v2 l]]=>//.
    cbn in H.
    apply le_S_n in H.
    inversion H.
  - apply Z.nle_gt in H.
    induction l as [|v2 l _] using rev_ind=>//.
    destruct l as [|v1 l]=>//.
    clear H.
    change (v1 :: ?l) with ([v1] ++ l) at 2.
    rewrite !rev_app_distr app_length Nat2Z.inj_add /=.
    rewrite !array_cons !array_app !array_singleton.
    rewrite rev_length loc_add_assoc.
    iDestruct "Ha" as "(Hv1 & Hl & Hv2)".
    wp_pures.
    wp_load.
    wp_pures.
    rewrite Z.add_simpl_r.
    change 1%Z with (Z.of_nat 1) at 2 4.
    rewrite -Nat2Z.inj_add /=.
    wp_load.
    wp_store.
    wp_store.
    wp_pures.
    rewrite {3}Nat2Z.inj_succ Z.add_succ_comm.
    rewrite (Z.add_simpl_r _ 2).
    wp_apply ("IH" with "Hl").
    iIntros "Hl".
    iApply "HΦ".
    iFrame.
Qed.

End proofs.
