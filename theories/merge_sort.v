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
  (* FILL IN HERE *) Admitted.

Lemma merge_spec (a1 a2 : loc) (l1 l2 : list Z) :
  {{{a1 ↦∗ ((λ x : Z, #x) <$> l1) ∗ a2 ↦∗ ((λ x : Z, #x) <$> l2) ∗ ⌜sorted l1⌝ ∗ ⌜sorted l2⌝}}}
    merge #a1 #(length l1) #a2 #(length l2)
  {{{(b : loc) (l : list Z), RET #b; b ↦∗ ((λ x : Z, #x) <$> l) ∗ ⌜sorted l⌝ ∗ ⌜l1 ++ l2 ≡ₚ l⌝}}}.
Proof.
  (* FILL IN HERE *) Admitted.

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
  (* FILL IN HERE *) Admitted.

End proofs.
