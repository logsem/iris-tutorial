From stdpp Require Export sorting.
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
Definition merge : val :=
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

(*
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

(*
  Our desired specification will be that sort produces a new sorted
  array that's a permutation of the input.
*)

Section proofs.
Context `{!heapGS Σ, !spawnG Σ}.

(*
  To merge to arrays a1 and a2, we require that they are both already
  sorted. Furthermore we need the result array b to have enough space,
  though we don't care what it contains.
*)
Lemma merge_spec (a1 a2 b : loc) (l1 l2 : list Z) (l : list val) :
  {{{a1 ↦∗ ((λ x : Z, #x) <$> l1) ∗ a2 ↦∗ ((λ x : Z, #x) <$> l2) ∗ b ↦∗ l ∗ ⌜StronglySorted Z.le l1⌝ ∗ ⌜StronglySorted Z.le l2⌝ ∗ ⌜length l = (length l1 + length l2)%nat⌝}}}
    merge #a1 #(length l1) #a2 #(length l2) #b
  {{{(l : list Z), RET #(); a1 ↦∗ ((λ x : Z, #x) <$> l1) ∗ a2 ↦∗ ((λ x : Z, #x) <$> l2) ∗ b ↦∗ ((λ x : Z, #x) <$> l) ∗ ⌜StronglySorted Z.le l⌝ ∗ ⌜l1 ++ l2 ≡ₚ l⌝}}}.
Proof.
  (* FILL IN HERE *) Admitted.

(*
  With this we can prove that sort actually sorts the output.
*)
Lemma merge_sort_inner_spec (a b : loc) (l : list Z) :
  {{{a ↦∗ ((λ x : Z, #x) <$> l) ∗ b ↦∗ ((λ x : Z, #x) <$> l)}}}
    merge_sort_inner #a #b #(length l)
  {{{(l' : list Z) vs, RET #(); a ↦∗ ((λ x : Z, #x) <$> l') ∗ b ↦∗ vs ∗ ⌜StronglySorted Z.le l'⌝ ∗ ⌜l ≡ₚ l'⌝ ∗ ⌜length vs = length l'⌝}}}.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma merge_sort_spec (a : loc) (l : list Z) :
  {{{a ↦∗ ((λ x : Z, #x) <$> l)}}}
    merge_sort #a #(length l)
  {{{(l' : list Z), RET #(); a ↦∗ ((λ x : Z, #x) <$> l') ∗ ⌜StronglySorted Z.le l'⌝ ∗ ⌜l ≡ₚ l'⌝}}}.
Proof.
  (* FILL IN HERE *) Admitted.

End proofs.
