From iris.heap_lang Require Import lang proofmode notation.

Section proofs.
Context `{!heapGS Σ}.

(*
  Like before, we can define linked lists recursively. However we can
  notice that no program can access the pointer `l` without checking
  whether the list is empty. As such the program must have taken at
  least one step. It should therefor not change much to add a later to
  the ownership of the tail of the list.

  This proposistion is different from the one in linked_lists. This
  difference however doesn't really matter from a program perspective.
  Infact it works better when working with concurrent code.
*)
Fixpoint is_list_of (v : val) (xs : list val) : iProp Σ :=
  match xs with
  | [] => ⌜v = NONEV⌝
  | x :: xs => ∃ l : loc, ⌜v = SOMEV #l⌝ ∗ ∃ t, l ↦ (x, t) ∗ ▷ is_list_of t xs
  end.

(*
  Sometimes we don't need to know the exact values of the list.
  Instead we just want them to satisfy some predicate, such as being a
  number. Let's define this in a similar weak sense, where the nth
  value only has to satisfy the predicate after n steps.
*)
Fixpoint list_all (xs : list val) (Φ : val → iProp Σ) : iProp Σ :=
  match xs with
  | [] => True
  | x :: xs => Φ x ∗ ▷ list_all xs Φ
  end.

(*
  With these we can define what it means for a value to be a linked
  list where the elements satisfy a predicate.
*)
Definition is_list (v : val) (Φ : val → iProp Σ) : iProp Σ :=
  ∃ xs, is_list_of v xs ∗ list_all xs Φ.

(*
  This definition works, but is slightly anoying to work with. If we
  could instead define the predicate recursively, without the nesesaty
  for a decresing argument. Just like inductive propositions. Actually
  we can. Iris has unique fixpoints for any contractive function.
  Contractive intuitively means that recursive calls only matter
  "later".

  To do this we use the notation `-d>` to specify that the argument
  does not depend on time. You can use `-n>` to specify that an
  argument does depend on time. However that will add the criteria
  that it's use is non-expansive (time preserving).
*)

Definition is_list_inner (is_list : val -d> (val → iProp Σ) -d> iProp Σ) : val -d> (val → iProp Σ) -d> iProp Σ :=
  λ v Φ, (⌜v = NONEV⌝ ∨ ∃ l : loc, ⌜v = SOMEV #l⌝ ∗ ∃ x t, l ↦ (x, t) ∗ Φ x ∗ ▷ is_list t Φ)%I.

(*
  Iris has a tactic `solve_contractive` that can handle definitions
  comprised of things that are known to be either non-expansive or
  contractive.
*)
Global Instance is_list_inner_contract : Contractive is_list_inner.
Proof. solve_contractive. Qed.

Definition is_list_rec := fixpoint is_list_inner.

Lemma is_list_rec_unfold v Φ : is_list_rec v Φ ≡ is_list_inner is_list_rec v Φ.
Proof. apply (fixpoint_unfold is_list_inner). Qed.

Lemma is_list_rec_correct : is_list_rec ≡ is_list.
Proof.
  intros v Φ.
  iSplit.
  - iIntros "Hv".
    iLöb as "IH" forall (v).
    rewrite is_list_rec_unfold.
    iDestruct "Hv" as "[-> | (%l & -> & %x & %t & Hl & Hx & Ht)]".
    + by iExists [].
    + iSpecialize ("IH" with "Ht").
      iDestruct "IH" as "(%xs & Ht & Hxs)".
      iExists (x :: xs) =>/=.
      iFrame.
      iExists l.
      iSplitR; first done.
      iExists t.
      iFrame.
  - iIntros "(%xs & Hv & Hxs)".
    iInduction xs as [| x xs] "IH" forall (v) =>/=.
    + rewrite is_list_rec_unfold.
      by iLeft.
    + iDestruct "Hv" as "(%l & -> & %t & Hl & Ht)".
      iDestruct "Hxs" as "[Hx Hxs]".
      rewrite is_list_rec_unfold.
      iRight.
      iExists l.
      iSplitR; first done.
      iExists x, t.
      iFrame.
      iApply ("IH" with "Ht Hxs").
Qed.
