From iris.bi Require Export fixpoint.
From iris.heap_lang Require Import lang proofmode notation.

(**
  In this file we present an alternative approach to defining representation
  predicates for linked lists, which uses fixpoints of predicates rather than
  Coq's Fixpoint mechanism. 
  The high-level point to notice is that we can define fixpoints of monotone 
  functions on Iris predicates, much in the same way as one can define fixpoints
  of monotone function on Coq predicates [XXX insert reference, or include an
  example.]
  Later on, we will discuss different kinds of fixpoints in more detail.
 *)

Section proofs.
Context `{!heapGS Σ}.

(**
  As we have already seen, we can define a predicate for linked lists
  representing a list of specific values, using Coq's notion of
  fixpoint for the inductive Coq type [list val].
*)
Fixpoint is_list_of (v : val) (xs : list val) : iProp Σ :=
  match xs with
  | [] => ⌜v = NONEV⌝
  | x :: xs => ∃ l : loc, ⌜v = SOMEV #l⌝ ∗ ∃ t, l ↦ (x, t) ∗ is_list_of t xs
  end.

(**
  However, sometimes we don't care about the exact list and instead
  we only want to know that each value of the list satisfies a predicate.
  This can be captures by using a helper predicate [all] expressing that
  all elements of a Coq list satisfies a predicate. 
  Using that, we can then simply state that the value is represented by one such
  list.
*)

Fixpoint all (xs : list val) (Φ : val → iProp Σ) : iProp Σ :=
  match xs with
  | [] => True
  | x :: xs => Φ x ∗ all xs Φ
  end.

Definition is_list (v : val) (Φ : val → iProp Σ) : iProp Σ :=
  ∃ xs, is_list_of v xs ∗ all xs Φ.

(**
  However, this definition is rather annoying to work with, as it
  requires explicitly finding the list of values. Alternatively, we
  can define the is_list redicate as the solution to a recursive
  definition. This means defining a function:
    [F : (A → iProp Σ) → (A → iProp Σ)]
  A solution is then a function [f] satisfying [f = F f]. Solutions to
  such equations are called fixpoints as [f] doesn't change under [F].
*)
Definition is_list_pre (Φ : val → iProp Σ) (f : val → iProp Σ) (v : val) : iProp Σ :=
  ⌜v = NONEV⌝ ∨ ∃ l : loc, ⌜v = SOMEV #l⌝ ∗ ∃ x t, l ↦ (x, t) ∗ Φ x ∗ f t.

(**
  Recursive definitions can have multiple fixpoints. Of these there
  are two special fixpoints: The least fixpoint and the greatest fixpoint.
  The least fixpoint corresponds to an inductively defined predicate,
  while the greatest corresponds to a coinductively defined predicates.

  These solutions exists when [F] is monotone, as captured by the
  typeclass [BiMonoPred].
*)
Global Instance is_list_pre_mono Φ : BiMonoPred (is_list_pre Φ).
Proof.
  split.
  - intros Ψ1 Ψ2 H1 H2.
    iIntros "#HΨ %v [->|(%l & -> & %x & %t & Hl & Hx & Ht)]".
    + by iLeft.
    + iRight.
      iExists l.
      iSplitR; first done.
      iExists x, t.
      iFrame.
      iApply ("HΨ" with "Ht").
  - (**
      In addition to monotonicity, we also need to prove that the
      resulting predicate is 'time preserving' (NonExpansive).
      (We will explain NonExpansiveness etc. in more detail later.)
      This is trivial in this case as values are discrete.
    *)
    apply _.
Qed.

(** 
  Now that we have proved monotonicity, we can obtain the least fixed point,
  and lemmas for its unfolding and for induction.
*)

Definition is_list_rec (v : val) (Φ : val → iProp Σ) := bi_least_fixpoint (is_list_pre Φ) v.

Lemma is_list_rec_unfold (v : val) (Φ : val → iProp Σ) : is_list_rec v Φ ⊣⊢ is_list_pre Φ (λ v, is_list_rec v Φ) v.
Proof. apply least_fixpoint_unfold, _. Qed.

Lemma is_list_rec_ind (Φ Ψ : val → iProp Σ) : □ (∀ v, is_list_pre Φ Ψ v -∗ Ψ v ) -∗ ∀ v, is_list_rec v Φ -∗ Ψ v.
Proof. apply least_fixpoint_iter, _. Qed.

(** 
  We can now prove that our new definition is_list_rec obtained as the fixpoint
  is equivalent to the definition we gave earlier.
*)
Lemma is_list_rec_correct (v : val) (Φ : val → iProp Σ) : is_list v Φ ⊣⊢ is_list_rec v Φ.
Proof.
  iSplit.
  - iIntros "(%xs & Hv & HΦs)".
    iInduction xs as [|x xs] "IH" forall (v); simpl.
    + rewrite is_list_rec_unfold.
      by iLeft.
    + rewrite is_list_rec_unfold.
      iRight.
      iDestruct "Hv" as "(%l & -> & %t & Hl & Ht)".
      iDestruct "HΦs" as "[HΦ HΦs]".
      iExists l.
      iSplitR; first done.
      iExists x, t.
      iFrame.
      iApply ("IH" with "Ht HΦs").
  - iRevert (v).
    iApply is_list_rec_ind.
    iIntros "!> %v [->|(%l & -> & %x & %t & Hl & HΦ & %xs & Ht & Hxs)]".
    + by iExists [].
    + iExists (x :: xs); cbn.
      iFrame.
      iExists l.
      iSplitR; first done.
      iExists t.
      iFrame.
Qed.

End proofs.
