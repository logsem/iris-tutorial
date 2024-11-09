From iris.heap_lang Require Import lang proofmode notation.

(* ################################################################# *)
(** * Case Study: Linked Lists *)

Section linked_lists.
Context `{!heapGS Σ}.

(**
  In this chapter, we will study several functions on linked lists. To
  do this, we must first agree on what a linked list is. In HeapLang, we
  can implement linked lists as chains of pointers. We define this
  formally with a predicate, which we denote [isList]. This predicate
  turns a list of values [xs] into a predicate describing the structure
  of the linked list.
*)
Fixpoint isList (l : val) (xs : list val) : iProp Σ :=
  match xs with
  | [] => ⌜l = NONEV⌝
  | x :: xs => ∃ (hd : loc) l', ⌜l = SOMEV (#hd)⌝ ∗ hd ↦ (x, l') ∗ isList l' xs
  end.
(**
  Here, [NONEV] and [SOMEV v] are the value equivalents of [NONE] and
  [SOME e].
*)

(**
  We can now define HeapLang functions that act on lists, such as [inc].
  The [inc] function recursively increments all the values of a list.
*)
Definition inc : val :=
  rec: "inc" "l" :=
    match: "l" with
      NONE => #()
    | SOME "hd" =>
        let: "x" := Fst (! "hd") in
        let: "l'" := Snd (! "hd") in
        "hd" <- ("x" + #1, "l'");;
        "inc" "l'"
    end.

(**
  Intuitively, the specification we give for this function should state
  that the linked list should only contain integers and that, after
  executing the function, each integer has been incremented. As such, we
  parametrise the specification not by a list of values, but by a list
  of integers. We then map each integer to a HeapLang value using [# _],
  allowing us to use the [isList] predicate.
*)
Lemma inc_spec (l : val) (xs : list Z) :
  {{{ isList l ((λ x : Z, #x) <$> xs) }}}
    inc l
  {{{ RET #(); isList l ((λ x, #(x + 1)) <$> xs)}}}.
Proof.
  (**
    The proof proceeds by structural induction in [xs]. As [l] changes in each
    iteration, we must universally quantify over it to strengthen the induction
    hypothesis.
  *)
  revert l.
  induction xs as [|x xs' IH]; simpl.
  - (* Base Case: xs = [] *)
    iIntros (l) "%Φ -> HΦ".
    wp_rec.
    wp_pures.
    by iApply "HΦ".
  - (* Induction step: xs = x :: xs' *)
    (* exercise *)
Admitted.

(**
  The append function recursively descends [l1], updating the links.
  Eventually, it reaches the tail, [NONE], where it will replace it with
  [l2].
*)
Definition append : val :=
  rec: "append" "l1" "l2" :=
    match: "l1" with
      NONE => "l2"
    | SOME "hd" =>
        let: "x" := Fst (!"hd") in
        let: "l1'" := Snd (!"hd") in
        let: "r" := "append" "l1'" "l2" in
        "hd" <- ("x", "r");;
        SOME "hd"
    end.

(**
  If [l1] and [l2] represent the lists [xs] and [ys] respectively, then
  we expect that [append l1 l2] will return a list representing
  [xs ++ ys].
*)
Lemma append_spec (l1 l2 : val) (xs ys : list val) :
  {{{ isList l1 xs ∗ isList l2 ys }}}
    append l1 l2
  {{{ l, RET l; isList l (xs ++ ys) }}}.
Proof.
  revert ys l1 l2.
  induction xs as [| x xs' IH]; simpl.
  (* exercise *)
Admitted.

(**
  We will implement reverse using a helper function called
  [reverse_append], which takes two arguments, [l] and [acc], and
  returns the list [rev l ++ acc].
*)
Definition reverse_append : val :=
  rec: "reverse_append" "l" "acc" :=
    match: "l" with
      NONE => "acc"
    | SOME "hd" =>
        let: "x" := Fst (! "hd") in
        let: "l'" := Snd (! "hd") in
        "hd" <- ("x", "acc");;
        "reverse_append" "l'" "l"
    end.

(**
  When [acc] is the empty list, it should thus simply return the reverse
  of [l].
*)
Definition reverse : val :=
  λ: "l", reverse_append "l" NONE.

Lemma reverse_append_spec (l acc : val) (xs ys : list val) :
  {{{ isList l xs ∗ isList acc ys }}}
    reverse_append l acc
  {{{ v, RET v; isList v (rev xs ++ ys) }}}.
Proof.
  revert l acc ys.
  induction xs as [| x xs' IH]; simpl.
  (* exercise *)
Admitted.

(**
  Now, we use the specification of [reverse_append] to prove the
  specification of [reverse].
*)
Lemma reverse_spec (l : val) (xs : list val) :
  {{{ isList l xs }}}
    reverse l
  {{{ v, RET v; isList v (rev xs) }}}.
Proof.
  (* exercise *)
Admitted.

(**
  The specifications thus far have been rather straightforward. Now we
  will show a very general specification for [fold_right].
*)
Definition fold_right : val :=
  rec: "fold_right" "f" "v" "l" :=
    match: "l" with
      NONE => "v"
    | SOME "hd" =>
        let: "x" := Fst (! "hd") in
        let: "l'" := Snd (! "hd") in
        "f" "x" ("fold_right" "f" "v" "l'")
    end.

(**
  The following specification has a lot of moving parts, so let us go
  through them one by one.
  - [l] is a linked list representing [xs], as seen by [isList l xs] in
    the precondition.
  - [P] is a predicate which all the values in [xs] should satisfy. This
    is written as [[∗ list] x ∈ xs, P x]. It is a recursively defined
    predicate, defined as follows:
      [[∗ list] x ∈ [], P x := True]
      [[∗ list] x ∈ x0 :: xs, P x := P x0 ∗ [∗ list] x ∈ xs, P x]
  - [I] is a predicate (think [I] for invariant) describing the relation
    between a list and the result of the fold.
  - [a] is the base value, so fold will return [a] for the empty list;
    this is captured by [I [] a].
  - [f] is the folding function, which we assume satisfies:
      [{{{ P x ∗ I ys a' }}} f x a' {{{ r, RET; I (x :: ys) r }}}].
    Intuitively, this says that if [f] is applied to an argument from
    the list (hence satisfying [P]) and [a'] is the result of folding
    [ys], captured by [I ys a'], then the result [r] will be the result
    of folding f over [x :: ys], captured by [I (x :: ys) r] in the
    postcondition.
  - The result [r] of folding must then satisfy [I xs r].
  - Importantly, we do not change the original list. So we put
    [isList l xs] in the postcondition.

  Note that Hoare triples are persistent, and persistent predicates are
  closed under universal quantification. Hence, in the proof, the
  assumption for [f] will move into the persistent context.
*)
Lemma fold_right_spec P I (f a l : val) xs :
  {{{
    isList l xs ∗ ([∗ list] x ∈ xs, P x) ∗ I [] a ∗
    (∀ (x a' : val) ys,
      {{{ P x ∗ I ys a' }}} f x a' {{{ r, RET r; I (x :: ys) r }}})
  }}}
    fold_right f a l
  {{{ r, RET r; isList l xs ∗ I xs r}}}.
Proof.
  revert a l.
  induction xs as [|x xs IHxs].
  all: simpl.
  (* exercise *)
Admitted.

(**
  We can now sum over a list simply by folding an addition function over
  it.
*)

Definition sum_list : val :=
  λ: "l",
    let: "f" := (λ: "x" "y", "x" + "y") in
    fold_right "f" #0 "l".

Lemma sum_list_spec l xs :
  {{{isList l ((λ x : Z, #x) <$> xs)}}}
    sum_list l
  {{{RET #(foldr Z.add 0 xs); isList l ((λ x : Z, #x) <$> xs)}}}.
Proof.
  iIntros (Φ) "Hl HΦ".
  wp_rec; wp_pures.
  wp_apply (fold_right_spec
    (λ x, ∃ i : Z, ⌜x = #i⌝)%I
    (λ xs y, ∃ ys, ⌜xs = (λ x : Z, #x) <$> ys⌝ ∗ ⌜y = #(foldr Z.add 0 ys)⌝)%I
    with "[Hl]"
  ).
  - iFrame.
    repeat iSplit.
    + iPureIntro; simpl.
      intros k v Hk.
      rewrite list_lookup_fmap in Hk.
      destruct (xs !! k) as [x|]; last done.
      injection Hk as <-.
      by exists x.
    + by iExists [].
    + clear.
      iIntros (x a' ys Φ) "!> [[%i ->] (%xs & -> & ->)] HΦ".
      wp_pures.
      iModIntro.
      iApply "HΦ".
      by iExists (i :: xs).
  - iIntros "%_ (Hl & %ys & %H & ->)".
    assert (Hinj:Inj eq eq (λ x : Z, #x)) by congruence.
    apply (inj _) in H.
    subst ys.
    by iApply "HΦ".
Qed.

End linked_lists.
