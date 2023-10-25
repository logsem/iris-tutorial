From iris.heap_lang Require Import lang proofmode notation.

Section linked_lists.
Context `{!heapGS Σ}.

(**
  Let us define what we mean by a linked list in HeapLang. We will do
  so by relating a program value to the Coq list it represents.

  Here we use [NONE] and [SOME e] as syntactic sugar for [InjL #()]
  and [InjR e]. Furthermore, [NONE] is the expression creating a
  [NONEV] value, likewise for [SOMEV], [InjLV] and [InjRV].
*)
Fixpoint isList (l : val) (xs : list val) : iProp Σ :=
  match xs with
  | [] => ⌜l = NONEV⌝
  | x :: xs => ∃ (hd : loc) l', ⌜l = SOMEV #hd⌝ ∗ hd ↦ (x, l') ∗ isList l' xs
  end.

(**
  Now we can define HeapLang functions that act on lists, such as
  inc. The inc function recursively increments all the values of a
  list by 1.
*)
Definition inc : val :=
  rec: "inc" "l" :=
    match: "l" with
      NONE => #()
    | SOME "p" =>
        let: "h" := Fst (! "p") in
        let: "t" := Snd (! "p") in
        "p" <- ("h" + #1, "t");;
        "inc" "t"
    end.

(**
  Here we want the input list to be a list of integers. To capture
  this we take a list of integers and map the elements to values using
  [# _]. When the function is done, we expect all the elements in the
  list to have been incremented. So we again use a map to express
  this.
*)
Lemma inc_spec (l : val) (xs : list Z) :
  {{{isList l ((λ x : Z, #x) <$> xs)}}}
    inc l
  {{{ RET #(); isList l ((λ x, #(x + 1)%Z) <$> xs)}}}.
Proof.
  (*
    To prove this we'll use structural induction on the list. However,
    the list we will be looking at will change with each iteration.
  *)
  revert l.
  induction xs.
  all: simpl.
  (* exercise *)
Admitted.

(**
  The append function recursively descends l1, updating the links.
  Eventually, it reaches the tail, where it will replace it with l2.
*)
Definition append : val :=
  rec: "append" "l1" "l2" :=
    match: "l1" with
      NONE => "l2"
    | SOME "p" =>
        let: "h" := Fst (! "p") in
        let: "t" := Snd (! "p") in
        "p" <- ("h", "append" "t" "l2");;
        SOME "p"
    end.

(**
  If l1 and l2 represent the lists xs and ys respectively, then we expect
  that append l1 l2 will return a list representing [xs ++ ys].
*)
Lemma append_spec (l1 l2 : val) (xs ys : list val) :
  {{{isList l1 xs ∗ isList l2 ys}}}
    append l1 l2
  {{{l, RET l; isList l (xs ++ ys)}}}.
Proof.
  revert ys l1 l2.
  induction xs.
  all: simpl.
  (* Exercise start *)
  - iIntros (ys l1 l2) "%Φ [-> H2] HΦ".
    wp_rec.
    wp_pures.
    by iApply "HΦ".
  - iIntros (ys l1 l2) "%Φ [(%hd & %l' & -> & Hhd & H1) H2] HΦ".
    wp_rec.
    wp_pures.
    wp_load.
    wp_load.
    wp_pures.
    wp_apply (IHxs with "[$H1 $H2]").
    iIntros "%l Hl".
    wp_store.
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iExists hd, l.
    by iFrame.
Qed.

(**
  We will implement reverse using a helper function, called reverse_append,
  which takes two arguments, [l] and [acc], and returns the list
  [rev l ++ acc].
*)
Definition reverse_append : val :=
  rec: "reverse_append" "l" "acc" :=
    match: "l" with
      NONE => "acc"
    | SOME "p" =>
        let: "h" := Fst (! "p") in
        let: "t" := Snd (! "p") in
        "p" <- ("h", "acc");;
        "reverse_append" "t" "l"
    end.

(**
  When acc is the empty list, it should thus simply return the reverse
  of [l].
*)
Definition reverse : val :=
  rec: "reverse" "l" := reverse_append "l" NONE.

Lemma reverse_append_spec (l acc : val) (xs ys : list val) :
  {{{isList l xs ∗ isList acc ys}}}
    reverse_append l acc
  {{{v, RET v; isList v (rev xs ++ ys)}}}.
Proof.
  revert l acc ys.
  induction xs.
  all: simpl.
  (* exercise *)
Admitted.

(**
  Now we use the specification of reverse_append to prove the specification
  of reverse.
*)
Lemma reverse_spec (l : val) (xs : list val) :
  {{{isList l xs}}}
    reverse l
  {{{v, RET v; isList v (rev xs)}}}.
Proof.
  (* exercise *)
Admitted.

(**
  The specifications thus far have been rather straightforward. 
  Now we will show a very general specification for [fold_right].
*)
Definition fold_right : val :=
  rec: "fold_right" "f" "v" "l" :=
    match: "l" with
      NONE => "v"
    | SOME "p" =>
        let: "h" := Fst (! "p") in
        let: "t" := Snd (! "p") in
        "f" "h" ("fold_right" "f" "v" "t")
    end.

(**
  The following specification has a lot of moving parts, so let's go
  through them one by one.
  - [l] is a linked list representing [xs], as seen by [isList l xs]
    in the precondition.
  - [P] is a predicate which all the values in xs should satisfy.
    This is written as [[∗ list] x ∈ xs, P x]. It is a recursively
    defined predicate, defined as follows:
      [[∗ list] x ∈ [], P x := True]
      [[∗ list] x ∈ x0 :: xs, P x := P x0 ∗ [∗ list] x ∈ xs, P x]
  - [I] is a predicate (think [I] for invariant) describing the 
    relation between a list and the result of the fold.
  - [a] is the base value, so fold will return a for the empty list;
    this is captured by [I [] a].
  - [f] is the folding function, which we assume satisfies:
      [{{{ P x ∗ I ys a'}}} f x a' {{{ r, RET; I (x :: ys) r }}}].
    Intuitively, this says that if [f] is applied to an argument from the
    list (hence satisfying [P]) and [a'] is the result of folding [ys],
    captured by [I ys a'], then the result [r] will be the result of
    folding f over [x :: ys], captured by [I (x :: ys) r] in the postcondition.
  - The result [r] must then satisfy [I xs r].
  - Importantly, we don't change the original list. So we put
    [isList l xs] in the postcondition.

  Note that Hoare triples are persistent and persistent predicates are
  closed under universal quantification, so, in the proof, the assumption for
  [f] will move into the persistent context!
*)
Lemma fold_right_spec P I (f a l : val) xs :
  {{{
    isList l xs ∗ ([∗ list] x ∈ xs, P x) ∗ I [] a ∗
    (∀ (x a' : val) ys, {{{ P x ∗ I ys a' }}} f x a' {{{ r, RET r; I (x :: ys) r }}})
  }}}
    fold_right f a l
  {{{ r, RET r; isList l xs ∗ I xs r}}}.
Proof.
  revert a l.
  induction xs as [|x xs IHxs].
  all: simpl.
  (* exercise *)
Admitted.

(** We can now sum over a list simply by folding an addition function over it. *)
Definition sum_list : val :=
  λ: "l",
    let: "f" := (λ: "x" "y", "x" + "y") in
    fold_right "f" #0 "l".

Lemma sum_list_spec l xs :
  {{{isList l ((λ x : Z, #x) <$> xs)}}}
    sum_list l
  {{{RET #(foldr Z.add 0%Z xs); isList l ((λ x : Z, #x) <$> xs)}}}.
Proof.
  iIntros (Φ) "Hl HΦ".
  wp_rec; wp_pures.
  wp_apply (fold_right_spec
    (λ x, ∃ i : Z, ⌜x = #i⌝)%I
    (λ xs y, ∃ ys, ⌜xs = (λ x : Z, #x) <$> ys⌝ ∗ ⌜y = #(foldr Z.add 0%Z ys)⌝)%I
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
