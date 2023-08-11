From iris.heap_lang Require Import lang proofmode notation.

Section linked_lists.
Context `{!heapGS Σ}.

(**
  Let's define what we mean by a linked list in heaplang. We'll do
  this by relating a value to the list it represents.
*)
Fixpoint isList (l : val) (xs : list val) : iProp Σ :=
  match xs with
  | [] => ⌜l = NONEV⌝
  | x :: xs => ∃ (hd : loc) l', ⌜l = SOMEV #hd⌝ ∗ hd ↦ (x, l') ∗ isList l' xs
  end.

(**
  Now we can define heaplang functions that act on lists, such as
  append. This function recursively decents l1, updating the links.
  Eventually it reaches the tail, where it will replace it with l2.
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
  If l1 and l2 represents the lists xs and ys respectively, we expect
  that append will return a list representing [xs ++ ys].
*)
Lemma append_spec (l1 l2 : val) (xs ys : list val) :
  {{{isList l1 xs ∗ isList l2 ys}}}
    append l1 l2
  {{{l, RET l; isList l (xs ++ ys)}}}.
Proof.
  induction xs in ys, l1, l2 |- * =>/=.
  (* Exercise start *)
  - iIntros "%Φ [-> H2] HΦ".
    wp_rec.
    wp_pures.
    by iApply "HΦ".
  - iIntros "%Φ [(%hd & %l' & -> & Hhd & H1) H2] HΦ".
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
  Now let's define a program that increments all the values of a list.
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
  Here we want the list to be a list of integers. To do this we take a
  list of integers and map the elements to values using [# _]. When
  the function is done, we expect all the elements in the list to have
  incremented. So we again use a map to incode this.
*)
Lemma inc_spec (l : val) (xs : list Z) :
  {{{isList l ((λ x : Z, #x) <$> xs)}}}
    inc l
  {{{ RET #(); isList l ((λ x, #(x + 1)%Z) <$> xs)}}}.
Proof.
  induction xs in l |- * =>/=.
  (* Exercise start *)
  - iIntros "%Φ -> HΦ".
    wp_rec.
    wp_pures.
    by iApply "HΦ".
  - iIntros "%Φ (%hd & %l' & -> & Hhd & Hl) HΦ".
    wp_rec.
    wp_pures.
    wp_load.
    wp_load.
    wp_pures.
    wp_store.
    wp_apply (IHxs with "Hl").
    iIntros "Hl".
    iApply "HΦ".
    iExists hd, l'.
    by iFrame.
Qed.

(**
  We will implement reverse using a helper function. This function
  takes two arguments, [l] and [acc], and returns the list
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
  induction xs in l, acc, ys |- * =>/=.
  (* Exercise start *)
  - iIntros "%Φ [-> Hacc] HΦ".
    wp_rec.
    wp_pures.
    by iApply "HΦ".
  - iIntros "%Φ [(%hd & %l' & -> & Hhd & Hl) Hacc] HΦ".
    wp_rec.
    wp_pures.
    wp_load.
    wp_load.
    wp_store.
    wp_apply (IHxs _ _ (a :: ys) with "[$Hl Hhd Hacc]").
    {
      cbn.
      iExists hd, acc.
      by iFrame.
    }
    by rewrite -app_assoc.
Qed.

(**
  Use the specification of reverse_append to prove the specification
  of reverse.
*)
Lemma reverse_spec (l : val) (xs : list val) :
  {{{isList l xs}}}
    reverse l
  {{{v, RET v; isList v (rev xs)}}}.
Proof.
  (* Exercise start *)
  iIntros "%Φ Hl HΦ".
  wp_lam.
  wp_pures.
  wp_apply (reverse_append_spec _ _ _ [] with "[$Hl]").
  { done. }
  by rewrite app_nil_r.
Qed.

(**
  The specifications thus far have been rather straight forward. So
  now we will show a very general specification for [fold_right].
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
  The following specification has a lot of moving parts, so lets go
  through them one by one.
  - [l] is a linked list implementing [xs], as seen by [isList l xs]
    in the precondition.
  - [P] is a predicate that all the values in xs should satisfy.
    This is written as [[∗ list] x ∈ xs, P x]. This is a recursively
    defined predicate, defined as follows:
    [[∗ list] x ∈ [], P x := True]
    [[∗ list] x ∈ x0 :: xs, P x := P x0 ∗ [∗ list] x ∈ xs, P x]
  - [I] is a predicate describing the relation between a list
    and the result of the fold.
  - [a] is the initial value, so the empty list should produce it.
    This is captured by [I [] a].
  - [f] is the folding function. So it satisfies:
    [{{{ P x ∗ I ys a'}}} f x a' {{{ r, RET; I (x :: ys) r }}}].
  - The result [r] must then satisfy [I xs r].
  - Importantly, we don't change the original list. So we put
    [isList l xs] in the post condition.
*)
Lemma fold_right_spec P I (f a l : val) xs :
  {{{
    isList l xs ∗ ([∗ list] x ∈ xs, P x) ∗ I [] a ∗
    (∀ (x a' : val) ys, {{{ P x ∗ I ys a' }}} f x a' {{{ r, RET r; I (x :: ys) r }}})
  }}}
    fold_right f a l
  {{{ r, RET r; isList l xs ∗ I xs r}}}.
Proof.
  induction xs in a, l |- * =>/=.
  (* Exercise start *)
  - iIntros "%Φ (-> & _ & I & #Hf) HΦ".
    wp_rec.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    by iFrame.
  - iIntros "%Φ ((%hd & %l' & -> & Hhd & Hl) & [P0 Ps] & I & #Hf) HΦ".
    wp_rec.
    wp_pures.
    wp_load.
    wp_load.
    wp_pures.
    wp_apply (IHxs with "[$Hl $Ps $I $Hf]").
    iIntros "%r [Hl I]".
    wp_apply ("Hf" with "[$P0 $I]").
    iIntros "%r' I".
    iApply "HΦ".
    iFrame.
    iExists hd, l'.
    by iFrame.
Qed.

(** We can now sum over a list simply by folding it using addition. *)
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
    + iPureIntro =>/= k v Hk.
      rewrite list_lookup_fmap in Hk.
      destruct (xs !! k) as [x|] =>//.
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
    apply fmap_inj in H.
    + subst ys.
      by iApply "HΦ".
    + intros x1 x2 Hx.
      by injection Hx.
Qed.

End linked_lists.
