From iris.heap_lang Require Import lang proofmode notation.

Section linked_lists.
Context `{!heapGS Σ}.

(**
  Let us define what we mean by a linked list in Heaplang. We will do
  so by relating a program value to the Coq list it represents.

  Here we use [NONE] and [SOME e] as syntactic sugar for [InjL #()]
  and [InjR e]. Further more, [NONE] is the expresion creating a
  [NONEV] value, likewise for [SOMEV], [InjLV] and [InjRV].
*)
Fixpoint isList (l : val) (xs : list val) : iProp Σ :=
  match xs with
  | [] => ⌜l = NONEV⌝
  | x :: xs => ∃ (hd : loc) l', ⌜l = SOMEV #hd⌝ ∗ hd ↦ (x, l') ∗ isList l' xs
  end.

(**
  Now we can define Heaplang functions that act on lists, such as
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
(* BEGIN SOLUTION *)
  - iIntros (l) "%Φ -> HΦ".
    wp_rec.
    wp_pures.
    by iApply "HΦ".
  - iIntros (l) "%Φ (%hd & %l' & -> & Hhd & Hl) HΦ".
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
(* END SOLUTION BEGIN TEMPLATE
  (* exercise *)
Admitted.
END TEMPLATE *)

(**
  The append function recursively descends l1, updating the links.
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
  (**XXX Lars: need some explanation of the above line, the last 4-5 symbols *)
  (**XXX Mathias: Seperated it for clarity. *)

  (**XXX Lars: also need to explain NONEV and SOMEV shown as InjLV and InjRV, 
    when stepping through proof *)
  (**XXX Mathias: Added a rough description at the begining of the file *)
  (* Exercise start *)

  (**XXX I think this is too hard as a first exercise with lists, maybe just
    keep the proof and then use the next examples as exercises. *)
  (**XXX Mathias: Moved inc up, and adjusted the comments*)
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
(* BEGIN SOLUTION *)
  - iIntros (l acc ys) "%Φ [-> Hacc] HΦ".
    wp_rec.
    wp_pures.
    by iApply "HΦ".
  - iIntros (l acc ys) "%Φ [(%hd & %l' & -> & Hhd & Hl) Hacc] HΦ".
    wp_rec.
    wp_pures.
    wp_load.
    wp_load.
    wp_store.
    wp_apply (IHxs _ _ (a :: ys) with "[Hl Hhd Hacc]").
    (**XXX Lars: not sure you have explained why the $ is used on Hl and not
      on the others *)
    (**XXX Mathias: Changed it to frame afterwards *)
    {
      iFrame.
      cbn.
      iExists hd, acc.
      by iFrame.
    }
    by rewrite -app_assoc.
Qed.
(* END SOLUTION BEGIN TEMPLATE
  (* exercise *)
Admitted.
END TEMPLATE *)

(**
  Use the specification of reverse_append to prove the specification
  of reverse.
*)
Lemma reverse_spec (l : val) (xs : list val) :
  {{{isList l xs}}}
    reverse l
  {{{v, RET v; isList v (rev xs)}}}.
(* SOLUTION *) Proof.
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
  revert a l.
  induction xs as [|x xs IHxs].
  all: simpl.
(* BEGIN SOLUTION *)
  - iIntros (a l) "%Φ (-> & _ & I & #Hf) HΦ".
    wp_rec.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    by iFrame.
  - iIntros (a l) "%Φ ((%hd & %l' & -> & Hhd & Hl) & [P0 Ps] & I & #Hf) HΦ".
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
(* END SOLUTION BEGIN TEMPLATE
  (* exercise *)
Admitted.
END TEMPLATE *)

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
