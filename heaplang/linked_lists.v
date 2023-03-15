From iris.heap_lang Require Import lang proofmode notation.

Section linked_lists.
Context `{!heapGS Σ}.

(*
  Let's define what we mean by a linked list in heaplang.
  We'll do this by relating a value to a list of values in coq.
*)
Fixpoint isList (l : val) (xs : list val) : iProp Σ :=
  match xs with
  | [] => ⌜l = NONEV⌝
  | x :: xs => ∃ (hd : loc) l', ⌜l = SOMEV #hd⌝ ∗ hd ↦ (x, l') ∗ isList l' xs
  end.

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

Lemma wp_append (l1 l2 : val) (xs ys : list val) : {{{isList l1 xs ∗ isList l2 ys}}} append l1 l2 {{{l, RET l; isList l (xs ++ ys)}}}.
Proof.
  iLöb as "IH" forall (l1 xs).
  destruct xs as [|x xs] =>/=.
  - iIntros (Φ) "[-> H2] HΦ".
    wp_rec.
    wp_pures.
    iModIntro.
    by iApply "HΦ".
  - iIntros (Φ) "[(%hd & %l1' & -> & Hhd & H1) H2] HΦ".
    wp_rec.
    wp_pures.
    wp_load.
    wp_pures.
    wp_load.
    wp_pures.
    wp_bind (append l1' l2).
    iApply ("IH" with "[H1 H2]"); first iFrame.
    iIntros "!> %l Hl".
    wp_store.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iExists hd, l.
    by iFrame.
Qed.

(*
  Let's define a program that increments all the values of a list.
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

Lemma wp_inc (l : val) (xs : list Z) : {{{isList l ((λ x : Z, #x) <$> xs)}}} inc l {{{ RET #(); isList l ((λ x, #(x + 1)%Z) <$> xs)}}}.
Proof.
  iLöb as "IH" forall (l xs).
  destruct xs as [|x xs] =>/=.
  - iIntros (Φ) "-> HΦ".
    wp_rec.
    wp_pures.
    by iApply "HΦ".
  - iIntros (Φ) "(%hd & %l' & -> & Hhd & Hl) HΦ".
    wp_rec.
    wp_pures.
    wp_load.
    wp_pures.
    wp_load.
    wp_pures.
    wp_store.
    iApply ("IH" with "Hl").
    iIntros "!> Hl".
    iApply "HΦ".
    iExists hd, l'.
    by iFrame.
Qed.

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

Definition reverse : val :=
  rec: "reverse" "l" := reverse_append "l" NONE.

Lemma wp_reverse_append (l acc : val) (xs ys : list val) : {{{isList l xs ∗ isList acc ys}}} reverse_append l acc {{{v, RET v; isList v (rev xs ++ ys)}}}.
Proof.
  iLöb as "IH" forall (l acc xs ys).
  destruct xs as [|x xs] =>/=.
  - iIntros (Φ) "[-> Hacc] HΦ".
    wp_rec.
    wp_pures.
    by iApply "HΦ".
  - iIntros (Φ) "[(%hd & %l' & -> & Hhd & Hl) Hacc] HΦ".
    wp_rec.
    wp_pures.
    wp_load.
    wp_pures.
    wp_load.
    wp_pures.
    wp_store.
    rewrite -app_assoc /=.
    iApply ("IH" with "[Hl Hhd Hacc] HΦ").
    iFrame =>/=.
    iExists hd, acc.
    by iFrame.
Qed.

Lemma wp_reverse (l : val) (xs : list val) : {{{isList l xs}}} reverse l {{{v, RET v; isList v (rev xs)}}}.
Proof.
  iIntros (Φ) "Hl HΦ".
  wp_rec; wp_pures.
  rewrite -(app_nil_r (rev xs)).
  iApply (wp_reverse_append with "[Hl] HΦ").
  by iFrame.
Qed.

Definition fold_right : val :=
  rec: "fold_right" "f" "v" "l" :=
    match: "l" with
      NONE => "v"
    | SOME "p" =>
        let: "h" := Fst (! "p") in
        let: "t" := Snd (! "p") in
        "f" "h" ("fold_right" "f" "v" "t")
    end.

Lemma wp_fold_right P I (f a l : val) xs :
  {{{
    isList l xs ∗ ([∗ list] x ∈ xs, P x) ∗ I [] a ∗
    (∀ (x a' : val) ys, {{{ P x ∗ I ys a' }}} f x a' {{{ r, RET r; I (x :: ys) r }}})
  }}}
    fold_right f a l
  {{{ r, RET r; isList l xs ∗ I xs r}}}.
Proof.
  iLöb as "IH" forall (a l xs).
  destruct xs as [|x xs] =>/=.
  - iIntros (Φ) "(-> & _ & Hi & _) HΦ".
    wp_rec.
    wp_pures.
    iApply "HΦ".
    by iFrame.
  - iIntros (Φ) "((%hd & %l' & -> & Hhd & Hl) & [Hx Hxs] & HI & #Hf) HΦ".
    wp_rec.
    wp_pures.
    wp_load.
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply ("IH" with "[Hl Hxs HI]").
    { by iFrame. }
    iIntros (r) "[Hl HI]".
    wp_apply ("Hf" with "[Hx HI]").
    { by iFrame. }
    iIntros (r') "HI".
    iApply "HΦ".
    iFrame.
    iExists hd, l'.
    by iFrame.
Qed.

Definition sum_list : val :=
  λ: "l",
    let: "f" := (λ: "x" "y", "x" + "y") in
    fold_right "f" #0 "l".

Lemma wp_sum_list l xs : {{{isList l ((λ x : Z, #x) <$> xs)}}} sum_list l {{{RET #(foldr Z.add 0%Z xs); isList l ((λ x : Z, #x) <$> xs)}}}.
Proof.
  iIntros (Φ) "Hl HΦ".
  wp_rec; wp_pures.
  wp_apply (wp_fold_right
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
      iIntros (x a' ys Φ) "!# [[%i ->] (%xs & -> & ->)] HΦ".
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
