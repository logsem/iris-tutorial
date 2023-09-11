From iris.heap_lang Require Import lang proofmode notation par.

Section proofs.
Context `{heapGS Σ, !spawnG Σ}.

(*
  The mapsto predicate l ↦ v has a feature we haven't looked at yet.
  Its full syntax is l ↦{dq} v. dq has type dfrac which is a camera
  with 2 pieces: DfracOwn and DfracDiscarded. For now we'll focus on
  the first. Instead of writing l ↦{DfracOwn q} v, we can write
  l ↦{#q} v. q has type Qp of strictly positive rational numbers.

  These fractions add together, meaning
  `l ↦{#p + q} v ⊣⊢ l ↦{#p} v ∗ l ↦{#q} v`
  with the validity constraint that the fractions add to at most 1.
  These fractions thus allow us to share pointer access without using
  invariants. As we don't need exclusive access to a location to read
  from it, we can use any dq for loads. However for stores we need
  exclusivity so that we can't invalidate other knowledge. Meaning we
  need l ↦{#1} v or simply l ↦ v.
*)

(*
  Using this we can easily prove a specification like the following
*)
Lemma prog1_spec :
  {{{True}}}
    let: "l" := ref #5 in
    (!"l" ||| !"l")
  {{{RET (#5, #5); True}}}.
Proof.
  iIntros "%Φ _ HΦ".
  (*
    Instead of writing an invariant, we simply split the mapsto into 2
    pieces.
  *)
  wp_alloc l as "[H1 H2]".
  wp_pures.
  wp_apply (par_spec (λ v, ⌜v = #5⌝)%I (λ v, ⌜v = #5⌝)%I with "[H1] [H2]").
  - wp_pures.
    by wp_load.
  - wp_pures.
    by wp_load.
  - iIntros (? ?) "[-> ->]".
    by iApply "HΦ".
Qed.

(*
  We can even regain the full mapsto afterwards, which would require
  a cancelable invariant otherwise.
*)
Lemma prog2_spec l :
  {{{l ↦ #5}}}
    (!#l ||| !#l)
  {{{RET (#5, #5); l ↦ #5}}}.
Proof.
  iIntros "%Φ [H1 H2] HΦ".
  wp_pures.
  wp_apply (par_spec (λ v, ⌜v = #5⌝ ∗ l ↦{#1/2} #5)%I (λ v, ⌜v = #5⌝ ∗ l ↦{#1/2} #5)%I with "[H1] [H2]").
  - wp_pures.
    wp_load.
    by iFrame.
  - wp_pures.
    wp_load.
    by iFrame.
  - iIntros (? ?) "[[-> H1] [-> H2]]".
    iCombine "H1 H2" as "H".
    by iApply "HΦ".
Qed.

Fixpoint is_list dq l vs : iProp Σ :=
  match vs with
  | [] => ⌜l = NONEV⌝
  | v :: vs => ∃ (p : loc) l', ⌜l = SOMEV #p⌝ ∗ p ↦{dq} (v, l') ∗ is_list dq l' vs
  end.

Definition copy : val :=
  rec: "copy" "l" :=
    match: "l" with
      NONE => NONE
    | SOME "p" =>
        let: "h" := Fst (! "p") in
        let: "t" := Snd (! "p") in
        SOME (ref ("h", "copy" "t"))
    end.

Lemma copy_spec dq l vs : {{{is_list dq l vs}}} copy l {{{l', RET l'; is_list dq l vs ∗ is_list (DfracOwn 1) l' vs}}}.
Proof.
  iIntros "%Φ Hl HΦ".
  iLöb as "IH" forall (l vs Φ).
  destruct vs as [|v vs]; simpl.
  - iDestruct "Hl" as "->".
    wp_rec.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    done.
  - iDestruct "Hl" as "(%p & %l' & -> & Hp & Hl')".
    wp_rec.
    wp_pures.
    wp_load.
    wp_load.
    wp_pures.
    wp_apply ("IH" with "Hl'").
    iIntros "%t [Hl' Ht]".
    wp_alloc p' as "Hp'".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iSplitL "Hp Hl'".
    + iExists p, l'.
      by iFrame.
    + iExists p', t.
      by iFrame.
Qed.

Global Instance is_list_persistent l vs : Persistent (is_list DfracDiscarded l vs).
Proof.
  induction vs in l |- *.
  all: apply _.
Qed.

End proofs.
