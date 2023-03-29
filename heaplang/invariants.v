From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.

Definition myrec : val :=
  λ: "f",
  let: "r" := ref (λ: "x", "x") in
  "r" <- (λ: "x", "f" (! "r") "x");;
  !"r".

Definition F : val :=
  λ: "f" "x",
  if: "x" = #0 then
    #1
  else
    "x" * "f" ("x" - #1).

Definition fac := myrec F.

Section proofs.
Context `{!heapGS Σ}.

Lemma fac2 : {{{ True }}} fac #2 {{{ RET #2; True }}}.
Proof.
  iIntros "%Φ _ HΦ".
  wp_lam; wp_pures.
  wp_alloc r as "Hr".
  wp_pures.
  wp_store.
  wp_load.
  wp_pures.
  wp_load.
  wp_lam.
  wp_pures.
  wp_load.
  wp_lam.
  wp_pures.
  wp_load.
  wp_lam.
  wp_pures.
  by iApply "HΦ".
Qed.

Let N := nroot .@ "myrec".

Lemma myrec_spec (f v : val) P Q :
  (∀ g v : val, {{{ (∀ v : val, {{{ P v }}} g v {{{ u, RET u; Q v u}}}) ∗ P v }}} f g v {{{ u, RET u; Q v u }}}) -∗
  {{{ P v }}} myrec f v {{{ u, RET u; Q v u }}}.
Proof.
  iIntros "#H %Φ !> HP HΦ".
  wp_lam.
  wp_alloc r as "Hr".
  wp_pures.
  wp_store.
  wp_load.
  iMod (inv_alloc N _ (r ↦ (λ: "x", f ! #r "x")) with "Hr") as "#HI".
  wp_pures.
  iLöb as "IH" forall (v Φ).
  wp_bind (! #r)%E.
  iInv "HI" as "Hr".
  wp_load.
  iModIntro.
  iFrame.
  iApply ("H" with "[$HP]").
  - clear v Φ.
    iIntros "%v %Φ !> HP HΦ".
    wp_pures.
    wp_apply ("IH" with "HP HΦ").
  - done.
Qed.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n => (S n) * factorial n
  end.

Lemma fac_spec (n : nat) : {{{ True }}} fac #n {{{ RET #(factorial n); True}}}.
Proof.
  iIntros "%Φ _ HΦ".
  iApply (myrec_spec _ _
    (λ v, ∃ n : nat, ⌜v = #n⌝)%I
    (λ v u, ∃ n : nat, ⌜v = #n⌝ ∗ ⌜u = #(factorial n)⌝)%I
  ).
  - clear n Φ.
    iIntros "%g %_ %Φ !> (#Hg & %n & ->) HΦ".
    wp_lam; wp_pures.
    rewrite (bool_decide_ext _ (n = 0)).
    2: {
      split; last by intros ->.
      intros [= H].
      by apply (inj Z.of_nat).
    }
    destruct (bool_decide_reflect (n = 0)).
    + subst n.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      by iExists 0.
    + destruct n; first done.
      wp_pures.
      rewrite Z.sub_1_r {3}Nat2Z.inj_succ.
      rewrite Z.pred_succ.
      wp_apply "Hg"; first by iExists _.
      iIntros "%_ (%m & %H & ->)".
      injection H as H.
      apply (inj Z.of_nat) in H.
      subst m.
      wp_pures.
      iApply "HΦ".
      iExists (S n).
      iPureIntro.
      split; first done.
      f_equal.
      by rewrite -Nat2Z.inj_mul.
  - by iExists n.
  - iIntros "!> %_ (%m & %H & ->)".
    injection H as H.
    apply (inj Z.of_nat) in H.
    subst m.
    by iApply "HΦ".
Qed.
  
End proofs.

