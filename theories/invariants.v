From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.

Definition prog : expr :=
  let: "l" := ref #0 in
  Fork ("l" <- #1);;
  !"l".

Section proofs.
Context `{!heapGS Σ}.

Let N := nroot .@ "stuff".

Lemma wp_prog : {{{ True }}} prog {{{ v, RET v; ⌜v = #0⌝ ∨ ⌜v = #1⌝ }}}.
Proof.
  iIntros "%Φ _ HΦ".
  rewrite /prog.
  wp_alloc l as "Hl".
  wp_pures.
  iMod (inv_alloc N _ (∃ v, l ↦ v ∗ (⌜v = #0⌝ ∨ ⌜v = #1⌝)) with "[Hl]") as "#I".
  {
    iNext.
    iExists #0.
    iFrame.
    by iLeft.
  }
  wp_apply wp_fork.
  - iInv "I" as "(%v & Hl & _)".
    wp_store.
    iSplitL; last done.
    iIntros "!> !>".
    iExists #1.
    iFrame.
    by iRight.
  - wp_pures.
    iInv "I" as "(%v & Hl & #Hv)".
    wp_load.
    iModIntro.
    iSplitL "Hl".
    + iExists v.
      by iFrame.
    + by iApply "HΦ".
Qed.

End proofs.
