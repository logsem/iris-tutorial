From iris.algebra Require Import excl.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.

Definition mk_lock : val :=
  λ: <>, ref #false.
Definition acquire : val :=
  rec: "acquire" "l" :=
  if: CAS "l" #false #true then
    #()
  else
    "acquire" "l".
Definition release : val :=
  λ: "l", "l" <- #false.

Section proofs.
Context `{heapGS Σ}.
Let N := nroot .@ "lock".

Context `{inG Σ (excl ())}.

Definition locked γ : iProp Σ := own γ (Excl ()).

Definition lock_inv γ l P : iProp Σ :=
  ∃ b : bool, l ↦ #b ∗ if b then True else own γ (Excl ()) ∗ P.

Definition is_lock γ v P : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ inv N (lock_inv γ l P).

Lemma mk_lock_spec P : {{{ P }}} mk_lock #() {{{ γ v, RET v; is_lock γ v P }}}.
Proof.
  iIntros "%Φ HP HΦ".
  wp_lam.
  wp_alloc l as "Hl".
  iMod (own_alloc (Excl ())) as "[%γ Hγ]".
  { done. }
  iMod (inv_alloc N _ (lock_inv γ l P) with "[HP Hl Hγ]") as "I".
  {
    iNext.
    iExists false.
    iFrame.
  }
  iModIntro.
  iApply "HΦ".
  iExists l.
  by iFrame.
Qed.

Lemma acquire_spec γ v P : {{{ is_lock γ v P }}} acquire v {{{ γ v, RET v; locked γ ∗ P }}}.
Proof.
  iIntros "%Φ (%l & -> & #I) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (CmpXchg _ _ _).
  iInv "I" as ([]) "[Hl Hγ]".
  - wp_cmpxchg_fail.
    iModIntro.
    iSplitL "Hl Hγ".
    {
      iNext.
      iExists true.
      iFrame.
    }
    wp_pures.
    wp_apply ("IH" with "HΦ").
  - wp_cmpxchg_suc.
    iModIntro.
    iSplitL "Hl".
    {
      iNext.
      iExists true.
      iFrame.
    }
    wp_pures.
    iModIntro.
    iApply ("HΦ" with "Hγ").
Qed.

Lemma release_spec γ v P : {{{ is_lock γ v P ∗ locked γ ∗ P }}} release v {{{ RET #(); True }}}.
Proof.
  iIntros "%Φ ((%l & -> & I) & Hγ & HP) HΦ".
  wp_lam.
  iInv "I" as "(%b & Hl & _)".
  wp_store.
  iModIntro.
  iSplitL "Hγ Hl HP".
  - iNext.
    iExists false.
    iFrame.
  - by iApply "HΦ".
Qed.

End proofs.
