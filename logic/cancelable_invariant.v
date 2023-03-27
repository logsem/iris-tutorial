From iris_tutorial.logic Require Export key.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.

(*
  In this file we will use our key/lock ghost theory to construct cancelable invariants.
*)
Definition cinv `{invGS_gen hlc Σ, keyG Σ} (N : namespace) (γ : gname) (P : iProp Σ) : iProp Σ :=
  inv N (gLock γ P).

Section proofs.
Context `{!invGS_gen hlc Σ, !keyG Σ}.

(*
  cinv needs to implement many of the type classes we implemented for gLock. However it will not be timeless as invariants are infact time dependent.

  Even though invariants are time dependent, they still preserve time. Actually they do better than just preserve time, they are infact contractive.
*)
Global Instance cinv_contractive N γ : Contractive (cinv N γ).
Proof. solve_contractive. Qed.
Global Instance cinv_ne N γ : NonExpansive (cinv N γ).
Proof. apply contractive_ne, _. Qed.
Global Instance cinv_proper N γ : Proper ((≡) ==> (≡)) (cinv N γ).
Proof. apply ne_proper, _. Qed.

Global Instance cinv_persistent N γ P : Persistent (cinv N γ P) := _.

(*
  Like invariants, cinv preserves persistent biimplication.
*)
Lemma cinv_iff N γ P Q : cinv N γ P -∗ □ (P ↔ Q) -∗ cinv N γ Q.
Proof.
  iIntros "HP #H".
  iApply (inv_iff with "HP").
  iIntros "!> !>".
  by iApply gLock_iff.
Qed.

Lemma cinv_alloc E N P : ▷P ={E}=∗ ∃ γ, cinv N γ P ∗ key γ (DfracOwn 1).
Proof.
  iIntros "HP".
  iMod key_alloc as "[%γ Hγ]".
  iMod (inv_alloc N _ (gLock γ P) with "[HP]") as "I".
  { by iApply gLock_intro. }
  iModIntro.
  iExists γ.
  iFrame.
Qed.

Lemma cinv_acc E N γ dq P : ↑N ⊆ E → cinv N γ P -∗ key γ dq ={E, E∖↑N}=∗ ▷ P ∗ key γ dq ∗ (▷ P ={E∖↑N, E}=∗ True).
Proof.
  iIntros (?) "HI Hγ".
  iMod (inv_acc with "HI") as "[HP H]"; first done.
  iPoseProof (gLock_unlock with "Hγ HP") as "[>$ $]".
  iIntros "!> HP".
  iApply "H".
  by iApply gLock_intro.
Qed. 

Lemma cinv_cancel E N γ P : ↑N ⊆ E → cinv N γ P -∗ key γ (DfracOwn 1) ={E}=∗ ▷ P.
Proof.
  iIntros (?) "HI Hγ".
  iMod (inv_acc with "HI") as "[HP H]"; first done.
  iPoseProof (gLock_unlock with "Hγ HP") as "[Hγ HP]".
  iMod ("H" with "[Hγ]") as "_".
  { by iApply gLock_key. }
  done.
Qed.

End proofs.
