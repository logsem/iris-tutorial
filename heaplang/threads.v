From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.
From iris_tutorial.logic Require Import key.

(*
  Heaplang has concurency in the form of a fork operation.
  This operation takes an expresion and runs it in a seperate thread. Meanwhile, the initial thread continues execution with a unit value.
  Fork does not have a reduction tactic. Instead we need to use it's specification explicitly via `wp_fork`.
  This lemma is more general than we need for our current use cases, but it esentially states that:
  `WP e {{_, True}} -∗ ▷ Φ #() -∗ WP Fork e {{v, Φ v}}`

  We can use fork to implement other common concurency operators such as `spawn` and `join`
*)
Definition spawn: val :=
  λ: "f",
  let: "c" := ref NONE in
  Fork ("c" <- SOME ("f" #()));;
  "c".
Definition join: val :=
  rec: "join" "c" :=
  match: !"c" with
    NONE => "join" "c"
  | SOME "x" => "x"
  end.

(*
  We can then use the function to define the par operator.
*)
Definition par: val :=
  λ: "f1" "f2",
  let: "h" := spawn "f1" in
  let: "v2" := "f2" #() in
  let: "v1" := join "h" in
  ("v1", "v2").

(* The notation for the par operator then hides the thunks *)
Notation "e1 ||| e2" := (par (λ: <>, e1)%E (λ: <>, e2)%E) : expr_scope.
(* Lambda expresion actually canonicalize as lambda values. Thus we need to refer to this canonical form when proving our specifications *)
Notation "e1 ||| e2" := (par (λ: <>, e1)%V (λ: <>, e2)%V) : val_scope.

Section threads.
Context `{!heapGS Σ, keyG Σ}.

Let N := nroot .@ "spawn".

Definition spawn_inv (γ : gname) (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ v, l ↦ v ∗ (⌜v = NONEV⌝ ∨ ∃ w, ⌜v = SOMEV w⌝ ∗ gLock γ (Ψ w)).

Definition join_handle (v : val) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ γ (l : loc), ⌜v = #l⌝ ∗ key γ (DfracOwn 1) ∗ inv N (spawn_inv γ l Ψ).

Global Instance spawn_inv_ne n γ l :
  Proper (pointwise_relation val (dist n) ==> dist n) (spawn_inv γ l).
Proof. solve_proper. Qed.
Global Instance join_handle_ne n l :
  Proper (pointwise_relation val (dist n) ==> dist n) (join_handle l).
Proof. solve_proper. Qed.


Lemma spawn_spec (Ψ : val → iProp Σ) (f : val) :
  {{{ ▷ WP f #() {{ Ψ }} }}} spawn f {{{ v, RET v; join_handle v Ψ }}}.
Proof.
  iIntros "%Φ Hf HΦ".
  rewrite /spawn.
  wp_alloc c as "Hc".
  wp_pures.
  iMod (key_alloc) as "[%γ Hγ]".
  iMod (inv_alloc N _ (spawn_inv γ c Ψ) with "[Hc]") as "#I".
  {
    iNext.
    iExists NONEV.
    iFrame.
    by iLeft.
  }
  wp_apply (wp_fork with "[Hf]").
  - iNext.
    wp_bind (f _).
    iApply (wp_wand with "Hf").
    iIntros "%v Hv".
    wp_pures.
    iInv N as "(%v' & Hc & _)".
    wp_store.
    iModIntro.
    iSplit=>//.
    iNext.
    iExists (SOMEV v).
    iFrame.
    iRight.
    iExists v.
    iSplit=>//.
    by iApply gLock_intro.
  - wp_pures.
    iModIntro.
    iApply "HΦ".
    iExists γ, c.
    by iFrame "Hγ I".
Qed.

Lemma join_spec (Ψ : val → iProp Σ) (h : val) :
  {{{join_handle h Ψ}}} join h {{{v, RET v; Ψ v}}}.
Proof.
  iIntros "%Φ (%γ & %l & -> & Hγ & #I) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (! #l)%E.
  iInv "I" as "(%_ & Hl & [>-> | (%w & >-> & HΨ)])".
  - wp_load.
    iModIntro.
    iSplitL "Hl".
    {
      iNext.
      iExists NONEV.
      iFrame.
      by iLeft.
    }
    wp_pures.
    iApply ("IH" with "Hγ HΦ").
  - wp_load.
    iModIntro.
    iPoseProof (gLock_unlock with "Hγ HΨ") as "[Hγ HΨ]".
    iSplitL "Hγ Hl".
    {
      iNext.
      iExists (SOMEV w).
      iFrame.
      iRight.
      iExists w.
      iSplit; first done.
      by iApply gLock_key.      
    }
    wp_pures.
    by iApply "HΦ".
Qed.

Lemma par_spec (P1 P2 : iProp Σ) (e1 e2 : expr) (Q1 Q2 : val → iProp Σ) :
  {{{P1}}} e1 {{{v, RET v; Q1 v}}} -∗
  {{{P2}}} e2 {{{v, RET v; Q2 v}}} -∗
  {{{P1 ∗ P2}}} (e1 ||| e2)%V {{{v1 v2, RET (v1, v2); Q1 v1 ∗ Q2 v2}}}.
Proof.
  iIntros "#H1 #H2 %Φ !> [HP1 HP2] HΦ".
  rewrite /par.
  wp_pures.
  wp_apply (spawn_spec Q1 with "[HP1]").
  {
    iNext.
    wp_pures.
    iApply ("H1" with "HP1").
    iIntros "!> %v H".
    done.
  }
  iIntros "%h Hh".
  wp_pures.
  wp_apply ("H2" with "HP2").
  iIntros "%v2 HQ2".
  wp_pures.
  wp_apply (join_spec with "Hh").
  iIntros "%v1 HQ1".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

End threads.