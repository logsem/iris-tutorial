From iris.base_logic Require Import upred iprop.
From iris.proofmode Require Import proofmode.

Section proofs.
Context {Σ : gFunctors}.

(**
  Turnstyle can be used as a unary operator to ask whether a
  proposition follows from the empty context. Here we locally specify
  that we want to talk about Iris propositions over [Σ].
  This is useful when stating lemmas that don't depend on generic Iris
  propositions.
*)
Local Notation "⊢ P" := (⊢@{iPropI Σ} P).

(**
  Coq propositions can be embedded into Iris using the pure modality
  [⌜Φ⌝]. Such propositions can be introduced using [iPureIntro]. This
  will exit the Iris proofmode, throwing away the Iris context. Pure
  propositions can be eliminated using the introduction pattern "%_".
*)
Lemma eq_5_5 : ⊢ ⌜5 = 5⌝.
Proof.
  iPureIntro.
  reflexivity.
Qed.

Lemma eq_elm {A} (P : A → iProp Σ) (x y : A) : ⌜x = y⌝ -∗ P x -∗ P y.
Proof.
  iIntros "%H HP".
  rewrite -H.
  iApply "HP".
Qed.

(**
  Iris has a class of propositions we call pure.
  These are the propositions [P] that are bi-entailed by [⌜Φ⌝] for
  some Φ. Iris has two typeclasses, [IntoPure] and [FromPure], to
  identify such propositions.
*)

Lemma true_intro : ⊢ True.
Proof.
  iPureIntro. (* True is pure*)
  constructor.
Qed.

Lemma and_pure : ⊢ ⌜5 = 5⌝ ∧ ⌜8 = 8⌝.
Proof.
  iPureIntro. (* And preserves pureness *)
  split; reflexivity.
Qed.

Lemma sep_pure : ⊢ ⌜5 = 5⌝ ∗ ⌜8 = 8⌝.
Proof.
  iPureIntro. (* Separation preserves pureness *)
  split; reflexivity.
Qed.

(**
  The pure modality allows us to state an important property,
  namely soundness. 

  Soundness is proved in the [uPred_primitive.pure_soundness] lemma
  stating: [∀ φ, (True ⊢ ⌜φ⌝) → φ]

  This means that anything proved inside the Iris logic is as true as
  anything proved in Coq.
*)

(**
  [⌜_⌝] turns Coq propositions into Iris propositions, while [⊢ _] turns
  Iris propositions into Coq propositions. These operations are not
  inverses, but they are related.
*)
Lemma pure_adj1 (φ : Prop) : φ → ⊢ ⌜φ⌝.
Proof.
  (* exercise *)
Admitted.

Lemma pure_adj2 (P : iProp Σ) : ⌜⊢P⌝ -∗ P.
Proof.
  (* exercise *)
Admitted.

End proofs.
