From iris.base_logic Require Import upred iprop.
From iris.proofmode Require Import proofmode.

Section proofs.
Context {Σ : gFunctors}.

(*
  When stating lemmas that do not depend on generic Iris propositions
  (which mention [Σ]), we have to manually specify the [Σ]. We do this
  locally using notation.
*)
Local Notation "⊢ P" := (⊢@{iPropI Σ} P).
Local Notation "Q ⊢ P" := (Q ⊢@{iPropI Σ} P).

(* ################################################################# *)
(** * Pure Propositions *)

(**
  The implementation of Iris in Coq has a unique class of propositions
  called `pure'. This class arises from the fact that Coq propositions
  can be embedded into the logic of Iris. Any Coq proposition [φ : Prop]
  can be turned into an Iris proposition through the pure embedding
  [⌜φ⌝ : iProp Σ]. This allows us to piggyback on much of the
  functionality and theory developed for the logic of Coq. The
  proposition [⌜φ⌝] is thus an Iris proposition, and we can use it as we
  would any other Iris proposition.
*)

Lemma asm_pure (φ : Prop) : ⌜φ⌝ ⊢ ⌜φ⌝.
Proof.
  iIntros "H".
  iApply "H".
Qed.

(**
  A pure proposition is then any Iris proposition [P] for which there
  exists a Coq proposition [φ], such that [P ⊣⊢ ⌜φ⌝].

  Pure propositions can be introduced using [iPureIntro]. This exits the
  Iris Proof Mode, throwing away the spatial context and turns the
  proposition into a Coq proposition.
*)
Lemma eq_5_5 : ⊢ ⌜5 = 5⌝.
Proof.
  iPureIntro.
  reflexivity.
Qed.

(**
  To eliminate a pure proposition, we can use the specialization pattern
  ["%_"]. This adds the proposition to the non-spatial context as a Coq
  proposition.
*)
Lemma eq_elm {A} (P : A → iProp Σ) (x y : A) : ⌜x = y⌝ -∗ P x -∗ P y.
Proof.
  iIntros "%Heq HP".
  rewrite -Heq.
  iApply "HP".
Qed.

(**
  It is quite easy to show that the propositions [⌜5 = 5⌝] and [⌜x = y⌝]
  from above are pure. However, it can become quite burdensome for more
  complicated Iris propositions. Fortunately, Iris has two typeclasses
  [IntoPure] and [FromPure] which can identify pure propositions for us.
  These are used by the [iPureIntro] tactic to automatically identify
  pure propositions.
*)

(** [True] is pure. *)
Lemma true_intro : ⊢ True.
Proof.
  iPureIntro.
  constructor.
Qed.

(** Conjunction preserves pureness. *)
Lemma and_pure : ⊢ ⌜5 = 5⌝ ∧ ⌜8 = 8⌝.
Proof.
  iPureIntro.
  split; reflexivity.
Qed.

(** Separating conjunction preserves pureness. *)
Lemma sep_pure : ⊢ ⌜5 = 5⌝ ∗ ⌜8 = 8⌝.
Proof.
  iPureIntro.
  split; reflexivity.
Qed.

(** Wand preserves pureness. *)
Lemma wand_pure {A} (x y : A) : ⊢ ⌜x = y⌝ -∗ ⌜y = x⌝.
Proof.
  iPureIntro.
  intros Heq.
  symmetry.
  assumption.
Qed.

(** Arbitrary Iris propositions are not pure. *)
Lemma abstr_not_pure (P : iProp Σ) : ⊢ P -∗ ⌜8 = 8⌝.
Proof.
  Fail iPureIntro. (* [P] is not pure *)
  iIntros "HP".
  iPureIntro. (* [⌜8 = 8⌝] is pure *)
  reflexivity.
Qed.

(**
  The pure embedding allows us to state an important property, namely
  soundness. Soundness is proved in the [uPred_primitive.pure_soundness]
  lemma stating: [∀ φ, (True ⊢ ⌜φ⌝) → φ]. This means that anything
  proved inside the Iris logic is as true as anything proved in Coq.
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

Lemma pure_adj2 (P : iProp Σ) : ⌜⊢ P⌝ -∗ P.
Proof.
  (* exercise *)
Admitted.

End proofs.
