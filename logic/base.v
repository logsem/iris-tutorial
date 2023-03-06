From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.

(*
  All proofs in Iris are done in a context with a `Σ: gFunctors`. It is used as a parameter in `iProp Σ` the type of iris propositions.
The details will come later.
  Keep in mind that `Σ` has type `gFunctors` plural, not `gFunctor` singular.
*)
Section proofs.
Context {Σ: gFunctors}.

(* Turnstyle `P ⊢ Q` is the coq proposition that Q follows from P in the Iris logic. *)
Lemma asm (P : iProp Σ) : P ⊢ P.
Proof.
  set (λ x : gFunctor, x : gFunctors).
  Search gFunctors.singleton.
  (*
    To prove such a stament we use the Iris proofmode. This is done using the tactic `iStartProof`.
    This new proofmode has it's own list of hypotheses, much like coq's proofmode.
    However, these hypotheses may only refer to iris propositions. All other hypotheses are kept in the coq context.
  *)
  iStartProof.
  (*
    Notice that the turnstyle turns into a magic wand (-∗) instead of an implication.
    The magic wand is the separation version of implication, and interacts with the Iris context, like implication would in coq.
  *)
  (*
    In order to manipulate the Iris context, we use tactics with the same name as in coq, but with an 'i' for iris at the begining.
    These tactics takes a string as input rather than a list identifiers or patterns.
  *)
  iIntros "HP".
  iApply "HP".
Qed.

(*
  As turnstyle turns into a wand, you are allowed to write a wand instead.
  This is usefull when describing multiple curried hypotheses.
*)
Lemma modus_ponens (P Q : iProp Σ) : P -∗ (P -∗ Q) -∗ Q.
Proof.
  iStartProof.
  iIntros "HP HQ".
  (**)
Abort.

(*
  Disjunctions `∨` are treated much like disjuctions in coq.
  The introduction pattern `[ _ | _ ]` allows us to eliminate a disjunction,
  while the tactics `iLeft` and `iRight` lets us introduce them.
*)
Lemma or_comm (P Q : iProp Σ) : Q ∨ P ⊢ P ∨ Q.
Proof.
  iStartProof.
  iIntros "H".
  (* Here I'm using an explicit destruct tactic. However `iIntros` accept the same introduction patterns. *)
  iDestruct "H" as "[HQ|HP]".
  - iRight.
    iApply "HQ".
  - (**)
Abort.

Lemma or_elem (P Q R : iProp Σ) : (P -∗ R) -∗ (Q -∗ R) -∗ P ∨ Q -∗ R.
Proof.
  iStartProof.
  (**)
Abort.

(*
  Iris does have conjuction `∧`, but it's rarely used and interacts poorly with the iris proofmode.
  Instead we use the separating disjunction `∗`.
  It can be eleminated using the introduction pattern "[ _ _ ]".
  Iris does have the tactic `iSplit` that works on `∧`, but not on `∗`.
  This is because we are not allowed to use the same resources to satisfy both sides of a `∗`.
  Therefor we instead use `iSplitL` and `iSplitR` to specify which hypotheses we want on respectively the left or the right.
*)
Lemma sep_comm (P Q : iProp Σ) : P ∗ Q ⊢ Q ∗ P.
Proof.
  iStartProof.
  iIntros "[HP HQ]".
  iSplitR "HP".
  - iApply "HQ".
  - iApply "HP".
Qed.

Lemma sep_assoc (P Q R : iProp Σ) : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R.
Proof.
  iStartProof.
  (* Iris proofmode supports "( P & .. & Q & R )" patterns of the form "[P .. [Q R] ..]" *)
  iIntros "(HP & HQ & HR)".
  (**)
Abort.

(*
  iProp supports bientailment as equivalence relation `P ⊣⊢ Q` or `P ∗-∗ Q` defined as `(P -∗ Q) ∧ (Q -∗ P)`.
  Most connectives preserves this relation encoded using the setoid library with the typeclass `Proper`.
  It is therefor possible to use the `rewrite` tactic inside the iris proofmode.
*)
Lemma wand_adj (P Q R : iProp Σ) : (P -∗ Q -∗ R) ⊣⊢ (P ∗ Q -∗ R).
Proof.
  iStartProof.
  (* As bientailment is defined with a `∧`, we use the `iSplit` tactic to introduce it. *)
  iSplit.
  - iIntros "H [HP HQ]".
    (*
      "H" takes two arguments.
      These arguments are separated, meaning we again have to separate our context.
      To specify this we don't call `iApply` directly on "H" instead we write `("H" with "[HP] [HQ]")`.
      Each "[]" represents a new goal, accepts a list of hypotheses we want to prove that subgoal.
    *)
    iApply ("H" with "[HP] [HQ]").
    + iApply "HP".
    + iApply "HQ".
  - (**)
Abort.

Lemma sep_or_distr (P Q R : iProp Σ) : P ∗ (Q ∨ R) ⊣⊢ P ∗ Q ∨ P ∗ R.
Proof.
  iStartProof.
  iSplit.
  (**)
Abort.

(*
  Iris has existetial and universal quantifiers over defined on any coq type.
  Existensial quantifiers are introduced using the `iExists` tactic, using the same syntax as `exists`.
  Elemination of existensials is done through the pattern "[%_ _]" or as part of a "(_&..&_)" with a "%" in front of the existential variable.
*)
Lemma sep_ex_distr {A} (P : iProp Σ) (Φ : A → iProp Σ) : (P ∗ ∃ x, Φ x) ⊣⊢ ∃ x, P ∗ Φ x.
Proof.
  iStartProof.
  iSplit.
  - iIntros "(HP&%x&HΦ)".
    iExists x.
    iSplitL "HP".
    + iApply "HP".
    + iApply "HΦ".
  - (**)
Abort.

End proofs.
