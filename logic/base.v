From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.

(*
  All proofs in Iris are done in a context with a `Σ: gFunctors`. It is used as a parameter in `iProp Σ` the type of iris propositions to specify available resources.
The details of Σ will come later. For now just remember to work inside a section with a Σ in it's context.
  Keep in mind that `Σ` has type `gFunctors` plural, not `gFunctor` singular.
  There is a coersion from gFunctor to gFunctors, so everything will seem to work until Σ becomes important.
*)
Section proofs.
Context {Σ: gFunctors}.

(*
  Iris propositions contain many of the usual logical connectives. Thus iris used a notation scope to overload the usual logical notation.
  This scope is delimited by `I` and bound to `iProp Σ`. As such you may need to wrap your propositions in `(_)%I` to use the notations.

  Iris defines two coq propositions for proving Iris propositions:
  - `⊢ P` asks whether `P` holds with no assumptions
  - `P ⊢ Q` asks whether `Q` holds assuming `P`

  There is no explicit proposition allowing you to give multiple hypotheses.
  This is partially because it's unesesary as assumptions can be curried or combined.
  However, and more importantly, unlike in clasical logic, in seperation logic we have multiple sensible choices for combining propositions.
  Iris is equiped with the usual and connective, however this is rarely used. Instead we use the seperating conjunction `P ∗ Q` stating that `P` and `Q` are satisfied using seperate resources.
  In fact seperation is so prevalent that `P ⊢ Q` is more commonly written as `-∗` the seperating implication also known as magic wand.
*)
Lemma asm (P : iProp Σ) : P ⊢ P.
Proof.
  (*
    To prove such a stament we use the Iris proofmode. This is done using the tactic `iStartProof`.
    This new proofmode has it's own list of hypotheses, much like coq's proofmode.
  *)
  iStartProof.
  (*
    In order to manipulate the Iris context, we use tactics with the same name as in coq, but prefixed with 'i' for iris.
    These tactics use stings as identifies rather than coq identifiers.
  *)
  iIntros "HP".
  iApply "HP".
Qed.

(*
  Writing a wand instead of a turnstyle makes currying more natural.
  Here is the iris version of modus ponens.
*)
Lemma modus_ponens (P Q : iProp Σ) : P -∗ (P -∗ Q) -∗ Q.
Proof.
  iStartProof.
  iIntros "HP HQ".
  (**)
Abort.

(*
  Iris does have conjuction `∧` and `→`, but they are rarely used and interacts poorly with the iris proofmode.
  Instead we use the separating disjunction `∗`, a sligtly stronger version of `∗`.
*)
Lemma sep_and (P Q : iProp Σ) : P ∗ Q ⊢ P ∧ Q.
Proof.
  (* `∗` is eleminated in the same way `∧` is in coq. *)
  iIntros "[HP HQ]".
  (* While `∧` is still introduced in the same way. *)
  iSplit.
  - iApply "HP".
  - iApply "HQ".
Qed.

Lemma sep_comm (P Q : iProp Σ) : P ∗ Q ⊢ Q ∗ P.
Proof.
  iIntros "[HP HQ]".
  (*
    Unlike `∧`, `∗` is not idempotent. Specificly there are propositions for which `¬(P ⊢ P ∗ P)`.
    Because of this it is generally not possible to use `iSplit` to introduce `∗`.
    Instead we have to use `iSplit` as it would duplicate all hypotheses.
  *)
  Fail iSplit.
  (*
    Instead Iris introduced the tactics `iSplitL` and `iSplitR`. These allows you to specify which hypotheses go to the left and right subproofs respectively.
  *)
  iSplitL "HQ".
  - iApply "HQ".
  - iApply "HP".
Qed.

Lemma sep_assoc (P Q R : iProp Σ) : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R.
Proof.
  iStartProof.
  (* Iris proofmode supports "( P & .. & Q & R )" patterns as a shorthand for "[P .. [Q R] ..]" *)
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

(*
  Disjunctions `∨` are treated much like disjuctions in coq.
  The introduction pattern `[ _ | _ ]` allows us to eliminate a disjunction,
  while the tactics `iLeft` and `iRight` lets us introduce them.
*)
Lemma or_comm (P Q : iProp Σ) : Q ∨ P ⊢ P ∨ Q.
Proof.
  iIntros "[HQ|HP]".
  - iRight.
    iApply "HQ".
  - (**)
Abort.

Lemma or_elem (P Q R : iProp Σ) : (P -∗ R) -∗ (Q -∗ R) -∗ P ∨ Q -∗ R.
Proof.
  (**)
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
