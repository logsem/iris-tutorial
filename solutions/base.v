From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.

(**
  All proofs in Iris are done in a context with a [Σ: gFunctors]. It
  is used as a parameter in [iProp Σ] the type of iris propositions to
  specify available resources. The details of Σ will come later. For
  now just remember to work inside a section with a Σ in it's context.
  Keep in mind that [Σ] has type [gFunctors] plural, not [gFunctor]
  singular. There is a coersion from gFunctor to gFunctors, so
  everything will seem to work until Σ becomes relevant.
*)
Section proofs.
Context {Σ: gFunctors}.

(**
  Iris propositions contain many of the usual logical connectives. As
  such iris uses a notation scope to overload the usual logical
  notation. This scope is delimited by [I] and bound to [iProp Σ]. As
  such you may need to wrap your propositions in [(_)%I] to use the
  notations.

  Iris defines two coq propositions for proving Iris propositions:
  - [⊢ P] asks whether [P] holds with no assumptions
  - [P ⊢ Q] asks whether [Q] holds assuming [P]

  There is no explicit proposition allowing you to give multiple
  hypotheses. This is partially because it's unesesary as assumptions
  can be curried or combined. However, and more importantly, unlike in
  clasical logic, in seperation logic we have multiple sensible
  choices for combining propositions. Iris is equiped with the usual
  `and` connective written [P ∧ Q], however this is rarely used.
  Instead we use the seperating conjunction [P ∗ Q] stating that [P]
  and [Q] are satisfied using seperate resources. In fact seperation
  is so widely used that [P ⊢ Q] is more commonly written as [P -∗ Q]
  the seperating implication also known as magic wand or simply wand.

  Iris has a proofmode that works very similarly to the coq proof
  mode. With this it is posible to proof Iris propositions much like
  you would coq propositions. To see this in action we will prove the
  statement [P ⊢ P] for all [P].
*)
Lemma asm (P : iProp Σ) : P ⊢ P.
Proof.
  (**
    First we need to enter the Iris proofmode. To do this we can use
    the tactic [iStartProof]. However most Iris tactics will
    automatically start the Iris proofmode for you, so this is not
    necessary and is usually omitted.
  *)
  iStartProof.
  (**
    This new proofmode has it's own context of hypotheses, working
    much like coq's proofmode. This context is called the spacial
    context and consists of hypotheses of Iris propositions.
    All tactics working directly with the Iris logic are prefixed by
    an i. This allows Iris to reuse familiar tactics names. These
    tactics use stings as identifies rather than coq identifiers so
    that they can refer to the Iris context.

    To introduce hypotheses in coq, one would normaly use the tactic
    [intros HP]. However we are working with the iris logic so we use
    instead use the tactic [iIntros "HP"].
  *)
  iIntros "HP".
  (**
    And to finish the proof on would normaly use either [exact] or
    [apply]. So in Iris we use either [iExact] or [iApply].
  *)
  iApply "HP".
Qed.

(**
  Writing a wand instead of a turnstyle makes currying more natural.
  Here is the iris version of modus ponens. This is provable using
  only [iIntros] and [iApply].
*)
Lemma modus_ponens (P Q : iProp Σ) : P -∗ (P -∗ Q) -∗ Q.
Proof.
  iIntros "P H".
  iApply "H".
  iApply "P".
Qed.

(**
  Seperating conjunction is very analogous to conjunction in coq. To
  see this, let's prove that it commutes.
*)
Lemma sep_comm (P Q : iProp Σ) : P ∗ Q ⊢ Q ∗ P.
Proof.
  (**
    To eleminate a seperating conjunction we can use the tactic
    [iDestruct] with the usual introduction pattern. However, like
    with [intros], we can use [iIntros] to eleminate directly.
  *)
  iIntros "[HP HQ]".
  (**
    Unlike [∧], [∗] is not idempotent. Specificly there are
    propositions for which [¬(P ⊢ P ∗ P)]. Because of this it is
    generally not possible to use `iSplit` to introduce [∗]. [iSplit]
    would duplicate the Iris context, and is therefor not avaiable
    when the context is non-empty.
  *)
  Fail iSplit.
  (**
    Instead Iris introduces the tactics [iSplitL] and [iSplitR]. These
    allows you to specify which hypotheses go to the left and right
    subproofs respectively.
  *)
  iSplitL "HQ".
  - iApply "HQ".
  - iApply "HP".
Qed.

(**
  Just as with the coq tactics, Iris allows nesting of introduction
  patterns. Infact, like coq, iris supports patterns of the form
  [(H1 & .. & H2 & H3)] as a shorthand for [[H1 .. [H2 H3] ..]].

  Try to use parenthesis introduction to prove associativity for [∗].
*)
Lemma sep_assoc_1 (P Q R : iProp Σ) : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R.
Proof.
  iIntros "(P & Q & R)".
  iSplitR "R"; last iApply "R".
  iSplitL "P".
  - iApply "P".
  - iApply "Q".
Qed.

(**
  iProp supports bientailment as equivalence relation [P ⊣⊢ Q]. Most
  connectives preserves this relation encoded using the setoid library
  with the typeclass [Proper]. It is therefor possible to use the
  `rewrite` tactic inside the iris proofmode.
  bientailment is internally defined as [(P -∗ Q) ∧ (Q -∗ P)], so it
  can be decomposed using the [iSplit] tactic.

  For hypotheses with multiple curried wands, it is again nesessary to
  specify how to split the Iris context during application. This can
  be done as [iApply ("Hyp" with "[H1 H2 H3] [H4 H5]")]. Each square
  brackets specifies the peace of the context going to that argument.
  Hypotheses that fit arguments dirrectly can be supply dirrectly
  without a square bracket to avoid trivial subgoals.

  Prove currying for the seperation connectives.
*)
Lemma wand_adj (P Q R : iProp Σ) : (P -∗ Q -∗ R) ⊣⊢ (P ∗ Q -∗ R).
Proof.
  iSplit.
  - iIntros "H [P Q]".
    iApply ("H" with "P Q").
  - iIntros "H P Q".
    iApply "H".
    iSplitL "P".
    + iApply "P".
    + iApply "Q".
Qed.

(**
  Disjunctions [∨] are treated just like disjuctions in coq.
  The introduction pattern [[ _ | _ ]] allows us to eliminate a disjunction,
  while the tactics [iLeft] and [iRight] lets us introduce them.

  Prove that or commutes.
*)
Lemma or_comm (P Q : iProp Σ) : Q ∨ P ⊢ P ∨ Q.
Proof.
  iIntros "[Q | P]".
  - by iRight.
  - by iLeft.
Qed.

(**
  We can even prove the usual elemination rule for or elemination
  written with seperation. This version is however not very useful, as
  it does not allow the 2 cases to share resources.
*)
Lemma or_elem (P Q R : iProp Σ) : (P -∗ R) -∗ (Q -∗ R) -∗ P ∨ Q -∗ R.
Proof.
  iIntros "H1 H2 [P|Q]".
  - iApply ("H1" with "P").
  - iApply ("H2" with "Q").
Qed.

Lemma sep_or_distr (P Q R : iProp Σ) : P ∗ (Q ∨ R) ⊣⊢ P ∗ Q ∨ P ∗ R.
Proof.
  iSplit.
  - iIntros "[P [Q | R]]".
    + iLeft. iFrame.
    + iRight. iFrame.
  - iIntros "[[P Q] | [P R]]".
    + iFrame.
    + iFrame.
Qed.

(**
  Iris has existetial and universal quantifiers over defined on any
  coq type. Existensial quantifiers are proved using the [iExists]
  tactic, using the same syntax as [exists]. Elemination of
  existensials is done through the pattern "[%_ _]" or as part of a
  "(_&..&_)" with a "%" in front of the existential variable.
*)
Lemma sep_ex_distr {A} (P : iProp Σ) (Φ : A → iProp Σ) : (P ∗ ∃ x, Φ x) ⊣⊢ ∃ x, P ∗ Φ x.
Proof.
  iSplit.
  - iIntros "(P & %x & Φ)".
    iExists x.
    iFrame.
  - iIntros "(%x & P & Φ)".
    iSplitL "P".
    + done.
    + by iExists x.
Qed.

(**
  Forall likewise works almost like in coq. To introduce the variables
  you can either use [iIntros (x y z)] or [iIntros "%x %y %z"]. These patterns
  are interchangable.
  To specify parameters of hypotheses we write [iApply ("H" $! x y z)].
*)
Lemma sep_all_distr {A} (P Q : A → iProp Σ) : (∀ x, P x) ∗ (∀ x, Q x) -∗ (∀ x, P x ∗ Q x).
Proof.
  iIntros "[P Q] %x".
  by iSplitL "P".
Qed.

End proofs.
