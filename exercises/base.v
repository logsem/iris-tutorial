From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.

(**
  Iris uses ssreflect. However we won't assume knowledge of ssreflect
  tactics. As such we will limit the use of ssreflect tactics when
  possible. However ssreflect overrides the definition of [rewrite]
  changing its syntacs and behaviour slightly. Notebly:
  - No commas between arguments, meaning you have to write
    [rewrite H1 H2] instead of [rewrite H1, H2].
  - [rewrite -H] instead of [rewrite <-H]
  - Occurences are written in from of the argument
    [rewrite {1 2 3}H] instead of [rewrite H at 1 2 3]
  - Rewrite can unfold definitions as [rewrite /def] which does the
    same as [unfold def]
*)

(**
  All proofs in Iris are done in a context with a [Σ: gFunctors]. It
  is used as a parameter in [iProp Σ], the type of iris propositions, to
  specify available resources. The details of Σ will come later. For
  now, just remember to work inside a section with a Σ in it's context.
  Keep in mind that [Σ] has type [gFunctors] plural, not [gFunctor]
  singular. There is a coersion from gFunctor to gFunctors, so
  everything will seem to work until Σ becomes relevant, if you 
  accidentally use [gFunctor].
*)
Section proofs.
Context {Σ: gFunctors}.

(**
  Iris propositions include many of the usual logical connectives. As
  such, Iris uses a notation scope to overload the usual logical
  notation. This scope is delimited by [I] and bound to [iProp Σ]. 
  Hence, you may need to wrap your propositions in [(_)%I] to use the
  notations.

  Iris defines two Coq propositions for proving Iris propositions:
  - [⊢ P] asks whether [P] holds with no assumptions
  - [P ⊢ Q] asks whether [Q] holds assuming [P]

  There is no explicit proposition allowing you to give multiple
  hypotheses. This is partially because it is not necessary, as assumptions
  can be curried or combined. However, more importantly, unlike in
  clasical logic, in separation logic we have multiple sensible
  choices for combining propositions. Iris is equipped with the usual
  'and' connective, written [P ∧ Q], however this is rarely used.
  Instead, we often use the separating conjunction [P ∗ Q], stating that [P]
  and [Q] are satisfied using separate resources. In fact separation
  is so widely used that [P ⊢ Q] is more commonly written as [P -∗ Q],
  the separating implication, also known as magic wand or simply wand.

  Iris has a proofmode that works very similarly to the Coq proof
  mode. With this it is posible to proove Iris propositions much like
  you would Coq propositions. To see this in action we will prove the
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
    The Iris proofmode has it's own context of hypotheses, working
    much like Coq's proofmode. This context is called the spatial
    context and consists of hypotheses of Iris propositions.
    All tactics working directly with the Iris logic are prefixed by
    an i. This allows Iris to reuse familiar tactic names. The Iris
    tactics use strings as identifies, rather than Coq identifiers, so
    that they can refer to the Iris context.

    To introduce hypotheses in Coq, one would normally use the tactic
    [intros H]. However we are working with the Iris logic so instead
    we use the tactic [iIntros "H"].
  *)
  iIntros "H".
  (**
    And to finish the proof, one would normally use either [exact] or
    [apply]. So in Iris we use either [iExact] or [iApply].
  *)
  iApply "H".
Qed.

(**
  Writing a wand instead of a turnstyle makes currying more natural.
  Here is the Iris version of modus ponens. It is provable using
  only [iIntros] and [iApply].
*)
Lemma modus_ponens (P Q : iProp Σ) : P -∗ (P -∗ Q) -∗ Q.
Proof.
  (* exercise *)
Admitted.

(**
  Separating conjunction has some of the same properties as 
  ordinary conjection in Coq. To see this, let's prove that it 
  is commutative.
*)
Lemma sep_comm (P Q : iProp Σ) : P ∗ Q ⊢ Q ∗ P.
Proof.
  (**
    To eliminate a separating conjunction we can use the tactic
    [iDestruct] with the usual introduction pattern. However, like
    with [intros], we can use [iIntros] to eliminate directly.
  *)
  iIntros "[HP HQ]".
  (**
    Unlike [∧], [∗] is not idempotent. Specifically, there are Iris
    propositions for which [¬(P ⊢ P ∗ P)]. Because of this, it is
    generally not possible to use `iSplit` to introduce [∗]. [iSplit]
    would duplicate the Iris context, and is therefore not avaiable
    when the context is non-empty.
  *)
  Fail iSplit.
  (**
    Instead Iris introduces the tactics [iSplitL] and [iSplitR]. These
    allow you to specify which hypotheses go to the left and right
    subproofs respectively.
  *)
  iSplitL "HQ".
  - iApply "HQ".
  - iApply "HP".
Qed.

(**
  Just as with the Coq tactics, Iris allows nesting of introduction
  patterns. In fact, like Coq, Iris supports patterns of the form
  [(H1 & .. & H2 & H3)] as a shorthand for [[H1 .. [H2 H3] ..]].

  Try to use an introduction with a pattern with parentheses 
  to prove associativity for [∗].
*)
Lemma sep_assoc_1 (P Q R : iProp Σ) : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R.
Proof.
  (* exercise *)
Admitted.

(**
  Manually splitting a separation can become tedious. To alleviate
  this, we can use the `iFrame` tactic. This tactic pairs up
  hypotheses with pieces of a separation sequence.
  Its full use is described in
  https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md?ref_type=heads#separation-logic-specific-tactics
*)
Lemma sep_comm_v2 (P Q : iProp Σ) : P ∗ Q ⊢ Q ∗ P.
Proof.
  iIntros "[HP HQ]".
  iFrame.
Qed.  

(**
  Bi-entailment of Iris propositions is denoted [P ⊣⊢ Q]. It is
  and equivalence relation and most connectives preserve 
  this relation encoded using the setoid library
  with the typeclass [Proper]. It is therefore possible to use the
  `rewrite` tactic inside the Iris proofmode.
  Bi-entailment is defined as [(P -∗ Q) ∧ (Q -∗ P)], so it
  can be decomposed using the [iSplit] tactic.

  For hypotheses with multiple curried wands, it is again nesessary to
  specify how to split the Iris context during application. This can
  be done as [iApply ("Hyp" with "[H1 H2 H3] [H4 H5]")]. Each set of
  square brackets specifies the part of the context going to that
  argument.
  Hypotheses that fit arguments directly can be supplied directly
  without a square bracket to avoid trivial subgoals.

  Prove currying for the separation connectives.
*)
Lemma wand_adj (P Q R : iProp Σ) : (P -∗ Q -∗ R) ⊣⊢ (P ∗ Q -∗ R).
Proof.
  iSplit.
  (* exercise *)
Admitted.

(**
  Disjunctions [∨] are treated just like disjuctions in Coq.
  The introduction pattern [[ _ | _ ]] allows us to eliminate a disjunction,
  while the tactics [iLeft] and [iRight] let us introduce them.

  Prove that disjunction commutes.
*)
Lemma or_comm (P Q : iProp Σ) : Q ∨ P ⊢ P ∨ Q.
Proof.
  (* exercise *)
Admitted.

(**
  We can even prove the usual elimination rule for or-elemination
  written with separation. This version is, however, not very useful, as
  it does not allow the 2 cases to share resources.
*)
Lemma or_elim (P Q R : iProp Σ) : (P -∗ R) -∗ (Q -∗ R) -∗ P ∨ Q -∗ R.
Proof.
  (* Exercise start *)
  iIntros "H1 H2 [P|Q]".
  - iApply ("H1" with "P").
  - iApply ("H2" with "Q").
Qed.

(**
  The separation conjunction distributes over disjunction 
  (for the same reason as ordinary conjunction).
 *)
Lemma sep_or_distr (P Q R : iProp Σ) : P ∗ (Q ∨ R) ⊣⊢ P ∗ Q ∨ P ∗ R.
Proof.
  (* exercise *)
Admitted.

(**
  Iris has existential and universal quantifiers over any
  Coq type. Existential quantifiers are proved using the [iExists]
  tactic, using the same syntax as for [exists]. Elimination of
  existentials is done through the pattern "[%_ _]" or as part of a
  "(_&..&_)" with a "%" in front of the existential variable.
*)
Lemma sep_ex_distr {A} (P : iProp Σ) (Φ : A → iProp Σ) : (P ∗ ∃ x, Φ x) ⊣⊢ ∃ x, P ∗ Φ x.
Proof.
  (* exercise *)
Admitted.

(**
  Forall likewise works almost like in Coq. To introduce universally
  quantified variables, you can either use [iIntros (x y z)] or 
  [iIntros "%x %y %z"]. These patterns are interchangable.
  To specify parameters of hypotheses, we write [iApply ("H" $! x y z)].
*)
Lemma sep_all_distr {A} (P Q : A → iProp Σ) : (∀ x, P x) ∗ (∀ x, Q x) -∗ (∀ x, P x ∗ Q x).
Proof.
  (* exercise *)
Admitted.

End proofs.
