From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.

(* ################################################################# *)
(** * Basics of Iris *)

(* ================================================================= *)
(** * Introduction *)

(**
  In short, Iris is `higher-order concurrent separation logic
  framework'. That is quite a mouthful, so let us break it down.

  Firstly, the `framework' part means that Iris is not tied to any
  single programming language -- it consists of a base logic and can be
  instantiated with any language one sees fit.

  Secondly, a concurrent separation logic (CSL) is a program logic used
  to reason about concurrent languages by introducing a notion of
  resource ownership. The basic idea is that one must own a resource
  before one can interact with it, and ownership is generally exclusive,
  meaning that a concurrent program must decide how to separate and
  delegate its resources to its threads, so that they may perform their
  desired actions. So what is a resource? In Iris, we may define our own
  notion of resources by creating a so-called `resource algebra', which
  we discuss later. For languages with a heap, a canonical example of a
  resource is a heap fragment. Owning a resource then amounts to
  `controlling' a fragment of the heap, allowing one to read and update
  the associated locations.

  Finally, 'higher-order' refers to the fact that predicates may depend
  on other predicates. Being a program logic means that programs are
  proved correct with respect to some specification – a description of
  the programs behavior and interaction with resources. As programs are
  usually composed of other programs, we would want our specifications
  to be general enough to be useful in many different contexts. Having
  support for higher-order predicates means that program specifications
  can be parametrized by arbitrary propositions. This allows one to
  write specifications for libraries independently of their clients –
  the clients will instantiate the propositions to specialise the
  specification to fit their needs.

  In this file, we introduce basic separation logic in Iris.
*)

(* ================================================================= *)
(** ** Iris in Coq *)

(**
  Iris uses ssreflect, but we will not assume knowledge of ssreflect
  tactics. As such we will limit the use of ssreflect tactics whenever
  possible. However, ssreflect overrides the definition of [rewrite]
  changing its syntax and behaviour slightly. Notably:
  - No commas between arguments, meaning you have to write
    [rewrite H1 H2] instead of [rewrite H1, H2].
  - [rewrite -H] instead of [rewrite <-H]
  - Occurrences are written in front of the argument
    [rewrite {1 2 3}H] instead of [rewrite H at 1 2 3]
  - Rewrite can unfold definitions as [rewrite /def] which does the
    same as [unfold def]

  The type of propisitions in Iris is [iProp Σ]. All proofs in Iris are
  done in a context with a [Σ: gFunctors], used to specify available
  resources. The details of [Σ] will come later when we introduce
  resource algebras. For now, just remember to work inside a section with
  a [Σ] in its context. Keep in mind that [Σ] has type [gFunctors]
  plural, not [gFunctor] singular. There is a coercion from gFunctor to
  gFunctors, so everything will seem to work until [Σ] becomes relevant if
  you accidentally use [gFunctor].
*)
Section proofs.
Context {Σ: gFunctors}.

(**
  Iris propositions include many of the usual logical connectives such
  as conjunction [P ∧ Q]. As such, Iris uses a notation scope to
  overload the usual logical notation in Coq. This scope is delimited by
  [I] and bound to [iProp Σ]. Hence, you may need to wrap your
  propositions in [(_)%I] to use the notations.
*)
Fail Definition and_fail (P Q : iProp Σ) := P ∧ Q.
Definition and_success (P Q : iProp Σ) := (P ∧ Q)%I.

(**
  Iris defines two Coq propositions for proving Iris propositions:
  - [⊢ P] asks whether [P] holds with no assumptions
  - [P ⊢ Q] asks whether [Q] holds assuming [P]
  Note that there is no proposition allowing you to give multiple
  hypotheses, á la [P1, P2, P3 ⊢ Q]. This does not limit the
  expresiveness of the logic as assumptions can be curried or combined.
  The reason for this is due to the nature of separating conjunction
  which we introduce in a bit.

  Iris has a proof mode that works very similarly to the Coq proof mode.
  With this, it is possible to prove Iris propositions much like you
  would Coq propositions. To see this in action we will prove the
  statement [P ⊢ P] for all [P].
*)
Lemma asm (P : iProp Σ) : P ⊢ P.
Proof.
  (**
    First, we need to enter the Iris proof mode. To do this we can use
    the tactic [iStartProof]. However, most Iris tactics will
    automatically start the Iris proof mode for you, so this is not
    necessary and is usually omitted.
  *)
  iStartProof.
  (**
    The Iris proof mode has its own context of hypotheses, working much
    like Coq's proof mode. This context is called the spatial context
    and contains Iris propositions. All tactics working directly with
    the Iris logic are prefixed by an `i'. This allows Iris to reuse
    familiar tactic names. The Iris tactics use strings as identifiers,
    rather than Coq identifiers so that they can refer to the Iris
    context.

    To introduce hypotheses in Coq, one would normally use the tactic
    [intros H]. However, as we are working with the Iris logic, we
    instead use the tactic [iIntros "H"].
  *)
  iIntros "H".
  (**
    To finish the proof, one would normally use either [exact] or
    [apply]. So in Iris we use either [iExact] or [iApply].
  *)
  iApply "H".
Qed.

(* ================================================================= *)
(** ** Basic Separation Logic *)

(**
  The core connective in separation logics is the `separating
  conjunction', written [P ∗ Q], for propositions [P] and [Q]. The
  proposition [P ∗ Q] expresses ownership of the resources described by
  [P] and those by [Q], and, in particular, they describe separate
  resources. Separating conjunction differs from regular conjunction
  particularly in its introduction rule:

        P1 ⊢ Q1       P2 ⊢ Q2
        ----------------------
          P1 ∗ P2 ⊢ Q1 ∗ Q2

  That is, we must decide which of our owned resources we use to prove
  [Q1] and which we use to prove [Q2]. To see this in action, let us
  prove that separating conjunction is commutative.
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
    generally not possible to use [iSplit] to introduce [∗]. The
    [iSplit] tactic would duplicate the Iris context, and is therefore
    not available when the context is non-empty.
  *)
  Fail iSplit.
  (**
    Instead, Iris introduces the tactics [iSplitL] and [iSplitR]. These
    allow you to specify how you want to separate your resources to
    prove each of the subgoals. The hypotheses mentioned by [iSplitL]
    are given to the left subgoal, and the remaining to the right.
    Conversely for [iSplitR].
  *)
  iSplitL "HQ".
  - iApply "HQ".
  - iApply "HP".
Qed.

(**
  Separating conjuction has an analogue to implication, which, instead
  of introducing the antecedent to the assumpitons with conjunction,
  introduces it with separating conjunction. This connective is written
  as [P -∗ Q] and pronounced `magic wand' or simply `wand'. Separation
  is so widely used that [P -∗ Q] is treated specially; instead of
  writing [P ⊢ Q] we can write [P -∗ Q], with the [⊢] being implicit.
  That is, [⊢ P -∗ Q] is equivalent to [P -∗ Q].

  Writing a wand instead of a turnstile makes currying more natural.
  Here is the Iris version of modus ponens. It is provable using only
  [iIntros] and [iApply].
*)
Lemma modus_ponens (P Q : iProp Σ) : P -∗ (P -∗ Q) -∗ Q.
(* SOLUTION *) Proof.
  iIntros "P H".
  iApply "H".
  iApply "P".
Qed.

(**
  Just as with Coq tactics, Iris allows nesting of introduction
  patterns. In fact, like Coq, Iris supports patterns of the form
  [(H1 & .. & H2 & H3)] as a shorthand for [[H1 .. [H2 H3] ..]].

  Try to use an introduction with a pattern of parentheses to prove
  associativity for [∗].
*)
Lemma sep_assoc_1 (P Q R : iProp Σ) : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R.
(* SOLUTION *) Proof.
  iIntros "(P & Q & R)".
  iSplitR "R"; last iApply "R".
  iSplitL "P".
  - iApply "P".
  - iApply "Q".
Qed.

(**
  Manually splitting a separation can become tedious. To alleviate this,
  we can use the [iFrame] tactic. This tactic pairs up hypotheses with
  pieces of a separation sequence. Its full use is described in
  https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md?ref_type=heads#separation-logic-specific-tactics
*)
Lemma sep_comm_v2 (P Q : iProp Σ) : P ∗ Q ⊢ Q ∗ P.
Proof.
  iIntros "[HP HQ]".
  iFrame.
Qed.  

(**
  Bi-entailment of Iris propositions is denoted [P ⊣⊢ Q]. It is an
  equivalence relation and most connectives preserve this relation. It
  is encoded using the setoid library with the typeclass [Proper]. It is
  therefore possible to use the [rewrite] tactic inside the Iris proof
  mode. Bi-entailment is defined as [(P -∗ Q) ∧ (Q -∗ P)], so it can be
  decomposed using the [iSplit] tactic.

  For hypotheses with multiple curried wands, it is again necessary to
  specify how to split the Iris context during application. This can be
  done as [iApply ("Hyp" with "[H1 H2 H3] [H4 H5]")]. Each set of square
  brackets specifies the part of the context going to that argument.
  Hypotheses that fit arguments directly can be supplied directly
  without a square bracket to avoid trivial subgoals.

  Prove currying for the separation connectives.
*)
Lemma wand_adj (P Q R : iProp Σ) : (P -∗ Q -∗ R) ⊣⊢ (P ∗ Q -∗ R).
(* BEGIN SOLUTION *)
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
(* END SOLUTION BEGIN TEMPLATE
Proof.
  iSplit.
  (* exercise *)
Admitted.
END TEMPLATE *)

(**
  Disjunctions [∨] are treated just like disjunctions in Coq. The
  introduction pattern [[ _ | _ ]] allows us to eliminate a disjunction,
  while the tactics [iLeft] and [iRight] let us introduce them.

  Prove that disjunction commutes.
*)
Lemma or_comm (P Q : iProp Σ) : Q ∨ P ⊢ P ∨ Q.
(* SOLUTION *) Proof.
  iIntros "[Q | P]".
  - by iRight.
  - by iLeft.
Qed.

(**
  We can even prove the usual elimination rule for or-elimination
  written with separation. This version is, however, not very useful, as
  it does not allow the two cases to share resources.
*)
Lemma or_elim (P Q R : iProp Σ) : (P -∗ R) -∗ (Q -∗ R) -∗ P ∨ Q -∗ R.
(* SOLUTION *) Proof.
  iIntros "H1 H2 [P|Q]".
  - iApply ("H1" with "P").
  - iApply ("H2" with "Q").
Qed.

(**
  Separating conjunction distributes over disjunction (for the same
  reason as ordinary conjunction). *)
Lemma sep_or_distr (P Q R : iProp Σ) : P ∗ (Q ∨ R) ⊣⊢ P ∗ Q ∨ P ∗ R.
(* BEGIN SOLUTION *)
Proof.
  iSplit.
  (* Exercise start *)
  - iIntros "[P [Q | R]]".
    + iLeft. iFrame.
    + iRight. iFrame.
  - iIntros "[[P Q] | [P R]]".
    + iFrame.
    + iFrame.
Qed.
(* END SOLUTION BEGIN TEMPLATE
Proof.
  (* exercise *)
Admitted.
END TEMPLATE *)

(**
  Iris has existential and universal quantifiers over any Coq type.
  Existential quantifiers are proved using the [iExists] tactic, using
  the same syntax as for [exists]. Elimination of existentials is done
  through the pattern "[%_ _]" or as part of a "(_&..&_)" with a "%" in
  front of the existential variable.
*)
Lemma sep_ex_distr {A} (P : iProp Σ) (Φ : A → iProp Σ) : (P ∗ ∃ x, Φ x) ⊣⊢ ∃ x, P ∗ Φ x.
(* SOLUTION *) Proof.
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
  Forall likewise works almost like in Coq. To introduce universally
  quantified variables, you can either use [iIntros (x y z)] or 
  [iIntros "%x %y %z"]. These patterns are interchangeable.
  To specify the parameters of hypotheses, we write [iApply ("H" $! x y z)].
*)
Lemma sep_all_distr {A} (P Q : A → iProp Σ) : (∀ x, P x) ∗ (∀ x, Q x) -∗ (∀ x, P x ∗ Q x).
(* SOLUTION *) Proof.
  iIntros "[P Q] %x".
  by iSplitL "P".
Qed.

End proofs.
