From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang proofmode notation.

(*########## CONTENTS PLAN ##########
- MOTIVATE PERSISTENTLY FROM POINTS-TO AND CONCURRENCY: READ ONLY MEMORY
- TALK ABOUT PERSISTENCY IN GENERAL (reuse existing tutorial)
- PRESERVED BY QUANTIFICATIONS AND CONNECTIVES
- MENTION THAT HT ARE PERSISTENT
  + SHOW EXAMPLE OF USEFULNESS (two invocations of some function)
- INTRODUCE PERSISTENT POINTS-TO PREDICATE (for read-only memory)
- USEFULNESS FOR CONCURRENT PROGRAMS EXAMPLE
#####################################*)

(* ################################################################# *)
(** * Persistently *)

Section persistently.
Context `{!heapGS Σ}.

(* ================================================================= *)
(** ** Introduction *)

(**
  In separation logic, propositions are generally not duplicable. This
  is because resources are generally exclusive. However, resources do
  not _have_ to be exclusive. A great example of this is `read only
  memory'. There is no danger in letting many threads access the same
  location simultaneously if they can only read from it. Hence, it would
  not make sense to require that ownership of those locations be
  exclusive. Motivated by this, we introduce a new modality denoted the
  persistently modality, written [□ P], for propositions [P]. The
  proposition [□ P] describes the same resources as [P], except it does
  not claim that the resources are exclusive – hence [□ P] can be
  duplicated. Persistent propositions hence act like propositions in an
  intuitionistic logic, which is why they are also sometimes referred to
  as intuitionistic.

  A propositions is persistent when [P ⊢ □ P]. That is, assuming [P], we
  need to show that [P] does not rely on any exclusive resources.
  Persistency is preserved by most connectives, so proving that a
  proposition is persistent is usually a matter of showing that the
  mentioned resources are shareable. Which resources are shareable
  depends on the specific notions of resources being used. For the
  resource of heaps, a location can be marked as read-only, making it
  shareable. The associated points-to predicate hence becomes
  persistent. We will see an example of this later.

  Propositions that do not rely on resources altogether are trivially
  persistent. We have already given those types of propositions a name:
  _pure_. This is also why we do not have to split the non-spatial
  context when using [iSplitL]/[iSplitR]; all pure propositions are
  persistent, hence duplicable.

  Of course, not all persistent propositions are pure (e.g. persistent
  points-to predicates). Thus, the Iris Proof Mode provides a third
  context just for persistent propositions, called the persistent
  context. Pure propositions can go in all three contexts. Persistent
  propositions can go in the spatial context or the persistent context.
  And all other propositions are limited to the spatial context only.
  Iris uses the typeclass [Persistent] to identify persistent
  propositions.
*)

Lemma pers_context (P Q : iProp Σ) `{!Persistent P} : P -∗ Q -∗ P ∗ Q.
Proof.
  (**
    The introduction pattern "#_" allows us to place a persistent
    hypothesis into the persistent context.
  *)
  iIntros "#HP HQ".
  iSplitR "HQ".
  (**
    Notice that after splitting, both the non-spatial and persistent
    contexts are duplicated. In particular, [HP] is available in both
    subgoals.
  *)
  - iApply "HP".
  - iApply "HQ".
Qed.

(**
  Note that all propositions in the spatial context are treated as
  non-persistent, regardless of whether they are persistent.
*)

Lemma not_in_pers_context (P Q : iProp Σ) `{!Persistent P} : P -∗ Q -∗ P ∗ Q.
Proof.
  (** We introduce [HP] to the spatial context. *)
  iIntros "HP HQ".
  iSplitR "HQ".
  (** [HP] is no longer duplicated. *)
  - iApply "HP".
  - iApply "HQ".
Qed.

(** Exercise: prove that persistent propositions are duplicable. *)

Lemma pers_dup (P : iProp Σ) `{!Persistent P} : P ⊢ P ∗ P.
Proof.
  (* exercise *)
Admitted.

(**
  Persistent propositions satisfy a lot of nice properties, simply by
  being duplicable [P ⊢ P ∗ P] For example, [P ∧ Q] and [P ∗ Q]
  coincide, when either [P] or [Q] is persistent. Likewise, [P → Q] and
  [P -∗ Q] coincide, when [P] is persistent.
*)
Check bi.persistent_and_sep.
Check bi.impl_wand.

(**
  The Iris Proof Mode knows these facts and allows [iSplit] to introduce
  [∗] when one of its arguments is persistent. 
*)


(* ================================================================= *)
(** ** Proving Persistency *)

(**
  To prove a proposition [□ P], we have to prove [P] without assuming
  any exclusive resources. In other words, we have to throw away the
  spatial context when proving [P].
*)

Lemma pers_intro (P Q : iProp Σ) `{!Persistent P} : P ∗ Q ⊢ □ P.
Proof.
  iIntros "[#HP HQ]".
  (** 
    The [iModIntro] tactic introduces a modality in the goal. In this
    case, since the modality is a [□], it throws away the spatial
    context.
  *)
  iModIntro.
  iApply "HP".
Qed.

(**
  Since the only difference between [□ P] and [P] is that the former
  does not claim the resources are exclusive, it follows that the
  persistently modality is idempotent.
*)

Lemma pers_idemp (P : iProp Σ) : □ □ P ⊣⊢ □ P.
Proof.
  iSplit.
  - iIntros "HP".
    (** 
      Iris already knows that [□] is idempotent, so it automatically
      removes all persistently modalities from a proposition when adding
      it to the persistent context. One may think of all propositions in
      the persistent context as having an implicit [□] in front.
    *)
    iDestruct "HP" as "#HP".
    done.
  - iIntros "#HP".
    (** Similarly, we do not have to introduce [□] before proving it. *)
    done.
Qed.

(**
  Only propositions that are instances of the [Persistent] typeclass can
  be added to the persistent context. As with the typeclasses for pure,
  the [Persistent] typeclass can automatically identify most persistent propositions.
*)

Lemma pers_sep (P Q : iProp Σ) : □ P ∗ □ Q ⊣⊢ □ (P ∗ Q).
Proof.
  iSplit.
  - (** 
      The [Persistent] typeclass detects that [□ P ∗ □ Q] is persistent. 
    *)
    iIntros "#HPQ".
    iDestruct "HPQ" as "[#HP #HQ]".
    iModIntro.
    (** 
      By default, [iFrame] will not frame propositions from the
      persistent context. To make it do so, we have to give it the
      argument "#".
    *)
    iFrame "#".
  - (* exercise *)
Admitted.

(**
  For simple predicates, such as [myPredicate] below, the [Persistent]
  typeclass can automatically infer that it is persistent. However, we
  can still manually make propositions instances of [Persistent].
*)

Definition myPredicate (x : val) : iProp Σ := ⌜x = #5⌝.

Local Instance myPredicate_persistent x : Persistent (myPredicate x).
Proof.
  (**
    As mentioned in the beginning of the chapter, a proposition [P] is
    persistent when [P ⊢ □ P]. This is almost what [Persistent] requires
    us to prove.
  *)
  rewrite /Persistent.
  (**
    Our actual goal is of the form [P ⊢ <pers> P]. Technically, there is
    a small discrepancy between [□] and [<pers>], but we will ignore
    that here.

    As pure propositions are persistent, we quite easily prove this.
  *)
  rewrite /myPredicate.
  iIntros "#H".
  iModIntro.
  iApply "H".
Qed.

(** Iris is quite smart, so we do not have to spell out the proof. *)
Local Instance myPredicate_persistent' x : Persistent (myPredicate x).
Proof. apply _. Qed.

(** 
  For more complicated predicates, such as ones defined as a fixpoint,
  [Persistent] cannot automatically infer its persistence. The following
  predicate asserts that all values in a given list is equal to [5].
*)

Fixpoint myPredFix (xs : list val) : iProp Σ :=
  match xs with
  | [] => True
  | x :: xs' => ⌜x = #5⌝ ∗ myPredFix xs'
  end.

(**
  This predicate only consists of pure propositions, so it should of
  course be persistent, but when we try to add it to the persistent
  context, Iris complains that it is not `intuitionistic' (i.e.
  persistent).
*)
Lemma first_is_5 (x : val) (xs : list val) :
  myPredFix (x :: xs) -∗ ⌜x = #5⌝ ∗ myPredFix (x :: xs).
Proof.
  Fail iIntros "#H".
Abort.

(**
  For such predicates, we have to prove that it is persistent manually,
  as we did for [myPredicate] above.
*)

Local Instance myPredFix_persistent xs : Persistent (myPredFix xs).
Proof.
  (** We prove it by induction in [xs]. *)
  induction xs as [| x xs' IH ]. 
  - (** [True] is persistent *)
    apply _.
  - (** 
      By IH, [myPredFix xs'] is persistent. As ⌜x = #5⌝ is also persistent,
      it follows that [myPredFix (x :: xs')] is persistent.
    *)
    apply _.
Qed.

(** Now, Iris recognises [myPredFix] as persistent. *)

Lemma first_is_5 (x : val) (xs : list val) :
  myPredFix (x :: xs) -∗ ⌜x = #5⌝ ∗ myPredFix (x :: xs).
Proof.
  iIntros "#H".
  (** 
    [iPoseProof] is similar to [iDestruct], but it does not throw away
    the hypothesis being destructed, if it is persistent.
  *)
  iPoseProof "H" as "[Hx _]".
  iFrame "H Hx".
Qed.

(* ================================================================= *)
(** ** Examples of Persistent Propositions *)

(** 
  TODO: intro.
*)

(* ----------------------------------------------------------------- *)
(** *** Hoare Triples *)

(* TODO: do *)

(* TODO: include following exercise *)

Example adder_client (inc : val) : expr :=
  let: "z1" := inc #0 in
  let: "z2" := inc "z1" in
  "z2".

Lemma adder_client_spec (inc : val) :
  {{{ 
    ∀(z : Z), {{{ True }}} inc #z {{{ v, RET v; ⌜v = #(z + 1)⌝}}}
  }}} 
    adder_client inc
  {{{ v, RET v; ⌜v = #2⌝ }}}.
Proof.
  (* exercise *)
Admitted.

(**
  All top level lemmas are persistent and can hence be reused.
*)

(* ----------------------------------------------------------------- *)
(** *** Persistent Points-to *)

(* TODO: do *)



End persistently.
