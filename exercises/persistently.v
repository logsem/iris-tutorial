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
  location simultaneously, if they can only read from it. Hence, it
  would not make sense to require that ownership of those locations be
  exclusive. Motivated by this, we introduce a new modality denoted the
  persistently modality, written [□ P], for propositions [P]. The
  proposition [□ P] describes the same resources as [P], except it does
  not claim that the resources are exclusive – hence [P] can be
  duplicated. Persistent propositions hence act like propositions in an
  intuitionistic logic, which is why they are also sometimes referred to
  as intuitionistic.

  A propositions is persistent when [P ⊢ □ P]. That is, assuming [P], we
  need to show that [P] does not rely on any exclusive resources.
  Persistency is preserved by most connectives, so proving that a
  proposition is persistent is usually a matter of showing that the
  mentioned resources are shareable. Which resources are shareable
  depends on the specific notions of resources being used. For the
  resource of heaps, locations that are never written to after a certain
  point can be marked as shareable, and the associated points-to
  predicate hence becomes persistent. We will see an example of this
  later.

  Propositions that do not rely on resources altogether are trivially
  persistent. We have already given those types of propositions a name:
  _pure_. This is also why we do not have to split the non-spatial context
  when using [iSplitL]/[iSplitR]; all pure propositions are persistent,
  hence duplicable.

  Of course, not all persistent propositions are pure. Thus, the Iris
  Proof Mode provides a third context just for persistent propositions,
  called the persistent context. Pure propositions can go in all three
  contexts. Persistent propositions can go in the spatial context or the
  persistent context. And all other propositions are limited to the
  spatial context only. Iris uses the typeclass [Persistent] to identify
  persistent propositions.
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
  The Iris Proof Mode knows these facts and allows [iSplit] to
  introduce [∗] when one of its arguments is persistent. 
*)
(* TODO: Example here *)


(* ================================================================= *)
(** ** Proving Persistency *)

(* TODO: examples with preserving connectives *)

(* TODO: include following exercise. Write some explaining text for proven
part of exercise. *)

Lemma pers_sep (P Q : iProp Σ) : □P ∗ □Q ⊣⊢ □(P ∗ Q).
Proof.
  iSplit.
  - iIntros "#HPQ".
    iDestruct "HPQ" as "[#HP #HQ]".
    iModIntro.
    iFrame "#".
  - (* exercise *)
Admitted.


(* TODO: Instance of Persistent for custom predicates (example) *)

(* ================================================================= *)
(** ** Examples of Persistent Propositions *)

(* ----------------------------------------------------------------- *)
(** *** Pure Propositions *)

(* TODO: do *)

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
