From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang proofmode notation.

(*########## CONTENTS PLAN ##########
- MOTIVATE PERSISTENTLY FROM POINTS-TO AND CONCURRENCY: READ ONLY MEMORY
- TALK ABOUT PERSISTENCY IN GENERAL (reuse existing tutorial)
- MENTION THAT HT AND WP ARE PERSISTENT
  + SHOW EXAMPLE OF USEFULNESS (two invocations of some function)
- INTRODUCE PERSISTENT POINTS-TO PREDICATE (for read-only memory)
- USEFULNESS FOR CONCURRENT PROGRAMS EXAMPLE
- PRESERVED BY QUANTIFICATIONS AND CONNECTIVES
#####################################*)

Section proofs.
Context `{!heapGS Σ}.

(**
  Thus far we've seen the pure context (the Coq context) and the spatial
  context. The Iris proofmode has a third context, called the
  intuitionistic context or (for [iProp]) the persistent context. These
  are propositions that act like propositions in an intuitionistic
  logic. Namely, they are reusable. These propositions need not,
  however, be pure as their validity can still depend on resources. Just
  like the pure modality, we also have a persistently modality [□ P]. It
  turns an arbitrary Iris proposition into a weaker persistent
  proposition. Persistent propositions are thus those [P] such that [P ⊢
  □ P]. Iris identifies these propositions using the typeclass
  [Persistent]. In fact, all pure propositions are persistent.
*)
Lemma pers_ex (P Q : iProp Σ) `{!Persistent P} : P -∗ Q -∗ P ∗ Q.
Proof.
  (**
    We are allowed to put persistent hypotheses into the spatial
    context. This will make the proofmode treat the hypothesis as
    though it was not persistent.
  *)
  iIntros "HP HQ".
  (**
    The introduction pattern "#_" allows us to place a hypothesis into
    the persistent context.
  *)
  iDestruct "HP" as "#HP".
  iSplitR.
  - (**
      Notice that even though we asked Iris to move all hypotheses
      into the second subgoal, we still kept "HP".
    *)
    iApply "HP".
  - (** And "HP" is also present in this subgoal *)
    iApply "HQ".
Qed.

Lemma pers_sep (P : iProp Σ) `{!Persistent P} : P ⊢ P ∗ P.
Proof.
  (* exercise *)
Admitted.

(**
  Persistent propositions satisfy a lot of nice properties,
  simply by being duplicable [P ⊢ P ∗ P]
  For example, [P ∧ Q] and [P ∗ Q] coincide, when either [P] or [Q] is persistent.
  Likewise, [P → Q] and [P -∗ Q] coincide, when [P] is persistent.
*)
Check bi.persistent_and_sep.
Check bi.impl_wand.

(** The Iris proofmode knows these facts and allows 
  [iSplit] to introduce [∗] when one of its arguments is persistent. 
*)


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

End proofs.
