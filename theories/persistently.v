From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.

Section proofs.
Context {Σ : gFunctors}.

(**
  Thus far we've seen the pure context (the coq context) and the
  spatial context. Iris proofmode has a 3rd context, called the
  inituitionistic context or (for [iProp]) persistent context.
  These are proposisitions that act like propositions in an
  inituitionistic logic. Namely, they are reusable. These propositions
  need not however be pure as they can still depend on resurces. Just
  like the pure modality, we also have a persistently modality [□ P].
  It turns arbitrary Iris propositions into a stronger persistent
  proposition. Persistent proposistions are thus those [P] such that
  [P ⊢ □ P]. Iris identifies these proposisition using the typeclass
  [Persistent]. In fact, all pure propositions are persistent.
*)
Lemma pers_ex (P Q : iProp Σ) `{!Persistent P} : P -∗ Q -∗ P ∗ Q.
Proof.
  (**
    We are allowed to put persistent hypotheses into the spacial
    context. This will make the proofmode treat the hypothesis as
    though it wasn't persistent.
  *)
  iIntros "HP HQ".
  (**
    The introduction pattern "#_" allows us to place a hypotheses into
    the persistent context.
  *)
  iDestruct "HP" as "#HP".
  iSplitR.
  - (**
      Notice that event though we asked Iris to move all hypotheses
      into the second subgoal, we still kept "HP".
    *)
    iApply "HP".
  - (** And "HP" is also present in this subgoal *)
    iApply "HQ".
Qed.

Lemma pers_sep (P : iProp Σ) `{!Persistent P} : P ⊢ P ∗ P.
Proof.
  (* Exercise start *)
  iIntros "#P".
  iSplit.
  - done.
  - done.
Qed.

(**
  Persistent propositions satisfy a lot of nice proporties simply by being duplicable [P ⊢ P ∗ P]
  For example, [P ∧ Q] and [P ∗ Q] coincide, when either [P] or [Q] is persistent.
  Likewise, [P → Q] and [P -∗ Q] coincide, when [P] is persistent.
*)
Check bi.persistent_and_sep.
Check bi.impl_wand.

(** Iris proofmode knows these facts, and allows [iSplit] to introduce [∗] when one of its arguements are persistent. *)


End proofs.
