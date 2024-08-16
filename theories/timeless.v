From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.

(* ################################################################# *)
(** * Timeless Propositions *)

(* ================================================================= *)
(** ** Definition and Uses *)

Section timeless.
Context `{!heapGS Σ}.

(**
  A large class of propositions do not depend on time; they are either
  always true or always false. Take for instance equalities –
  [2 + 2 = 4] is always true. We call such propositions timeless. All
  pure propositions are timeless and ownership of resources is timeless
  if the resource comes from a resource algebra (this includes points-to
  predicates). Further, timelessness is preserved by most connectives.
  As a rule of thumb, a predicate is timeless if
  - it does not contain a later
  - it does not mention an invariant
  - it is first-order

  Naively, one might assume that if [P] is timeless, then [▷ P ⊢ P].
  However, together with Löb induction, this would actually imply that
  [P] is [True]. Instead, the power of timeless propositions comes from
  the rule: [▷ P ⊢ |={⊤}=> P], whenever [P] is timeless. This rule
  allows us to strip laters from timeless propositions whenever the goal
  contains a fancy update modality.

  To identify timeless propositions, Iris uses the typeclass [Timeless].
*)

Lemma later_timeless_fup (P : iProp Σ) `{!Timeless P} :
  ▷ P ⊢ |={⊤}=> P.
Proof.
  iIntros "HP".
  (**
    As [▷] is a modality, we can use the [iMod] tactic to strip it from
    our hypothesis. In this case, this is allowed as the goal contains a
    fancy update modality and [P] is timeless.
  *)
  iMod "HP".
  done.
Qed.

(**
  As usual, we can use the notation ">" to invoke [iMod]. This is how we
  will usually invoke [iMod] to strip laters. The above proof can hence
  be shortened as follows.
*)

Lemma later_timeless_fup' (P : iProp Σ) `{!Timeless P} :
  ▷ P ⊢ |={⊤}=> P.
Proof.
  iIntros ">HP".
  done.
Qed.

(**
  We may _always_ add a fancy update modality in front of a WP
  (concretely with the [fupd_wp] lemma), so if the goal is a weakest
  precondition, we can remove laters from timeless propositions in our
  context.
*)

Lemma later_store (l : loc) (v : val) :
  {{{ ▷ (l ↦ v) }}} #l <- #4 {{{ w, RET w; l ↦ #4 }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  wp_store.
  by iApply "HΦ".
Qed.

(**
  Since the points-to predicate is well supported, we do not actually
  have to remove the later manually; the tactics work even when the
  predicate has a later.
*)

Lemma later_store' (l : loc) (v : val) :
  {{{ ▷ (l ↦ v) }}} #l <- #4 {{{ w, RET w; l ↦ #4 }}}.
Proof.
  iIntros (Φ) "Hl HΦ".
  wp_store.
  by iApply "HΦ".
Qed.

(**
  The last scenario we mention is when the goal contains a later. In
  this case, we may remove laters from timeless hypothesis, without
  removing the later from the goal.
*)

Lemma later_timeless_strip (P Q : iProp Σ) `{!Timeless P} :
  (P -∗ ▷Q) ∗ ▷ P ⊢ ▷ Q.
Proof.
  iIntros "[HPQ >HP]".
  by iApply "HPQ".
Qed.

(* ================================================================= *)
(** ** Timeless Propositions and Invariants *)

(**
  Timeless propositions are especially useful in connection with
  invariants. Recall from the invariants chapter that, when we open an
  invariant, [inv N P], we only get the resources _later_, [▷P]. Often,
  however, we require the resources now. Consider the following example.
*)

Lemma inv_timeless (l : loc) (w : val) (P : iProp Σ) (N : namespace) :
  {{{ inv N (⌜w = #5⌝ ∗ P) ∗ (l ↦ w) }}}
    CAS #l #5 #6
  {{{ v, RET v; l ↦ #6 }}}.
Proof.
  iIntros (Φ) "[#Hinv Hl] HΦ".
  (**
    To prove that the CAS succeeds, we need to know that [w] equals [5].
    Thus, we must open the invariant.
  *)
  wp_bind (CmpXchg #l #5 #6)%E.
  iInv "Hinv" as "[Heq HP]".
  (**
    Opening the invariant only gives us that [w] equals [5] later.
    However, as pure propositions are timeless, we can strip the later.
  *)
  iMod "Heq" as "%Heq".
  rewrite Heq.
  (** Now we can prove that the CAS succeeds. *)
  wp_cmpxchg_suc.
  iSplitL "HP"; first by iFrame.
  iModIntro.
  wp_pures.
  by iApply "HΦ".
Qed.

(**
  When opening invariants, we usually strip laters from timeless parts
  of the invariant immediately.
*)

Lemma inv_timeless' (l : loc) (w : val) (P : iProp Σ) (N : namespace) :
  {{{ inv N (⌜w = #5⌝ ∗ P) ∗ (l ↦ w) }}}
    CAS #l #5 #6
  {{{ v, RET v; l ↦ #6 }}}.
Proof.
  iIntros (Φ) "[#Hinv Hl] HΦ".
  wp_bind (CmpXchg #l #5 #6)%E.
  (**
    Open the invariant, strip the later from the equality (achieved by
    [">"]), and rewrite with the equality (achieved by ["->"]).
  *)
  iInv "Hinv" as "[>-> HP]".
  wp_cmpxchg_suc.
  iSplitL "HP"; first by iFrame.
  iModIntro.
  wp_pures.
  by iApply "HΦ".
Qed.

End timeless.
