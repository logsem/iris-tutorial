From iris.heap_lang Require Import lang proofmode notation.

(*########## CONTENTS PLAN ##########
  - BASIC DESCRIPTION OF TIMELESS PROPOSITIONS
  - STRIPPING LATERS AND FUP (later_timeless_fup)
    + USUALLY DONE WHEN INTRODUCING PROPOSITIONS VIA '>'
  - SHOW EXAMPLES
  - EXAMPLE WITH INVARIANTS
#####################################*)

(* ################################################################# *)
(** * Timeless Propositions *)

Section timeless.
Context `{!heapGS Σ}.

(** 
  A large class of propositions do not depend on time; they are either
  always true or always false. Take for instance equalities – [2 + 2 =
  4] is always true. We call such propositions timeless. All pure
  propositions are timeless and ownership of resources is timeless (e.g.
  [l ↦ 5]). Further, timelessness is preserved by most connectives. As a
  rule of thumb, a predicate is timeless if
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
    The [iMod] tactic removes a modality from a hypothesis if the goal
    permits. In this case, since the goal has a fancy update modality,
    we can remove the later.
  *)
  iMod "HP".
  done.
Qed.

(**
  Similarly to how "!>" invokes [iModIntro], the pattern ">" invokes
  [iMod]. The above proof can hence be shortened as follows.
*)

Lemma later_timeless_fup' (P : iProp Σ) `{!Timeless P} :
  ▷ P ⊢ |={⊤}=> P.
Proof.
  iIntros ">HP".
  done.
Qed.

(**
  We may _always_ add a fancy update in front of a WP (concretely with
  the [fupd_wp] lemma), so if the goal is a weakest precondition, we
  can remove laters from timeless propositions in our context.
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
  (P ⊢ ▷ Q) →
  (▷ P ⊢ ▷ Q).
Proof.
  intros HPLQ.
  iIntros ">HP".
  by iApply HPLQ.
Qed.

(* TODO: EXAMPLE WITH INVARIANTS *)

End timeless.
