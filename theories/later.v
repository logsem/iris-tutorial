From iris.heap_lang Require Import lang proofmode notation.

(*########## CONTENTS PLAN ##########
- TIMELESS PROPOSITIONS AND STRIPPING LATERS
  + USUALLY DONE WHEN INTRODUCING PROPOSITIONS VIA '>'
  + SHOW EXAMPLES
- EXPAND ON LÖB INDUCTION
#####################################*)

(* ################################################################# *)
(** * Later *)

Section later.
Context `{!heapGS Σ}.

(* ================================================================= *)
(** ** Basics *)

(**
  Iris is a step-indexed logic, meaning it has a built-in notion of
  time. This can be expressed with the later modality [▷ P] signifying
  that [P] holds after one time step. With the reading of propositions
  as describing owned resources, [▷ P] asserts that we will own the
  resources described by [P] after one time step.

  The later modality is used quite extensively in Iris. We have already
  seen that it is used to define Hoare triples, but it has many more
  uses. For instance, it is a prime tool to reason about recursive
  programs. It can be used to write specifications that capture the
  minimum number of steps taken by a program. It is also an integral
  part of working with invariants, which we introduce in a later
  chapter.
*)

(**
  The later modality is monotone meaning that if we know that [P ⊢ Q],
  then we can also conclude [▷ P ⊢ ▷ Q]. This is captured by the [iNext]
  tactic, which introduces a later, while stripping laters from our
  hypotheses.
*)

Lemma later_mono (P Q : iProp Σ) : (Q ⊢ P) -> (▷ Q ⊢ ▷ P).
Proof.
  intros HQP.
  iIntros "HQ".
  iNext.
  by iApply HQP.
Qed.

(**
  The [iNext] tactic is actually a specialisation of the more general
  [iModIntro] tactic, which works with all modalities. The [iModIntro]
  tactic can be invoked with the introduction pattern ["!>"], making it
  less verbose to handle the later modality.
*)

Lemma later_mono' (P Q : iProp Σ) : (Q ⊢ P) -> (▷ Q ⊢ ▷ P).
Proof.
  intros HQP.
  iIntros "HQ !>".
  by iApply HQP.
Qed.

(**
  TODO: Finish rest of file.
  Furthermore, later satisfies [P ⊢ ▷ P] and [▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q].
*)

Lemma later_weak (P : iProp Σ) : P ⊢ ▷ P.
Proof.
  iIntros "HP".
  iNext.
  done.
Qed.

(**
  These rules allow the tactics to ignore hypotheses in the context that
  do not have a later on them.
*)

Lemma later_impl (P Q : iProp Σ) : P ∗ ▷ (P -∗ Q) -∗ ▷ Q.
(* SOLUTION *) Proof.
  iIntros "[HP HQ] !>".
  iApply "HQ".
  iApply "HP".
Qed.


(* ================================================================= *)
(** ** Tying Later to Program Steps *)

(**
  A somewhat important clarification is that the later modality exists
  independently of the specific language Iris is instantiated with; the
  later modality is part of the Iris base logic. However, when
  instantiating Iris with a language, a common choice is to tie a single
  [▷] to a single program step.

  These time steps are linked to the execution steps of our programs in
  HeapLang. Every time we use one of the wp tactics, we let time tick
  forward. To see this, let us look at a simple program: [1 + 2 + 3].
  This program takes two steps to evaluate, so we can prove that if a
  proposition holds after 2 steps, then it will hold after the program
  has terminated.
*)
Lemma take_2_steps (P : iProp Σ) : ▷ ▷ P -∗ WP #1 + #2 + #3 {{_, P}}.
Proof.
  iIntros "HP".
  wp_pure.
  wp_pure.
  done.
Qed.

(**
  This works because later is monotone. Inside WP there is a later for
  every step of the program, so the wp tactics can use monotonicity to
  remove laters from the context.
*)

(* ================================================================= *)
(** ** Timeless Propositions *)

Lemma later_timeless_strip (P Q : iProp Σ) `{!Timeless P}:
  (P ⊢ ▷ Q) ->
  (▷ P ⊢ ▷ Q).
Proof.
  intros HPLQ.
  iIntros ">HP".
  by iApply HPLQ.
Qed.

Lemma later_strip_fail (P Q : iProp Σ) :
  (P ⊢ ▷ Q) ->
  (▷ P ⊢ ▷ Q).
Proof.
  intros HPLQ.
  Fail iIntros ">HP".
Abort.

Lemma later_store (l : loc) (v : val) :
  {{{ ▷ (l ↦ v) }}} #l <- #4 {{{ w, RET w; l ↦ #4 }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  wp_store.
  by iApply "HΦ".
Qed.

Lemma later_store' (l : loc) (v : val) :
  {{{ ▷ (l ↦ v) }}} #l <- #4 {{{ w, RET w; l ↦ #4 }}}.
Proof.
  iIntros (Φ) "Hl HΦ".
  wp_store.
  by iApply "HΦ".
Qed.


(* ================================================================= *)
(** ** Löb Induction *)

(**
  With this later modality, we can do a special kind of induction,
  called Löb induction. The formal statement is `□ (▷ P -∗ P) -∗ P`.
  Intuitively, this is a form of course of value induction, where we
  say that if given that `P` holds for executions strictly smaller than n
  steps we can prove that `P` holds for n steps, then `P` holds for
  all steps.

  We can use this principle to prove many properties of recursive
  programs. To see this in action, we will define a simple recursive
  program that increments a counter.
*)

Definition count : val :=
  rec: "count" "x" := "count" ("x" + #1).

(**
  This program never terminates, as it will keep calling itself with
  larger and larger inputs. To show this we pick the postcondition
  [False]. We can now use Löb induction, along with [wp_rec], to prove
  this specification.
*)
Lemma count_spec (x : Z) : ⊢ WP count #x {{_, False}}.
Proof.
  iLöb as "IH" forall (x).
  wp_rec.
  wp_pure.
  iApply "IH".
Qed.

End later.
