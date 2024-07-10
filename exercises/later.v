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
  The later modality is monotone meaning that if we know [P ⊢ Q], then
  we can also conclude [▷ P ⊢ ▷ Q]. This is captured by the [iNext]
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
  The later modality weakens propositions; owning resources now is
  stronger than owning them later. In other words, [P ⊢ ▷ P]. This means
  that we can always remove a later from the goal, regardless of whether
  our hypotheses have a later.
*)

Lemma later_weak (P : iProp Σ) : P ⊢ ▷ P.
Proof.
  iIntros "HP".
  iNext.
  done.
Qed.

(** 
  The later modality distributes over [∧], [∨], [∗], and is preserved
  by [∃] and [∀]. This means that we can destruct these constructs
  regardless of being prefaced by any laters.
*)

Lemma later_sep (P Q : iProp Σ) : ▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q.
Proof.
  iSplit.
  - iIntros "[HP HQ]".
    iFrame.
  - iIntros "[HP HQ] !>".
    iFrame.
Qed.

(**
  As a consequence of monotonicity, weakening, and distribution over
  [∗], the [iNext] tactic can simply ignore hypotheses in the context
  that do not have a later on them.
*)

Lemma later_impl (P Q : iProp Σ) : P ∗ ▷ (P -∗ Q) -∗ ▷ Q.
Proof.
  (* exercise *)
Admitted.

(* ================================================================= *)
(** ** Tying Later to Program Steps *)

(**
  A somewhat important clarification is that the later modality exists
  independently of the specific language Iris is instantiated with; the
  later modality is part of the Iris base logic. However, when
  instantiating Iris with a language, the obvious choice is to tie a
  single [▷] to a single program step. This is also the choice that has
  been made for HeapLang – every time we use one of the `wp' tactics to
  symbolically execute a single step, we let time tick one unit forward,
  stripping away a single [▷] from our hypotheses.

  To see this in action, let us look at a simple program: [1 + 2 + 3].
  This program takes two steps to evaluate, so we can prove that if a
  proposition holds after two steps, then it will hold after the program
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
  The reason this works is that under the hood of [WP], there is a later
  for every step of the program. Thus, the `wp' tactics can use the
  properties mentioned in the previous section to remove laters from the
  context, similarly to [iNext].
*)

(* ================================================================= *)
(** ** Löb Induction *)

(* TODO: Update section. *)

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
