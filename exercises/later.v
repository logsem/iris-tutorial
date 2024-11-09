From iris.heap_lang Require Import lang proofmode notation.

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
  uses. For instance, it is a prime tool for reasoning about recursive
  programs. It can be used to write specifications that capture the
  minimum number of steps taken by a program. It is also an integral
  part of working with invariants, which we introduce in a later
  chapter.
*)

(**
  The later modality is monotone, meaning that if we know [P ⊢ Q], then
  we can also conclude [▷ P ⊢ ▷ Q]. In words, if we know that [P]
  entails [Q], then we also know that if we get [P] after one step, we
  will also get [Q] after one step. This is captured by the [iNext]
  tactic, which introduces a later while stripping laters from our
  hypotheses.
*)

Lemma later_mono (P Q : iProp Σ) : (Q ⊢ P) → (▷ Q ⊢ ▷ P).
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

Lemma later_mono' (P Q : iProp Σ) : (Q ⊢ P) → (▷ Q ⊢ ▷ P).
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
  by [∃] and [∀]. This means we can destruct these constructs
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
  proposition holds after two steps, it will hold after the program has
  terminated.
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

(**
  Further, it turns out that in many cases, a [▷] on an assumption can
  be safely ignored. For instance, in the example below, we only own the
  points-to predicate _later_, yet we can still perform the load.
*)

Lemma later_points_to (l : loc) : ▷ (l ↦ #5) -∗ WP !#l + #1 {{v, ⌜v = #6⌝}}.
Proof.
  iIntros "Hl".
  wp_load.
  by wp_pures.
Qed.

(**
  The technical reason for this is that points-to predicates are
  so-called _timeless_ propositions, and the `wp' tactics are aware of
  this fact. We study timeless propositions further in a separate
  chapter.
*)

(* ================================================================= *)
(** ** Löb Induction *)

(**
  The later modality allows for a strong induction principle called Löb
  induction. Essentially, Löb induction states that to prove a
  proposition [P], we are allowed to assume that [P] holds later, i.e.
  [▷ P]. Formally, we have [□ (▷ P -∗ P) -∗ P]. Recall that [▷]
  represents a single step in the logic. Löb induction essentially
  performs induction in the number of steps. Intuitively, Löb induction
  states that if we can show that whenever [P] holds for strictly
  smaller than [n] steps, we can prove that [P] holds for [n] steps,
  then [P] holds for all steps.

  We can use this principle to prove many properties of recursive
  programs. To see this in action, we will define a simple recursive
  function that increments a counter.
*)

Example count : val :=
  rec: "count" "x" := "count" ("x" + #1).

(**
  This function never terminates for any input as it will keep calling
  itself with larger and larger inputs. To show this, we pick the
  postcondition [False]. We can now use Löb induction, along with
  [wp_rec], to prove this specification.
*)

Lemma count_spec (x : Z) : ⊢ WP count #x {{_, False}}.
Proof.
  (**
    The tactic for Löb induction, [iLöb], requires us to specify the
    name of the induction hypothesis, which we here call ["IH"].
    Optionally, it can also universally quantify over any of our variables
    before performing induction. We here universally quantify over [x] as it
    changes for every recursive call.
  *)
  iLöb as "IH" forall (x).
  (**
    [iLöb] automatically introduces the universally quantified variables in
    the goal, so we can proceed to execute the function.
  *)
  wp_rec.
  wp_pure.
  (**
    Since we have taken steps, the [▷] in our induction hypothesis has
    been stripped, allowing us to apply the hypothesis for the recursive
    call.
  *)
  iApply "IH".
Qed.

End later.
