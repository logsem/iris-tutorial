From iris.heap_lang Require Import lang proofmode notation.

(*########## CONTENTS PLAN ##########
- TIMELESS PROPOSITIONS AND STRIPPING LATERS
  + USUALLY DONE WHEN INTRODUCING PROPOSTIIONS VIA '>'
  + SHOW EXAMPLES
- EXPAND ON LÖB INDUCTION
#####################################*)

(* ################################################################# *)
(** * Later *)

Section later.
Context `{!heapGS Σ}.

(**
  Iris is a step-indexed logic, meaning it has a built-in notion of
  time. This can be expressed with the later modality [▷ P] signifying
  that [P] holds after one time step. These time steps are linked to the
  execution steps of our programs in HeapLang. Every time we use one
  of the wp tactics, we let time tick forward. To see this, let us look
  at a simple program: [1 + 2 + 3]. This program takes two steps to
  evaluate, so we can prove that if a proposition holds after 2 steps, 
  then it will hold after the program has terminated.
*)
Lemma take_2_steps (P : iProp Σ) : ▷ ▷ P -∗ WP #1 + #2 + #3 {{_, P}}.
Proof.
  iIntros "HP".
  wp_pure.
  wp_pure.
  done.
Qed.

(**
  This works because later is monotone, meaning [▷ P ⊢ ▷ Q] if
  [P ⊢ Q]. Inside WP there is a later for every step of the program,
  so the wp tactics can use monotonicity to remove laters from the
  context. Furthermore, later satisfies [P ⊢ ▷ P] and
  [▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q]. These rules allow the tactics to ignore
  hypotheses in the context that do not have a later on them.

  Instead of applying these rules directly, we can use the tactic
  [iNext] to introduce a later, while stripping laters from our
  hypotheses.
*)
Lemma later_impl (P Q : iProp Σ) : P ∗ ▷ (P -∗ Q) -∗ ▷ Q.
Proof.
  iIntros "[HP HQ]".
  iNext.
  iApply "HQ".
  iApply "HP".
Qed.

(**
  Alternatively, as later is a modality, you can use [iModIntro] and
  therefore [iIntros "!>"] to introduce it, making it less verbose to
  handle.
*)

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
