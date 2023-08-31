From iris.heap_lang Require Import lang proofmode notation.

Section heaplang.
Context `{!heapGS Σ}.

(**XXX Lars: !heapGS not explained *)

(**
  Heaplang is a programming language with an accompanying Iris program logic 
  defined on top of Iris base logic. Heaplang is an untyped higher-order
  functional programming language with dynamically allocated references 
  and concurrency, in the form of dynamically allocated threads that 
  can share access to memory.
  The evaluation order is right to left and it is a call-by-value language.

  To see how we can reason about programs written in Heaplang,
  let us define a small toy program.
*)
Definition prog : expr :=
  (** Allocate the number 1 on the heap *)
  let: "x" := ref #1 in
  (** Increment x by 2 *)
  "x" <- !"x" + #2;;
  (** Read the value of x *)
  !"x".

(**
  This program should evaluate to 3. To prove this we'll use the
  weakest precondition [WP]. This let's us specify a post condition we
  expect to hold, if the program halts.
*)
Lemma wp_prog : ⊢ WP prog {{ v, ⌜v = #3⌝ }}.
Proof.
  rewrite /prog.
  (**
    Heaplang has a set of tactics for reasoning about the evaluation of the
    language. The initial step of prog is to allocate a reference
    containing the value 1. We can symbolically execute this step of prog by
    using the [wp_alloc] tactic with a name for the
    location and a name for the knowledge that the location stores the
    value 1.
  *)
  wp_alloc l as "Hl".
  (**
    The next step of prog is a purely functional reduction step, and 
    and thus we can use [wp_pures] to continue symbolic execution.
  *)
  wp_pures.
  (**
    Next we load from the location [l] using the knowledge that it
    currently stores the value 1.
  *)
  wp_load.
  (** Then we evaluate the addition *)
  wp_pures.
  (**
    Storing is handled by [wp_store].
    Notice that this updates [Hl]. This only works because we are
    working in a separation logic.
  *)
  wp_store.
  (** Finally we use [wp_load] again *)
  wp_load.
  (**
    Now that the program is concluded, we are left with a fancy update
    modality. You can usually ignore this modality and simply introduce
    it. We will explain its uses as we go along.
  *)
  iModIntro.
  (** Now we are left with a trivial proof that 1 + 2 = 3 *)
  done.
Qed.

(**
  The full list of symbolic evaluation tactics can be found at
  https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/heap_lang.md
*)

(**
  Let us use the property we just proved for prog to 
  prove a specification for a larger program.
*)
Lemma wp_prog_add_2 : ⊢ WP prog + #2 {{v, ⌜v = #5⌝}}.
Proof.
  iStartProof.
  (**
    The first part of this program is to evaluate [prog]. So we can
    seperate the program into 2 parts. First we evaluate [prog], then
    we take the result and add 2 to it. To do this we can use [wp_bind].
  *)
  wp_bind prog.
  (**
    Now we have the problem that our post condition doesn't match the
    one we proved. To fix this we can use monotonicity of WP.
  *)
  iApply wp_mono.
  2: { iApply wp_prog. }
  iIntros "%_ ->".
  (** And now we can evaluate the rest of the program *)
  wp_pures.
  (** This post condition is again trivial *)
  done.
Qed.

(**
  The previous proof worked, but it is not very ergonomic.
  To fix this, we'll make [wp_prog] generic on its post condition.
*)
Lemma wp_prog_2 (Φ : val → iProp Σ) :
  (∀ v, ⌜v = #3⌝ -∗ Φ v) -∗ WP prog {{v, Φ v}}.
Proof.
  iIntros "HΦ".
  rewrite /prog.
  wp_alloc l as "Hl".
  wp_load.
  wp_store.
  wp_load.
  by iApply "HΦ".
Qed.

(** Now the other proof becomes much simpler. *)
Lemma wp_prog_add_2_2 : ⊢ WP prog + #2 {{v, ⌜v = #5⌝}}.
Proof.
  wp_bind prog.
  (** Now the proof is on the exact form required by [wp_prog_2] *)
  iApply wp_prog_2.
  (** And the proof proceeds as before *)
  iIntros "%_ ->".
  by wp_pures.
Qed.

(**
  Hoare triples are basically an extended version of a WP with a 
  precondition. They are defined as
  [∀ Φ, Pre -∗ (▷ ∀ r0 .. rn, Post -∗ Φ v) -∗ WP e {{v, Φ v}}].
  This may seem like a very long and complicated definition, so let's
  look at it's parts.

  As in the example above, Hoare triples are parameterised on the post conditions
  satisfied by Post. This allows us to further specialize the
  posible return values by specifying it as a pattern quantified over
  arbitrary parameters. The implication of the post condition is
  hidden under a later modality (▷), signifying that the program takes at least one
  step. And finally we have a precondition Pre.

  The syntax for Hoare triples is as follows:
  [{{{ Pre }}} e {{{ r0 .. rn, RET v; Post }}}]
  - [Pre]: the precondiction that is assumed to hold before the
    program runs.
  - [e]: the program to run.
  - [r0 .. rn]: the parameters used to define the return value.
  - [v]: an expression specifying the shape of the return value.
  - [Post]: the postcondition satisfied after the program has halted.
*)

(**XXX Lars: the later has not been introduced before; maybe just say that 
  it will be described in detail in the following file, or make a file for later
  before doing Heaplang, similarly to persistent.v ?? *)

(** Let's consider a function that swaps 2 values. *)
Definition swap : val :=
  λ: "x" "y",
  let: "v" := !"x" in
  "x" <- !"y";;
  "y" <- "v".

(** To specify this program we can use a Hoare triple. *)
Lemma wp_swap (l1 l2 : loc) (v1 v2 : val) :
  {{{l1 ↦ v1 ∗ l2 ↦ v2}}}
    swap #l1 #l2
  {{{RET #(); l1 ↦ v2 ∗ l2 ↦ v1}}}.
Proof.
  iIntros "%Φ [H1 H2] HΦ".
  rewrite /swap.
  wp_pures.
  wp_load.
  wp_load.
  wp_store.
  wp_store.
  iApply "HΦ".
  by iFrame.
Qed.

(**
  And we can use this specification to prove correctness of client
  code.
*)
Lemma swap_swap (l1 l2 : loc) (v1 v2 : val) :
  {{{l1 ↦ v1 ∗ l2 ↦ v2}}}
    swap #l1 #l2;; swap #l1 #l2
  {{{RET #(); l1 ↦ v1 ∗ l2 ↦ v2}}}.
Proof.
  iIntros "%Φ [H1 H2] HΦ".
  wp_bind (swap _ _).
  iApply (wp_swap with "[$H1 $H2]").
  iIntros "!> [H1 H2]".
  wp_pures.
  iApply (wp_swap with "[$H1 $H2]").
  done.
Qed.

End heaplang.
