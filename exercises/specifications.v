From iris.heap_lang Require Import lang proofmode notation.

(*########## CONTENTS PLAN ##########
- INTRODUCE WEAKEST-PRECONDITIONS
  + EXAMPLES WITH PURE EXPRESSIONS
- INTRODUCE RESOURCE OF HEAPS
  + POINTS-TO PREDICATE
  + EXAMPLES WITH ALLOC, STORE, LOAD, CMPXCHG
- INTRODUCE HOARE-TRIPLES
  + EXAMPLES
  + RELATIONSHIP TO WP
  + CONVENTION: HT FOR SPECS, WP FOR PROOFS
#####################################*)

(* ################################################################# *)
(** * Specifications *)

(* ================================================================= *)
(** ** Introduction *)

(**
  Now that we have seen basic separation logic in Iris and introduced a
  suitable language, HeapLang, we are finally ready to start reasoning
  about programs. HeapLang ships with a program logic defined using
  Iris. We can access the logic through the [proofmode] package, which
  also defines tactics to aliviate working with the logic. The logic
  provides constructs that allow us to specify the behaviour of HeapLang
  programs. These specifications can then be proven by using the rules
  associated with the constructs. The tactics provided by the
  [proofmode] package essentially just apply these rules.

  The program logic for HeapLang relies on a basic notion of a resource
  – the resource of heaps. Recall that [Σ] specifies the available
  resources. To make the resource of heaps available, we have to specify
  that [Σ] should contain the it. The typeclass [heapGS] does exactly
  this. Using [heapGS] and the [Context] command, we can assume that [Σ]
  contains the resource of heaps throughout the [specifications]
  section.
*)

Section specifications.
Context `{!heapGS Σ}.

(* ================================================================= *)
(** ** Weakest Precondition *)

(**
  The first construct for specifying program behaviour that we shall use
  is the `weakest precondition'. To motivate it, let us consider a
  simple example.
*)

Example arith : expr :=
  #1 + #2 * #3 + #4 + #5.

(**
  This program should evaluate to [16]. We can express this in the logic
  with a weakest precondition. In general, a weakest precondition has
  the form [WP e {{v, Φ v}}]. This asserts that, if the HeapLang program
  [e] terminates at some value [v], then [v] satisfies the predicate
  [Φ]. The double curly brackets [{{v, Φ v}}] is called the
  `postcondition'. For the case of [arith], we would express its
  behaviour using the following weakest precondition.
*)

Lemma arith_spec : ⊢ WP arith {{ v, ⌜v = #16⌝ }}.
Proof.
  rewrite /arith.
  (**
    To prove this weakest precondition, we can use the tactics provided
    by [proofmode]. The initial step of the program is to multiply [#2]
    by [#3]. The tactic [wp_binop] symbolically executes this expression
    using the underlying rules of the logic.
  *)
  wp_binop.
  (**
    Note that the expression [#2 * #3] turned into [#(2 * 3)] – the Coq
    expression [2 * 3] is treated as a value in HeapLang.
    
    The next step of the program is to add [#1] to [#(2 * 3)]. We could
    again use [wp_binop] to symbolically execute this, but instead we
    shall use the [wp_pure] tactic. This tactic can symbolically execute
    all pure expressions.
  *)
  wp_pure.
  (** 
    If there are several pure steps in a row, we can use the [wp_pures]
    tactic, which repeatedly applies [wp_pure].
  *)
  wp_pures.
  (**
    When the expression in a weakest precondition turns into a value,
    the goal becomes to prove the postcondition with said value.
    Technically, the goal is to prove the postcondition behind a `fancy
    update modality'. This functionality is related to resources and
    invaraints, so we skip it for now. We can always remove a fancy
    update modality in the goal with [iModIntro].
  *)
  iModIntro.
  iPureIntro.
  reflexivity.
Qed.

(**
  Let us look at another example of a pure program. The `lambda' program
  from lang.v constists of only let expressions, lambdas, applications,
  and arithmetic.
*)

Example lambda : expr :=
  let: "add5" := (λ: "x", "x" + #5) in
  let: "double" := (λ: "x", "x" * #2) in
  let: "compose" := (λ: "f" "g", (λ: "x", "g" ("f" "x"))) in
  ("compose" "add5" "double") #5.

(**
  The program logic for HeapLang provides specific tactics to
  symbolically execute these kinds of expressions, e.g. [wp_let] for let
  expressions, [wp_lam] for applications, and [wp_op] for arithmetic. A list
  of all tactics for HeapLang expressions can be found at
  https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/heap_lang.md#tactics.

  Exercise: prove the following specification for the lambda program.
*)
Lemma lambda_spec : ⊢ WP lambda {{ v, ⌜v = #20⌝ }}.
Proof.
  rewrite /lambda.
  (* exercise *)
Admitted.

(* ================================================================= *)
(** ** Resources *)

(*########## CONTENTS PLAN ##########
- RE-INTRODUCE THAT PROPOSITIONS DESCRIBES RESOURCES
- IN IRIS, USER CAN DEFINE THEIR OWN NOTION (resource_algebra.v)
- A BASIC NOTION IS THAT OF POINTS-TO PREDICATES (resource for heaps)
- EXAMPLES
- EXCLUSIVITY
- EXAMPLES
- HOARE TRIPLES FOR HEAPLANG HEAP INSTRUCTIONS (STORE, READ, CAS)
#####################################*)

(* TODO: UPDATE SECTION TO FIT ABOVE *)

(**
  To see how we can reason about programs written in HeapLang,
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
  weakest precondition [WP]. This lets us specify a postcondition we
  expect to hold if the program halts.
*)
Lemma wp_prog : ⊢ WP prog {{ v, ⌜v = #3⌝ }}.
Proof.
  rewrite /prog.
  (**
    HeapLang has a set of tactics for reasoning about the evaluation of the
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
    Next, we load from the location [l] using the knowledge that it
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
    Now that the program has concluded, we are left with a fancy update
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

(* ================================================================= *)
(** ** Composing Programs and Proofs *)

(* TODO: UPDATE SECTION *)

(**
  Let us use the property we just proved for prog to 
  prove a specification for a larger program.
*)
Lemma wp_prog_add_2 : ⊢ WP prog + #2 {{v, ⌜v = #5⌝}}.
Proof.
  iStartProof.
  (**
    The first part of this program is to evaluate [prog]. So we can
    separate the program into 2 parts. First, we evaluate [prog], then
    we take the result and add 2 to it. To do this we can use [wp_bind].
  *)
  wp_bind prog.
  (**
    Now we have the problem that our postcondition doesn't match the
    one we proved. To fix this we can use the monotonicity of WP.
  *)
  iApply wp_mono.
  2: { iApply wp_prog. }
  iIntros "%_ ->".
  (** And now we can evaluate the rest of the program *)
  wp_pures.
  (** This postcondition is again trivial *)
  done.
Qed.

(**
  The previous proof worked, but it is not very ergonomic.
  To fix this, we'll make [wp_prog] generic on its postcondition.
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

(* ================================================================= *)
(** ** Hoare Triples *)

(* TODO: UPDATE SECTION *)

(**
  Hoare triples are an extended version of a WP with a 
  precondition. They are defined as
  [∀ Φ, Pre -∗ (▷ ∀ r0 .. rn, Post -∗ Φ v) -∗ WP e {{v, Φ v}}].
  This may seem like a very long and complicated definition, so let's
  look at it's parts.

  As in the example above, Hoare triples are parameterized on the post conditions
  satisfied by Post. This allows us to further specialize the
  possible return values by specifying them as a pattern quantified over
  arbitrary parameters. The implication of the postcondition is
  hidden under a later modality (▷), signifying that the program takes at least one
  step. This modality will be described in the following file.
  Finally, we have a precondition Pre.

  The syntax for Hoare triples is as follows:
  [{{{ Pre }}} e {{{ r0 .. rn, RET v; Post }}}]
  - [Pre]: the precondition that is assumed to hold before the
    program runs.
  - [e]: the program to run.
  - [r0 .. rn]: the parameters used to define the return value.
  - [v]: an expression specifying the shape of the return value.
  - [Post]: the postcondition is satisfied after the program has halted.
*)

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
  And we can use this specification to prove the correctness of the
  client code.
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

End specifications.
