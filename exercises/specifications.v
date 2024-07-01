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
  programs. These specifications can then be proven by using rules
  associated with the constructs. The tactics provided by the
  [proofmode] package essentially just apply these rules.

  The program logic for HeapLang relies on a basic notion of a resource
  – the resource of heaps. Recall that [Σ] specifies the available
  resources. To make the resource of heaps available, we have to specify
  that [Σ] should contain it. The typeclass [heapGS] does exactly this.
  Using [heapGS] and the [Context] command, we can assume that [Σ]
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
    by [#3]. The tactic [wp_op] symbolically executes this expression
    using the underlying rules of the logic.
  *)
  wp_op.
  (**
    Note that the expression [#2 * #3] turned into [#(2 * 3)] – the Coq
    expression [2 * 3] is treated as a value in HeapLang.
    
    In particular, [wp_op] has here applied three underlying rules:
    wp-bind, wp-op, and wp-val. The rule wp-bind allows us to `focus' on
    some sub-expression [e], which is the next part to be evaluated
    according to some evaluation context [K]. The rule is as follows:

              [WP e {{v, WP K[v] {{Φ}} }} ⊢ WP K[e] {{Φ}}]

    This allows us to change the goal from
    [WP (#1 + #2 * #3 + #4 + #5) {{ v, ⌜v = #16⌝ }}] 
    to
    [WP #2 * #3 {{ v, WP (#1 + [] + #4 + #5)[v] {{ v, ⌜v = #16⌝ }} }}]

    Next, the wp-op rule symbolically executes a single arithmetic
    operation, [⊚].

                        [v = v₁ ⊚ v₂]
                --------------------------------
                [WP v {{Φ}} ⊢ WP v₁ ⊚ v₂ {{Φ}}]

    We can thus perform the multiplication and change the goal to
    [WP #(2 * 3) {{ v, WP (#1 + [] + #4 + #5)[v] {{ v, ⌜v = #16⌝ }} }}]
    
    Finally, wp-val states that we can prove a weakest precondition of a
    value by proving the postcondition specialised to that value.

                      [Φ(v) ⊢ WP v {{Φ}}]

    The goal is changed to
    [WP #1 + #(2 * 3) + #4 + #5 {{ v, ⌜v = #16⌝ }}]
    
    This is where [wp_op] has taken us. The next step of the program is
    to add [#1] to [#(2 * 3)]. We could again use [wp_op] to
    symbolically execute this, but instead, we shall use the [wp_pure]
    tactic. This tactic can symbolically execute any pure expression.
  *)
  wp_pure.
  (**
    Similarly to above, this tactic applies wp-bind, wp-op, and wp-val.
  
    If there are several pure steps in a row, we can use the [wp_pures]
    tactic, which repeatedly applies [wp_pure].
  *)
  wp_pures.
  (**
    When the expression in a weakest precondition turns into a value,
    the goal becomes to prove the postcondition with said value
    (essentially applying wp-val). Technically, the goal is to prove the
    postcondition behind a `fancy update modality'. This functionality
    is related to resources and invaraints, so we skip it for now. We
    can always remove a fancy update modality in the goal with
    [iModIntro].
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
  expressions, [wp_lam] for applications, and [wp_op] for arithmetic. A
  list of all tactics for HeapLang expressions can be found at
  https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/heap_lang.md#tactics.
  These tactics similarly apply the underlying rules of the logic,
  however we shall from now on refrain from explicitly mentioning the
  rules applied. Through experience, the reader should get an intuition
  for how each tactic manipulates the goal.

  Exercise: prove the following specification for the lambda program.
*)
Lemma lambda_spec : ⊢ WP lambda {{ v, ⌜v = #20⌝ }}.
Proof.
  rewrite /lambda.
  (* exercise *)
Admitted.

(* ================================================================= *)
(** ** Resources *)

(**
  In this section, we introduce our first notion of a resource: the
  resource of heaps. As mentioned in basics.v, propositions in Iris
  describe/assert ownership of resources. To describe resources in the
  resource of heaps, we use the `points-to' predicate, written [l ↦ v].
  Intuitively, this describes all heap fragments that has value [v]
  stored at location [l]. The proposition [l1 ↦ #1 ∗ l2 ↦ #2] then
  describes all heap fragments that map [l1] to [#1] and [l2] to [#2].

  To see this in action, let us consider a simple program.
*)
Definition prog : expr :=
  (** Allocate the number 1 on the heap *)
  let: "x" := ref #1 in
  (** Increment x by 2 *)
  "x" <- !"x" + #2;;
  (** Read the value of x *)
  !"x".

(**
  This program should evaluate to 3. We express this with a weakest
  precondition.
*)
Lemma prog_spec : ⊢ WP prog {{ v, ⌜v = #3⌝ }}.
Proof.
  rewrite /prog.
  (**
    The initial step of [prog] is to allocate a reference containing the
    value 1. We can symbolically execute this step of [prog] using the
    [wp_alloc] tactic. As a result of the allocation, we get the
    existence of some location [l] which points-to 1, [l ↦ #1]. The
    [wp_alloc] tactic requires that we give names to the location and the
    proposition.
  *)
  wp_alloc l as "Hl".
  (**
    The next step of [prog] is a let expression which we symbolically
    execute with [wp_let].
  *)
  wp_let.
  (**
    Next, we load from location [l]. Loading from a location requires
    the associated points-to predicate in the context. Since we have
    [Hl], we can perform the load using the [wp_load] tactic.
  *)
  wp_load.
  (** Then we evaluate the addition. *)
  wp_op.
  (**
    Storing is handled by [wp_store]. As with loading, we must have the
    associated points-to predicate in the context. [wp_store] updates
    the points-to predicate to reflect the store.
  *)
  wp_store.
  (** Finally, we use [wp_load] again. *)
  wp_load.
  (** Now we are left with a trivial proof that [1 + 2 = 3]. *)
  iModIntro.
  done.
Qed.

(**
  HeapLang also provides the CmpXchg instruction to interact with the
  heap. The [wp_cmpxchg] symbolically executes an instruction on the
  form [CmpXchg l v1 v2]. As with [wp_load] and [wp_store], [wp_cmpxchg]
  also requires the associated points-to predicate [l ↦ v]. If this is
  present in the context, then [wp_cmpxchg as H1 | H2] will generate two
  subgoals. The first corresponds to the case where the CmpXchg
  instruction succeeded. Thus, we get to assume [H1 : v = v1], and our
  points-to predicate for [l] is updated to [l ↦ v2]. The second
  coresponds to case where CmpXchg failed. We instead get [H2 : v ≠ v1],
  and our points-to predicate for [l] is unchanged.

  Let us demonstrate this with a simple example program which simply
  checks if a given location contains the number 0 and, if it does,
  updates it to 10.
*)

Example cmpXchg_0_to_10 (l : loc) : expr := (CmpXchg #l #0 #10).

Lemma cmpXchg_0_to_10_spec (l : loc) (v : val) :
  l ↦ v -∗
  WP (cmpXchg_0_to_10 l) {{ u, (⌜v = #0⌝ ∗ l ↦ #10) ∨
                               (⌜v ≠ #0⌝ ∗ l ↦ v) }}.
Proof.
  iIntros "Hl".
  wp_cmpxchg as H1 | H2.
  - (* CmpXchg succeeded *)
    iLeft.
    by iFrame.
  - (* CmpXchg failed *)
    iRight.
    by iFrame.
Qed.

(**
  If it is clear that a CmpXchg instruction will succeed, then we can
  apply the [wp_cmpxchg_suc] tactic which will immidiately discharge
  the case where CmpXchg fails. Similarly, we can use [wp_cmpxchg_fail]
  when a CmpXchg instruction will clearly fail.

  Recall the [cas] example from lang.v
*)

Example cas : expr :=
  let: "l" := ref #5 in
  if: CAS "l" #6 #7 then
    #()
  else
    let: "a" := !"l" in
    if: CAS "l" #5 #7 then
      let: "b" := !"l" in
      ("a", "b")
    else
      #().

(**
  The result of both CAS instructions are predetermined. Hence, we can
  use the [wp_cmpxchg_suc] and [wp_cmpxchg_fail] tactics to symbolically
  execute them (remember that [CAS l v1 v2] is syntactic sugar for 
  [Snd (CmpXchg l v1 v2)]).
  Exercise: finish the proof of the specification for [cas].
*)

Lemma cas_spec : ⊢ WP cas {{ v, ⌜v = (#5, #7)%V⌝ }}.
Proof.
  rewrite /cas.
  wp_alloc l as "Hl".
  wp_let.
  wp_cmpxchg_fail.
  wp_proj.
  wp_if.
  (* exercise *)
Admitted.

(**
  We finish this section with a final remark about the points-to
  predicate. An essential property of the points-to predicate is that it
  is not duplicable. That is, for every location [l], there can only
  exist one points-to predicate associated with it [l ↦ v]. This is
  captured by the following lemma.
*)
Lemma pt_not_dupl (l : loc) (v v' : val) : l ↦ v ∗ l ↦ v' ⊢ False.
Proof.
  (**
    The proof of this lemma is not important here. It relies on details
    of the underlying implementation of the resource of heaps. We will
    return to this when we treat resources in general later in the
    tutorial.
  *)
  iIntros "[Hlv Hlv']".
  iCombine "Hlv Hlv'" gives "[%H _]".
  contradiction.
Qed.

(* ================================================================= *)
(** ** Composing Programs and Proofs *)

(* TODO: UPDATE SECTION *)

(**
  Let us use the property we just proved for prog to 
  prove a specification for a larger program.
*)
Lemma prog_add_2_spec : ⊢ WP prog + #2 {{ v, ⌜v = #5⌝}}.
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
  2: { iApply prog_spec. }
  iIntros "%_ ->".
  (** And now we can evaluate the rest of the program *)
  wp_pures.
  (** This postcondition is again trivial *)
  done.
Qed.

(**
  The previous proof worked, but it is not very ergonomic.
  To fix this, we'll make [prog_spec] generic on its postcondition.
*)
Lemma prog_spec_2 (Φ : val → iProp Σ) :
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
Lemma prog_add_2_spec_2 : ⊢ WP prog + #2 {{v, ⌜v = #5⌝}}.
Proof.
  wp_bind prog.
  (** Now the proof is on the exact form required by [prog_spec_2] *)
  iApply prog_spec_2.
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
Lemma swap_spec (l1 l2 : loc) (v1 v2 : val) :
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
Lemma swap_swap_spec (l1 l2 : loc) (v1 v2 : val) :
  {{{l1 ↦ v1 ∗ l2 ↦ v2}}}
    swap #l1 #l2;; swap #l1 #l2
  {{{RET #(); l1 ↦ v1 ∗ l2 ↦ v2}}}.
Proof.
  iIntros "%Φ [H1 H2] HΦ".
  wp_bind (swap _ _).
  iApply (swap_spec with "[$H1 $H2]").
  iIntros "!> [H1 H2]".
  wp_pures.
  iApply (swap_spec with "[$H1 $H2]").
  done.
Qed.

End specifications.
