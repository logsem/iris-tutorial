From iris.heap_lang Require Import lang proofmode notation par.

(* ################################################################# *)
(** * Specifications *)

(* ================================================================= *)
(** ** Introduction *)

(**
  Now that we have seen basic separation logic in Iris and introduced a
  suitable language, HeapLang, we are finally ready to start reasoning
  about programs. HeapLang ships with a program logic defined using
  Iris. We can access the logic through the [proofmode] package, which
  also defines tactics to alleviate working with the logic. The logic
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

              [WP e {{ w, WP K[w] {{ v, Φ v }} }} ⊢ WP K[e] {{ v, Φ v }}]

    This allows us to change the goal from

    [WP (#1 + #2 * #3 + #4 + #5) {{ v, ⌜v = #16⌝ }}]

    to

    [WP #2 * #3 {{ w, WP (#1 + [] + #4 + #5)[w] {{ v, ⌜v = #16⌝ }} }}]

    Next, the wp-op rule symbolically executes a single arithmetic
    operation, [⊚].
    [[
                              v = v₁ ⊚ v₂
                -------------------------------------------
                WP v {{ v, Φ v }} ⊢ WP v₁ ⊚ v₂ {{ v, Φ v }}
    ]]

    We can thus perform the multiplication and change the goal to

    [WP #(2 * 3) {{ w, WP (#1 + [] + #4 + #5)[w] {{ v, ⌜v = #16⌝ }} }}]

    Finally, wp-val states that we can prove a weakest precondition of a
    value by proving the postcondition specialised to that value.

                          [Φ(v) ⊢ WP v {{ w, Φ w }}]

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
    the goal becomes proving the postcondition with said value
    (essentially applying wp-val). Technically, the goal is to prove the
    postcondition behind a `fancy update modality'. This functionality
    is related to resources and invariants, so we skip it for now. We
    can always remove a fancy update modality in the goal with
    [iModIntro].
  *)
  iModIntro.
  iPureIntro.
  reflexivity.
Qed.

(**
  Let us look at another example of a pure program. The `lambda' program
  from lang.v consists of only let expressions, lambdas, applications,
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

  <<https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/heap_lang.md#tactics>>

  These tactics similarly apply the underlying rules of the logic,
  however we shall from now on refrain from explicitly mentioning the
  rules applied. Through experience, the reader should get an intuition
  for how each tactic manipulates the goal.

  Exercise: prove the following specification for the lambda program.
*)
Lemma lambda_spec : ⊢ WP lambda {{ v, ⌜v = #20⌝ }}.
(* BEGIN SOLUTION *)
Proof.
  rewrite /lambda.
  wp_pures.
  done.
Qed.
(* END SOLUTION BEGIN TEMPLATE
Proof.
  rewrite /lambda.
  (* exercise *)
Admitted.
END TEMPLATE *)

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
  (** Allocate the number [1] on the heap *)
  let: "x" := ref #1 in
  (** Increment [x] by [2] *)
  "x" <- !"x" + #2;;
  (** Read the value of [x] *)
  !"x".

(**
  This program should evaluate to [3]. We express this with a weakest
  precondition.
*)
Lemma prog_spec : ⊢ WP prog {{ v, ⌜v = #3⌝ }}.
Proof.
  rewrite /prog.
  (**
    The initial step of [prog] is to allocate a reference containing the
    value [1]. We can symbolically execute this step of [prog] using the
    [wp_alloc] tactic. As a result of the allocation, we get the
    existence of some location [l] which points-to [1], [l ↦ #1]. The
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
    the associated points-to predicate in the context. The predicate
    then governs the result of the load. Since we have [Hl], we can
    perform the load using the [wp_load] tactic.
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
  HeapLang also provides the [CmpXchg] instruction to interact with the
  heap. The [wp_cmpxchg] symbolically executes an instruction on the
  form [CmpXchg l v1 v2]. As with [wp_load] and [wp_store], [wp_cmpxchg]
  requires the associated points-to predicate [l ↦ v]. If this is
  present in the context, then [wp_cmpxchg as H1 | H2] will generate two
  subgoals. The first corresponds to the case where the [CmpXchg]
  instruction succeeded. Thus, we get to assume [H1 : v = v1], and our
  points-to predicate for [l] is updated to [l ↦ v2]. The second
  corresponds to case where [CmpXchg] failed. We instead get
  [H2 : v ≠ v1], and our points-to predicate for [l] is unchanged.

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
  If it is clear that a [CmpXchg] instruction will succeed, then we can
  apply the [wp_cmpxchg_suc] tactic which will immediately discharge the
  case where [CmpXchg] fails. Similarly, we can use [wp_cmpxchg_fail]
  when a [CmpXchg] instruction will clearly fail.

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
  The result of both [CAS] instructions are predetermined. Hence, we can
  use the [wp_cmpxchg_suc] and [wp_cmpxchg_fail] tactics to symbolically
  execute them (remember that [CAS l v1 v2] is syntactic sugar for
  [Snd (CmpXchg l v1 v2)]).
  Exercise: finish the proof of the specification for [cas].
*)

Lemma cas_spec : ⊢ WP cas {{ v, ⌜v = (#5, #7)%V⌝ }}.
(* BEGIN SOLUTION *)
Proof.
  rewrite /cas.
  wp_alloc l as "Hl".
  wp_let.
  wp_cmpxchg_fail.
  wp_proj.
  wp_if.
  wp_load.
  wp_let.
  wp_cmpxchg_suc.
  wp_proj.
  wp_if.
  wp_load.
  wp_let.
  wp_pair.
  done.
Qed.
(* END SOLUTION BEGIN TEMPLATE
Proof.
  rewrite /cas.
  wp_alloc l as "Hl".
  wp_let.
  wp_cmpxchg_fail.
  wp_proj.
  wp_if.
  (* exercise *)
Admitted.
END TEMPLATE *)

(**
  We finish this section with a final remark about the points-to
  predicate. One of its essential properties is that it is not
  duplicable. That is, for every location [l], there can only exist one
  points-to predicate associated with it [l ↦ v]. This is captured by
  the following lemma.
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

(**
  Let us use the specification we proved for [prog] in the previous
  section to prove a specification for a larger program.
*)
Lemma prog_add_2_spec : ⊢ WP prog + #2 {{ v, ⌜v = #5⌝ }}.
Proof.
  iStartProof.
  (**
    The first part of this program is to evaluate [prog]. We already
    have a specification that tells us how this sub-expression behaves:
    [prog_spec]. To apply it, we must change the goal to match the
    specification. Using the wp-bind rule presented earlier, we can
    focus in on the [prog] expression. Iris provides the tactic
    [wp_bind] for this purpose.
  *)
  wp_bind prog.
  (**
    The expression now matches the [prog_spec] specification, but the
    postcondition still does not match. To fix this, we can use
    monotonicity of WP. That is,

      [WP e {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e {{ Ψ }}].

    With this it suffices to prove that the postcondition of [prog_spec]
    implies the postcondition in our current goal. This is achieved with
    the [wp_wand] lemma, which generates two subgoals, one corresponding
    to [WP e {{ Φ }}] and one to [(∀ v, Φ v -∗ Ψ v)].
  *)
  iApply wp_wand; simpl.
  { iApply prog_spec. }
  simpl.
  (**
    When introducing equalities, we can immediately rewrite using it
    with [->] or [<-], depending on which direction we want to rewrite.
  *)
  iIntros "%w ->".
  (** And now we can evaluate the rest of the program. *)
  wp_pure.
  done.
Qed.

(**
  The previous proof worked, but it is not very ergonomic. To fix this,
  we will make [prog_spec] generic on its postcondition.
*)
Lemma prog_spec_2 (Φ : val → iProp Σ) :
  (∀ v, ⌜v = #3⌝ -∗ Φ v) -∗ WP prog {{ v, Φ v }}.
Proof.
  iIntros "HΦ".
  rewrite /prog.
  wp_alloc l as "Hl".
  wp_load.
  wp_store.
  wp_load.
  by iApply "HΦ".
Qed.

(** Now, the other proof becomes simpler. *)
Lemma prog_add_2_spec' : ⊢ WP prog + #2 {{ v, ⌜v = #5⌝ }}.
Proof.
  wp_bind prog.
  (** The goal is now on the exact form required by [prog_spec_2] *)
  iApply prog_spec_2.
  (** And the proof proceeds as before *)
  iIntros "%w ->".
  wp_pure.
  done.
Qed.

(**
  We can even simplify this proof further by using the [wp_apply]
  tactic which automatically applies [wp_bind] for us.
*)
Lemma prog_add_2_spec'' : ⊢ WP prog + #2 {{ v, ⌜v = #5⌝ }}.
  wp_apply prog_spec_2.
  iIntros "%w ->".
  wp_pure.
  done.
Qed.

(* ================================================================= *)
(** ** Hoare Triples *)

(**
  Having studied weakest preconditions, we shift our focus onto another
  construct for specifying program behaviour: Hoare triples. The weakest
  precondition does not explicitly specify which conditions must be met
  before executing the program. It only talks about which conditions are
  met after – the postcondition. Hoare triples build on weakest
  preconditions by requiring us to explicitly mention the the conditions
  that must hold before running the program – the precondition.

  The syntax for Hoare triples is as follows:
    [{{{ P }}} e {{{ r0 .. rn, RET v; Q v }}}]
  - [P]: the precondition that is assumed to hold before the program runs.
  - [e]: the program to run.
  - [r0 .. rn]: optional, forall quantified variables used for abstract
    return values.
  - [v]: the return value.
  - [Q]: the postcondition which holds after the program terminates.

  In Iris, Hoare triples are actually defined in terms of weakest
  preconditions. The definition is as follows:

    [□( ∀ Φ, P -∗ ▷ (∀ r0 .. rn, Q -∗ Φ v) -∗ WP e {{v, Φ v }})]

  This is quite a lengthy definition, so let us break it down.
  Firstly, inspired by the [prog_spec_2] example from the previous
  section, this definition makes the postcondition generic.
  Next, the precondition [P] implies the generic weakest precondition,
  signifying that we must first prove [P] before we can apply
  specification for [e].
  Finally, the definition uses two modalities that we have yet to cover.
  The persistently modality [□] signifies that the specification can be
  freely duplicated, meaning we can reuse Hoare triples.
  The later modality [▷] signifies that the program takes at least one
  step. The reason for including this is purely technical, and can for
  the most part be ignored.
  We will get back to both modalities later. For now, let us look at
  an example. Consider a function that swaps two values.
*)

Definition swap : val :=
  λ: "x" "y",
  let: "v" := !"x" in
  "x" <- !"y";;
  "y" <- "v".

(** We will use a Hoare triple to specify this program's behaviour. *)
Lemma swap_spec (l1 l2 : loc) (v1 v2 : val) :
  {{{ l1 ↦ v1 ∗ l2 ↦ v2 }}}
    swap #l1 #l2
  {{{ RET #(); l1 ↦ v2 ∗ l2 ↦ v1 }}}.
Proof.
  (**
    When introducing a Hoare triple, we use the definition above to turn
    the goal into a weakest precondition.
  *)
  iIntros "%Φ [H1 H2] HΦ".
  (** We can now prove the specification as we have done previously. *)
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
  Since Hoare triples are generic in the postcondition `under the hood',
  specifications written using Hoare triples can be easily used by
  clients, as demonstrated in the previous section. We demonstrate it
  here again with a client of [swap].
*)
Lemma swap_swap_spec (l1 l2 : loc) (v1 v2 : val) :
  {{{ l1 ↦ v1 ∗ l2 ↦ v2 }}}
    swap #l1 #l2;; swap #l1 #l2
  {{{ RET #(); l1 ↦ v1 ∗ l2 ↦ v2 }}}.
Proof.
  iIntros "%Φ H HΦ".
  wp_apply (swap_spec with "H").
  iIntros "H".
  wp_seq.
  wp_apply (swap_spec with "H").
  done.
Qed.

(**
  A convention in Iris is to write specifications using Hoare triples,
  but prove them by converting them to weakest preconditions as in the
  examples above. There are several reasons for this. Firstly, it
  ensures that all specifications are generic in the postcondition.
  Secondly, specifications written in terms of Hoare triples are usually
  easier to read, as they name explicitly what must be obtained before
  the program can be executed. Finally, proving Hoare triples directly
  can be quite awkward and burdensome, especially in Coq.
*)

(* ================================================================= *)
(** ** Concurrency *)

(**
  We finish this chapter with a final example that utilises the theory
  presented in the previous sections. The example gives a specification
  for a concurrent program, which illustrates how ownership of resources
  (in particular points-to predicates) can be transferred between
  threads. The program is as follows.
*)

Example par_client : expr :=
  let: "l1" := ref #0 in
  let: "l2" := ref #0 in
  (("l1" <- #21) ||| ("l2" <- #2)) ;;
  let: "life" := !"l1" * !"l2" in
  ("l1", "l2", "life").

(**
  The program uses parallel composition (e1 ||| e2) from the [par]
  package. Note that the two threads operate on separate locations;
  there is no possibility for a data race.

  The [par] package provides a specification for parallel composition
  called [wp_par]. The specification is as follows.

  [[
  ∀ (Ψ1 Ψ2 : val → iProp Σ) (e1 e2 : expr) (Φ : val → iProp Σ),
    WP e1 {{ Ψ1 }} -∗
    WP e2 {{ Ψ2 }} -∗
    (∀ v1 v2, (Ψ1 v1) ∗ (Ψ2 v2) -∗ ▷ Φ (v1, v2)) -∗
    WP (e1 ||| e2) {{ Φ }}
  ]]

  Essentially, to prove a weakest precondition of parallel composition
  [WP (e1 ||| e2) {{ Φ }}], one must prove a weakest precondition for
  each of the threads, [WP e1 {{ Ψ1 }}] and [WP e2 {{ Ψ2 }}], and show
  that all pairs of values that satisfy the postconditions [Ψ1] and [Ψ2]
  respectively, also satisfy the postcondition of the weakest
  precondition we wish to prove [Φ]. Note that the specification uses
  the `later' modality [▷]. This is not needed for our current purposes,
  so it can safely be ignored. We cover the later modality later.
*)

(**
  The [wp_par] specification relies on a notion of resources different
  from the resource of heaps. The details of the resources are
  irrelevant for our example, but we must still assume that [Σ] contains
  the resources.
*)

Context `{!spawnG Σ}.

(**
  Let us now return to our [par_client] example. We specify the
  behaviour of [par_client] with a Hoare triple.
*)

Lemma par_client_spec :
  {{{ True }}}
    par_client
  {{{ l1 l2 life, RET (#l1, #l2, #life); l1 ↦ #21 ∗ l2 ↦ #2 ∗ ⌜life = 42⌝ }}}.
Proof.
  iIntros (Φ _) "HΦ".
  rewrite /par_client.
  (**
    The program starts by creating two fresh location, [l1] and [l2].
  *)
  wp_alloc l1 as "Hl1".
  wp_let.
  wp_alloc l2 as "Hl2".
  wp_let.
  wp_pures.
  (**
    The specification for [par] requires us to specify the
    postconditions for the two threads. Since the threads return unit,
    the postconditions will just describe the points-to predicates,
    reflecting the writes.
  *)
  set t1_post := (λ v : val, (l1 ↦ #21)%I).
  set t2_post := (λ v : val, (l2 ↦ #2)%I).
  (**
    We can now apply the [wp_par] specification. Note how we transfer
    ownership of [l1 ↦ #0] to the first thread, and [l2 ↦ #0] to the
    second. This allows each thread to perform their store operations.
  *)
  wp_apply (wp_par t1_post t2_post with "[Hl1] [Hl2]").
  (**
    We must now prove WP specifications for each thread, with the
    postconditions we specified above.
  *)
  { wp_store. by iFrame. }
  { wp_store. by iFrame. }
  (**
    Finally, we return to the main thread, and we are allowed to assume
    the postconditions of both threads. Since the postconditions
    mentioned the points-to predicates, these are essentially
    transferred back to the main thread.
  *)
  iIntros (r1 r2) "[Hl1 Hl2]".
  rewrite /t1_post /t2_post.
  (**
    Note: the [wp_par] specification adds a later modality [▷] to the
    goal. This actually strengthens [wp_par], but we do not need that
    strength in this example, so we can simply ignore it. The [▷] can be
    introduced with [iNext].
  *)
  iNext.
  wp_seq.
  wp_load.
  wp_load.
  wp_pures.
  iApply ("HΦ" $! l1 l2 (21 * 2)).
  by iFrame.
Qed.

(**
  Food for thought: Imagine a program that has threads operating on the
  _same_ location in parallel, akin to the following.
*)
Example race (l : loc) : expr := ((#l <- #1) ||| (#l <- #2)).

(**
  Even though the program is non-deterministic, we can still give it a
  meaningful specification.
*)
Definition race_spec (l : loc) (v : val) :=
  {{{ l ↦ v }}} race l {{{ w, RET w; (l ↦ #1) ∨ (l ↦ #2) }}}.

(**
  Could we prove this specification similarly to how we proved
  [par_client]?
*)

End specifications.