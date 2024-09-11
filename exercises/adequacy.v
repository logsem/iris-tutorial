From iris.algebra Require Import excl.
From iris.base_logic.lib Require Export token.
From iris.heap_lang Require Import adequacy lang proofmode notation par.
From exercises Require Import spin_lock.

(* ################################################################# *)
(** * Adequacy *)

(**
  Thus far, we have assumed that the weakest precondition is correct.
  But what does that even mean? This is what is called _adequacy_, and
  its definition depends on the properties we want it to satisfy. In
  Iris, we have decided to focus on two properties:
  - The program won't get stuck.
  - The program satisfies the postcondition.

  In this chapter, we go over how to define these properties and show
  that the weakest precondition satisfies them.

  HeapLang is defined using a step relation. This relation defines how
  an expression can be reduced in a single step.

    [prim_step e1 σ1 κs e2 σ2 efs]

  Here, [e1] is the expression we want to reduce, and [σ1] is the
  current state of the machine. [e2] and [σ2] are then the new
  expression and new state. [efs] is a list of expressions representing
  new threads spawned. Finally, [κs] represents a list of something
  called observations. We won't use these, so [κs] will remain empty.

  This relation isn't very nice to work with by itself. To fix this, we
  package the state of the program into what we call a configuration.
  Notice that this configuration takes a list of expressions. These
  represent all the threads that are currently running.
*)

Definition cfg : Type := list expr * state.

(**
  Now, let us define steps in terms of configurations. To model the
  non-sequential behaviour of threads, we define steps to be a step in
  any thread.
*)
Inductive step (ρ1 ρ2 : cfg) : Prop :=
  step_atomic e1 σ1 e2 σ2 efs t1 t2 :
    ρ1 = (t1 ++ e1 :: t2, σ1) →
    ρ2 = (t1 ++ e2 :: t2 ++ efs, σ2) →
    prim_step e1 σ1 [] e2 σ2 efs →
    step ρ1 ρ2.

(**
  With this, we can define multiple steps as the reflexive transitive
  closure ([rtc]) of [step].

  Now, a program is stuck if any thread cannot take a step and is not a
  value. Conversely, a thread is not stuck if it is either a value or
  can take a step.
*)
Definition not_stuck e σ :=
  is_Some (to_val e) ∨ ∃ e' σ' efs, prim_step e σ [] e' σ' efs.

(**
  With this, we can now express the first adequacy criterion: a program
  will not get stuck if all possible future configurations are not
  stuck.

  [∀ t σ' e', rtc step ([e], σ) (t, σ') → e' ∈ t → not_stuck e' σ']

  Likewise, for the second criterion, we say that a program satisfies a
  postcondition when the main thread terminates to a value, and that
  value satisfies the postcondition.

  [∀ t σ' v, rtc step ([e], σ) (of_val v :: t, σ') → φ v σ']

  Together, these two properties define [adequate]. However, [adequate]
  takes an extra parameter of type [stuckness]. This parameter specifies
  whether adequacy includes the first criterion.

  The proof that the weakest precondition implies adequacy is:

  [[
    heap_adequacy Σ `{!heapGpreS Σ} s e σ φ : ∀ _ : heapGS Σ,
      inv_heap_inv -∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝}} → adequate s e σ (λ v σ,
      φ v)
  ]]

  To use this statement, we have to actually instantiate [Σ]. It needs
  to contain all the kinds of resources we needed to prove the weakest
  precondition. Let us use [prog] from the Spin Lock chapter as an
  example. To prove [prog_spec], we used the resource of heaps as well
  as tokens. The resources needed by the resource of heaps are all
  contained in [heapΣ]. Likewise, the resources needed by token
  ([exclR unitO]) are contained in [tokenΣ].
*)

Definition progΣ : gFunctors := #[
  heapΣ; (* The resources required by HeapLang *)
  tokenΣ (* The resources we used for spin-lock *)
].

(** Finally, we can combine the pieces to prove adequacy. *)
Lemma prog_adequacy σ :
  adequate NotStuck prog σ (λ v _, v = #0 ∨ v = #1).
Proof.
  apply (heap_adequacy progΣ).
  iIntros "%_ _".
  iApply prog_spec.
Qed.

(** 
  With this, we now have a _closed_ proof that [prog] does not get
  stuck, and if it terminates at some value [v], then [v = #0 ∨ v = #1].
*)
