From iris.algebra Require Import excl.
From iris.heap_lang Require Import adequacy lang proofmode notation par.
From solutions Require Import spin_lock.

(**
  Thus far we've assumed that the weakest precondition is correct. But
  what does that even mean? This is what is called adequacy, and its
  definition depends on the properties we want it to satisfy. In Iris
  we've decided to focus on two properties:
  - The program won't get stuck.
  - The program satisfies the postcondition.

  In this file, we'll go over how to define these properties and show
  that the weakest precondition satisfies them.

  HeapLang is defined using a step relation. This relation defines how
  an expression can be reduced in a single step.
  [prim_step e1 σ1 κs e2 σ2 efs]
  Here [e1] is the expression we want to reduce, and [σ1] is the
  current state of the machine. [e2] and [σ2] are then the new
  expression and state. [efs] is a list of expressions representing new
  threads spawned. Finally [κs] represents a list of something called
  observations. We won't use these, so κs will remain empty.

  This relation isn't very nice to work with by itself. To fix this
  we will package the state of the program into what we will call a
  configuration. Notice that this configuration takes a list of
  expressions. These represent all the threads that are currently running.
*)

Definition cfg : Type := list expr * state.

(**
  Now let's define steps in terms of configurations. To model the
  non-sequential Steps behaviour of threads, we define steps to be
  a step in any thread.
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

  Now a program is stuck if any thread can't take a step and isn't a
  value. Conversely, a thread is not stuck if it is either a value or
  can take a step.
*)
Definition not_stuck e σ :=
  is_Some (to_val e) ∨ ∃ e' σ' efs, prim_step e σ [] e' σ' efs.

(**
  So a program won't get stuck if all possible future configurations
  aren't stuck.

  [∀ t σ' e', rtc step ([e], σ) (t, σ') → e' ∈ t → not_stuck e' σ']

  Likewise, a program satisfies a postcondition when the main thread
  terminates to a value, that value satisfies that postcondition.

  [∀ t σ' v, rtc step ([e], σ) (of_val v :: t, σ') → φ v σ']

  These two properties together define [adequate]. However [adequate]
  takes an extra parameter of type [stuckness]. This parameter
  specifies whether adequacy includes the first condition.

  The proof that the weakest precondition implies adequacy is:
  [heap_adequacy Σ `{!heapGpreS Σ} s e σ φ :
    ∀ _ : heapGS Σ, inv_heap_inv -∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝}} →
    adequate s e σ (λ v σ, φ v)
  ]

  To use this statement we have to actually instantiate Σ. It needs to
  contain all the kinds of resources we needed to prove the weakest
  precondition. Let's use [prog] from spin_lock. To prove [prog_spec]
  we used the resources of heaplang as well as [exclR unitO]. The
  resources of heaplang are all contained in [heapΣ]. For the camera,
  we use GFunctor to turn it into a gfunctor.
*)
Definition progΣ := #[
  heapΣ; (* The resources required for heaplang itself *)
  GFunctor (exclR unitO) (* The camera we used for spin-lock *)
].

(** Finally we can combine the pieces to prove adequacy. *)
Lemma prog_adequacy σ : adequate NotStuck prog σ (λ v _, v = #0 ∨ v = #1).
Proof.
  apply (heap_adequacy progΣ).
  iIntros "%_ _".
  unshelve iApply prog_spec.
  apply (subG_inG _ (GFunctor (exclR unitO))).
  apply subG_app_r, subG_refl.
Qed.
