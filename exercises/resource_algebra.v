From iris.algebra Require Import cmra.
From iris.heap_lang.lib Require Export par.
From iris.heap_lang Require Import proofmode notation.

(**
  In this file, we will define a new cmra (pronounced camera) from
  scratch. These are used as an abstract state of the program called
  ghost state. To motivate the camera we will look at the following
  program:
*)
Definition prog : expr :=
  let: "l" := ref #4 in
  ("l" <- !"l" + #1) ||| ("l" <- !"l" + #1);;
  !"l".

(**
  We wish to show that the program terminates with a number that is at
  least 5. To do this we will use an invariant separated into the
  different abstract states of our program. At the outset, the
  location will map to 4. During the execution of the threads, the
  location will be changed to either 5 or 6. However, we just care about
  that it must become greater than 4. As such we will have the
  following states.
*)

Inductive state :=
  (** The starting state *)
  | Start
  (** The state after the location has been increased. *)
  | Final
  (**
    An invalid state we will use to restrict the operations on the
    state.
  *)
  | Invalid.

(**
  Now we need to define an equivalence relation on the state. However,
  we just want states to be equivalent exactly when they are equal.
*)
Global Instance state_equiv_instance : Equiv state := eq.
Global Instance state_equiv_equivalence : Equivalence (≡@{state}) := _.
(**
  To help convert between equivalence and equality we can tell Iris
  that they coincide. Which in this case is trivial.
*)
Global Instance state_leibniz_equiv : LeibnizEquiv state := _.

(**
  To define a camera we first need to define its ofe (Ordered family
  of equivalences). An ofe encodes a kind of time dependence, but most
  cameras don't depend on time and are thus what is called discrete.
  To quickly define a discrete ofe, we can use [discrete_ofe_mixin].
  This will produce a warning because we are reusing a definition in
  a canonical projection. However, this warning can be safely ignored
  in this case.
*)
Canonical stateO := Ofe state (discrete_ofe_mixin _).

(**
  To use the state as a resource we need to turn it into a camera.
*)
Section cmra.

(**
  First of all, we need to define how fragments of state can be
  combined. We define [Final ⋅ Final] as [Final], and make every other
  combination [Invalid]. In particular, this means that [Start] will
  be exclusive, while [Final] can be shared.
*)
Local Instance state_op_instance : Op state := λ s1 s2,
  match s1, s2 with
  | Final, Final => Final
  | _, _ => Invalid
  end.

(**
  Next, we have to define which fragments of state are valid.
  Naturally, we define everything except for [Invalid] as valid.
*)
Local Instance state_valid_instance : Valid state := λ s,
  match s with
  | Start | Final => True
  | Invalid => False
  end.

(**
  Finally, we need to define the core. This defines what ownership is
  persistent.
*)
Local Instance state_pcore_instance : PCore state := λ s,
  match s with
  | Start => None
  | _ => Some s
  end.

(**
  Because our camera is discrete, we only need to prove RAMixin,
  rather than the full CmraMixin.
*)
Lemma state_ra_mixin : RAMixin state.
Proof.
  split.
  - solve_proper.
  - naive_solver.
  - solve_proper.
  - by intros [] [] [].
  - by intros [] [].
  - by intros [] [].
  - by intros [] [].
  - intros [] _ [] [[] ->] e; try done.
    all: eexists; split; first done.
    all: try by exists Invalid.
    by exists Final.
  - by intros [] [].
Qed.

(**
  We can now package this into a cmra which will add one more
  operation [✓{_} _]. For discrete cameras this is the same as [✓ _].
*)
Canonical Structure stateR := discreteR state state_ra_mixin.
(**
  To help the Iris proofmode, we'll register stateR as a discrete
  cmra.
*)
Global Instance state_cmra_discrete : CmraDiscrete state.
Proof. apply discrete_cmra_discrete. Qed.

End cmra.

Global Instance Start_exclusive : Exclusive Start.
Proof. by intros []. Qed.

Global Instance Final_core_id : CoreId Final.
Proof. red. done. Qed.

(**
  We want the ability to change the state from [Start] to [Final].
  However, we will instead prove a more general fact: That any state
  can update to [Final]
*)
Lemma state_update s : s ~~> Final.
Proof.
  (**
    As we are working with a discrete cmra we can simplify this
    statement as follows.
  *)
  unfold "~~>".
  setoid_rewrite <-cmra_discrete_valid_iff.
  intros _ mz H.
  by destruct s, mz as [[| |]|].
Qed.

Section proofs.
Context `{!heapGS Σ, !spawnG Σ, !inG Σ stateR}.

Let N := nroot .@ "state".

(**
  We can create new resources via the basic update modality [|==> P].
  This operation states that P holds after an update of resources.
  To work with the basic update modality we can use two facts:
  - [P ⊢ |==> P]
  - [(P ⊢ |==> Q) ⊢ (|==> P ⊢ |==> Q)]
  Rather than working with these facts directly, we can use
  [iModIntro] and [iMod] respectively.
*)
Lemma alloc_Start : ⊢ |==> ∃ γ, own γ Start.
Proof.
  (** To allocate a new resource we use [own_alloc] *)
  iPoseProof (own_alloc Start) as "H".
  (** We are naturally only allowed to allocate valid resources *)
  { done. }
  (** We can remove the bupd from "H" as we are proving a bupd *)
  iMod "H" as "H".
  (** We can now use iModIntro or the "!>" introduction pattern. *)
  iModIntro.
  done.
Qed.

(**
  Likewise, owning a resource means it is valid.
  A quick note: [✓ _] and [⌜✓ _⌝] are different, they only coincide
  when the cmra is discrete.
*)
Lemma state_valid γ (s : state) : own γ s ⊢ ⌜✓ s⌝.
Proof.
  iIntros "H".
  iPoseProof (own_valid with "H") as "%H".
  done.
Qed.

(**
  Next, we can lift [state_update] to ownership using [own_valid].
  As a shorthand for [_ -∗ |==> _] we write [_ ==∗ _].
*)
Lemma state_bupd γ (s : state) : own γ s ==∗ own γ Final.
Proof.
  iApply own_update.
  apply state_update.
Qed.

(**
  We can now define the invariant as follows
*)
Definition state_inv γ (l : loc) (x : Z) : iProp Σ :=
  ∃ y : Z, l ↦ #y ∗ (own γ Start ∗ ⌜x = y⌝ ∨ own γ Final ∗ ⌜x < y⌝%Z).

(**
  Rather than proving the entire program at once, we will split it
  into 3 pieces. Starting with the 2 threads.

  Note that WP contains a bupd, meaning we can update resources in
  between steps.
*)
Lemma thread_spec γ l (x : Z) : {{{inv N (state_inv γ l x)}}} #l <- !#l + #1 {{{RET #(); own γ Final}}}.
Proof.
  (* exercise *)
Admitted.

Lemma body_spec l (x : Z) : {{{l ↦ #x}}} (#l <- !#l + #1) ||| (#l <- !#l + #1);; !#l {{{(y : Z), RET #y; ⌜x < y⌝%Z}}}.
Proof.
  (* exercise *)
Admitted.

Lemma prog_spec : {{{True}}} prog {{{(y : Z), RET #y; ⌜5 ≤ y⌝%Z}}}.
Proof.
  (* exercise *)
Admitted.

End proofs.

(**
  Iris ships with a bunch of different cmras you can use out of the
  box. Rather than creating new resources for every new situation, we
  can instead compose existing cmras. Our state camera corresponds to
  [csum (excl ()) (agree ())].

  The available cameras can be found here:
  https://gitlab.mpi-sws.org/iris/iris/-/tree/master/iris/algebra
*)
