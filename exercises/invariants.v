From iris.base_logic.lib Require Export invariants token.
From iris.heap_lang Require Import lang proofmode notation par.

(* ################################################################# *)
(** * Invariants *)

(* ================================================================= *)
(** ** A Motivating Example *)

(**
  Let us make a simple multi-threaded program.
*)
Definition prog : expr :=
  let: "l" := ref #0 in
  Fork ("l" <- #1);;
  !"l".

(**
  This program will race to either update [l] or read [l], meaning the
  resulting value could be either [0] or [1].
*)

Section proofs.
Context `{!heapGS Σ}.

Lemma wp_prog : {{{ True }}} prog {{{ v, RET v; ⌜v = #0⌝ ∨ ⌜v = #1⌝ }}}.
Proof.
  iIntros "%Φ _ HΦ".
  rewrite /prog.
  wp_alloc l as "Hl".
  wp_pures.
  (**
    Fork does not have its own tactic. Instead, we use its
    specification. This specification forces us to split our resources
    between the threads.
  *)
  wp_apply (wp_fork with "[Hl]").
  (**
    As such we have to pick a thread to own [l]. But as both threads
    need to access [l], we are stuck.
  *)
Abort.

(* ================================================================= *)
(** ** Introduction to Invariants *)

Section inv_intro.

(**
  As the above program illustrates, some resources are required by
  multiple threads simultaneously. If those resources are not shareable
  (i.e. persistent), then we will get stuck, as in the example above.
  To get around this problem, we can devise an invariant for said
  resources. That is, we come up with a proposition [P] which describes
  the resources in a way that is always true, no matter where in the
  program we are, or how threads have interleaved. We can then use Iris'
  invariant functionality to assert that [P] is an invariant: [inv N P].
  Here, [N] is a `namespace', which we may think of as the name of the
  invariant.

  The key property of invariants that solve our problem is that they are persistent.
*)

Lemma inv_persist (N : namespace) (P : iProp Σ) :
  Persistent (inv N P).
Proof. apply _. Qed.

(**
  Thus, if we can come up with a proposition [P] describing our
  resources correctly throughout the entire program, then we can
  _allocate_ [P] as an invariant, and supply said invariant to the
  threads requiring access to the resources described by [P]. To access
  [P] from the invariant, threads must then _open_ the invariant.

  The next two sub-sections cover how to open and allocate invariants.
*)

(* ----------------------------------------------------------------- *)
(** *** Opening Invariants *)

(**
  Once we have an invariant [inv N P], we can use the [iInv] tactic to
  _open_ the invariant, granting us access to [P]. To ensure soundness
  of the logic, there are some restrictions to opening an invariant.

  Firstly, an invariant can only be opened once before being closed
  again. This is enforced in Iris through `masks'. A mask can be thought
  of as a set that tracks which invariants are closed. If no invariants
  are open, the mask is [⊤]. If only invariant [N] is open, the mask is
  [⊤ ∖ ↑N]. If we have two invariants [N1] and [N2] that are both open,
  the mask is [⊤ ∖ ↑N1 ∖ ↑N2], and so on. Only invariants that are in
  the mask can be opened. Thus, if invariant [N] is not in the mask
  (i.e. it is open), then we cannot use [iInv] to open [N] again.
  Closing the invariant puts [N] back into the mask, allowing it to be
  opened again. Closing an open invariant [iInv N P] corresponds to
  proving that [P] still holds.

  We can only open an invariant if the goal has a mask which contains
  [N]. As such, if the goal is a generic proposition, we cannot open any
  invariants.
*)

Lemma inv_open_fail (N : namespace) (P Q : iProp Σ) :
  inv N (P) ⊢ Q.
Proof.
  iIntros "Hinv".
  Fail iInv "Hinv" as "HP".
Abort.

(**
  An example of a goal that has a mask is a weakest precondition. That
  is, the shape of a weakest precondition is actually

    [WP e @ E {{ Φ }}]

  with [E] being the mask. However, when the mask is [⊤], it is
  notationally hidden, which is why we have yet to see it.

  Another example of a goal permitting invariant openings is the _fancy
  update modality_, which essentially just adds a mask to the update
  modality. A fancy update modality is written [|={E}=>] for a mask [E].
  The fancy update modality is like the update modality, but with
  support for invariants: if the goal contains [|={E}=>], then we are
  allowed to open all invariants in [E].
*)

(**
  Another restriction on invariant openings is that, when the goal is a
  weakest precondition [WP e {{Φ}}], an invariant can be open for at
  most one program step. This is enforced by requiring [e] to be an
  atomic expression, meaning it reduces to a value in one step. After
  the one step, we have to close the invariant again.
  
  Let us try to see these concepts in action with a simple example.
*)

Lemma inv_open_example_attempt_1 (N : namespace) (l : loc) :
  inv N (l ↦ #1) ⊢ WP !#l + !#l {{ v, ⌜v = #2⌝ }}.
Proof.
  iIntros "#Hinv".
  (**
    To prove the WP, we must get access to [l ↦ #1] from the invariant.
    As discussed, to open the invariant, the expression must be atomic.
    Let us ignore this and try to open the invariant anyway.
  *)
  iInv "Hinv" as "Hl".
  (** 
    Iris now asks us to prove that [!#l + !#l] is atomic. Hence we are
    stuck.
  *)
Abort.

(** 
  When the expression in the WP is not atomic, we can make it so by
  _binding_ the expression we want to open the invariant around.
*)

Lemma inv_open_example_attempt_2 (N : namespace) (l : loc) :
  inv N (l ↦ #1) ⊢ WP !#l + !#l {{ v, ⌜v = #2⌝ }}.
Proof.
  iIntros "#Hinv".
  (**
    We now first bind the expression (!#l), which _is_ atomic.
  *)
  wp_bind (!#l)%E.
  (**
    This allows us to open the invariant.
  *)
  iInv "Hinv" as "Hl".
  (**
    This tactic did quit a bit, so let us break it down.

    Firstly, notice that we got the points-to predicate from the
    invariant. A small caveat is that we only get the predicate later.
    This is usually not an issue, as the later can be removed in most
    cases, which we discuss in a later chapter.

    Secondly, the postcondition of the weakest precondition in the goal
    got augmented with [|={⊤ ∖ ↑N}=> ▷ l ↦ #1]. After stepping through
    the current WP, we will have to prove this proposition to show that
    the invariant [l ↦ #1] still holds. The fancy update modality is
    there to stop us from opening the invariant to prove that the
    invariant still holds.

    Thirdly, notice the mask on the weakest precondition: [⊤ ∖ ↑N]. This ensures
    that we cannot open [N] again to prove the WP. If we tried to open
    the invariant again, Iris would ask us to show that [↑N] is a subset
    of [⊤ ∖ ↑N]. For the sake of demonstration, let us try this.
  *)
  iInv "Hinv" as "Hl'".
  (**
    This is of course impossible to prove, so we are stuck.
  *)
Abort.

Lemma inv_open_example (N : namespace) (l : loc) :
  inv N (l ↦ #1) ⊢ WP !#l + !#l {{ v, ⌜v = #2⌝ }}.
Proof.
  iIntros "#Hinv".
  wp_bind (!#l)%E.
  iInv "Hinv" as "Hl".
  (**
    Having opened the invariant, we now have access to [l ↦ #1], which
    we can use to prove the WP.
  *)
  wp_load.
  (**
    Now that we have used our invariant to take the one step, we must
    close the invariant by proving that the invariant still holds.
  *)
  iSplitL "Hl".
  { iApply "Hl". }
  (**
    Even though we have now closed the invariant, the fancy
    update modality still prevents us from opening the invariant.
    However, we can always introduce a fancy update modality with
    [iModIntro].
    *)
  iModIntro.
  (**
    Since the mask on the weakest precondition in the goal is implicitly
    [⊤], we can open [N] again.
  *)
  (**
    We have now used the invariant to reduce the right-hand [!#l].
    Reducing the left-hand dereference is done analogously.
    First we bind the dereference.
  *)
  wp_bind (!#l)%E.
  (** Then we open the invariant. *)
  iInv "Hinv" as "Hl".
  (** Next, we use the contents of the invariant to prove the dereference. *)
  wp_load.
  (** Finally, we close the invariant by proving it still holds. *)
  iSplitL "Hl".
  { iApply "Hl". }
  (** 
    Now, both dereferences have been reduced, so we easily prove the
    remaining WP.
  *)
  iModIntro.
  wp_pure.
  done.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Allocating Invariants *)

(**
  Now we know how to open invariants, but how are they created in the
  first place?

  Once we have devised a proposition [P] describing our resources
  invariantly, we can turn [P] into an invariant [inv N P] using the
  [inv_alloc] lemma. The lemma states

      [inv_alloc : ▷P -∗ |={E}=> inv N P]

  That is, to turn [P] into an invariant, we must prove that [P] is true
  after one step (or, if we can, in the current step). As with
  allocation of ownership of resources, we do not get access to the
  invariant immediately; it is behind a fancy update modality
  [|={E}=>].

  Let us see this in action. First, we give a name to the invariant we
  wish to allocate.
*)
Let N := nroot .@ "myInvariant".

(**
  Now, let us try to prove the following (quite contrived)
  specification.
*)
Lemma inv_alloc_loc :
  {{{ True }}} ref #0 {{{(l : loc), RET #l; inv N (l ↦ #0)}}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_alloc l as "Hl".
  (**
    We now wish to allocate the invariant using [inv_alloc]. To strip
    the fancy update modality immediately, we use the [iMod] tactic.
    We can do this since the goal contains a fancy update modality.
  *)
  iMod (inv_alloc N _ (l ↦ #0) with "[Hl]") as "Hinv".
  (**
    As discussed, in order to allocate the invariant, we must prove that
    it holds after one step.
  *)
  { iNext. done. }
  (**
    With the invariant allocated, we can finish the proof.
  *)
  iModIntro.
  iApply "HΦ".
  iApply "Hinv".
Qed.

(**
  Side note: The above proof demonstrates why, when we have to prove the
  postcondition of a WP, we have to prove it _behind_ a fancy update
  modality. Having the fancy update modality in the goal allows us to
  allocate/open invariants, and allocate/update resources.
*)

End inv_intro.

(* ================================================================= *)
(** ** A Motivating Example - Take Two *)

(**
  Armed with the knowledge of invariants, let us attempt to prove the
  specification from the beginning of the chapter again. We start by
  giving a name to our invariant.
*)
Let N := nroot .@ "prog".

(**
  So what should the invariant be? The resource of interest is what the
  location [l] points to, and throughout the program, it points to
  either [0] or [1]. As such, we will create an invariant which captures
  that [l] points to either [0] or [1].
*)
Definition prog_inv (l : loc) : iProp Σ :=
  ∃ v, l ↦ v ∗ (⌜v = #0⌝ ∨ ⌜v = #1⌝).

Lemma wp_prog : {{{ True }}} prog {{{ v, RET v; ⌜v = #0⌝ ∨ ⌜v = #1⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite /prog.
  wp_alloc l as "Hl".
  wp_pures.
  (** We now allocate our [prog_inv] invariant, using [inv_alloc]. *)
  iMod (inv_alloc N _ (prog_inv l) with "[Hl]") as "#Hinv".
  (** We prove that the invariant is currently true. *)
  {
    iNext.
    iExists #0.
    iFrame.
    by iLeft.
  }
  (**
    With the invariant allocated and in the persistent context, we can
    use it to prove both threads.
  *)
  wp_apply wp_fork.
  - (**
      As [#l <- #1] is atomic and the mask on the WP is [⊤], we can open the invariant.
    *)
    iInv "Hinv" as "(%v & Hl & _)".
    (** We use the obtained points-to predicate to prove the WP. *)
    wp_store.
    (** We close the invariant... *)
    iSplitL.
    {
      iIntros "!> !>".
      iExists #1.
      iFrame.
      by iRight.
    }
    (** ... and finish the proof of the forked thread. *)
    done.
  - (* exercise *)
Admitted.

End proofs.

(* ================================================================= *)
(** ** Another Example *)

(**
  Let us look at another program. This program will create a thread to
  continuously increment a counter, while the main thread will read the
  counter at some point. As such, this program should produce some
  non-negative number. However, we will only prove that it returns a
  number. Later, we will see other tools that will allow us to refine
  this.
*)

Definition prog2 : expr :=
  let: "l" := ref #0 in
  Fork ((
    rec: "go" <> :=
      "l" <- !"l" + #1;;
      "go" #()
  ) #());;
  !"l".

Section proofs.
Context `{!heapGS Σ}.
Let N := nroot .@ "prog2".

(**
  Our invariant will simply be that the location points to an integer.
*)
Definition prog2_inv (l : loc) : iProp Σ :=
  ∃ i : Z, l ↦ #i.

Lemma prog2_spec : {{{ True }}} prog2 {{{ (i : Z), RET #i; True }}}.
Proof.
  iIntros "%Φ _ HΦ".
  rewrite /prog2.
  wp_alloc l as "Hl".
  wp_pures.
  (** Like before, we allocate the invariant. *)
  iMod (inv_alloc N _ (prog2_inv l) with "[Hl]") as "#I".
  { iNext. by iExists 0. }
  wp_apply wp_fork.
  - wp_pure.
    (** We use löb induction to accent the recursive calls. *)
    iLöb as "IH".
    wp_pures.
    (**
      We need to access the contents of the invariant to step through
      the read of [l] and the store to [l]. However, invariants can only
      be open for one step, so we are forced to open the invariant twice
      in succession.
      First, we open it around the read.
    *)
    wp_bind (! _)%E.
    iInv "I" as "[%i Hl]".
    wp_load.
    iModIntro.
    iSplitL "Hl".
    { by iExists i. }
    wp_pures.
    (**
      Next, we open it around the store.
    *)
    wp_bind (_ <- _)%E.
    iInv "I" as "[%j Hl]".
    wp_store.
    iModIntro.
    iSplitL "Hl".
    { by iExists (i + 1)%Z. }
    do 2 wp_pure.
    done.
  - wp_pures.
    iInv "I" as "[%i Hl]".
    wp_load.
    iModIntro.
    iSplitL "Hl".
    { by iExists i. }
    by iApply "HΦ".
Qed.

End proofs.
