From iris.algebra Require Export excl_auth frac_auth.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation par.

(**
  Let's make a simple multi-threaded program. We can use [Fork e] to
  create a new thread to run [e]. As such the following program will
  race to either update [l] or read [l]. Meaning the resulting value
  could be either 0 or 1.
*)
Definition prog : expr :=
  let: "l" := ref #0 in
  Fork ("l" <- #1);;
  !"l".

Section proofs.
Context `{!heapGS Σ}.

Lemma wp_prog : {{{ True }}} prog {{{ v, RET v; ⌜v = #0⌝ ∨ ⌜v = #1⌝ }}}.
Proof.
  iIntros "%Φ _ HΦ".
  rewrite /prog.
  wp_alloc l as "Hl".
  wp_pures.
  (**
    Fork does not have its own tactic. Instead we use its
    specification. This specification forces us to split our resources
    between the threads.
  *)
  wp_apply (wp_fork with "[Hl]").
  (**
    As such we have to pick a thread to own [l]. But as both threads
    need to access [l], we are stuck.
  *)
Abort.

(**
  To get around this, we will use invariants. Invariants are written
  [inv N P] where N is a namespace (Think of it as the name of the
  invariant), and [P] is the proposition we want to make invariant.
  As the name suggests, invariants are propositions that will remain
  true forever. This allows them to be persistent no matter what [P] is.
  
  As stated, invariant need a namespace. This allows invariants to be
  used together as long as they are in different namespaces.
*)
Let N := nroot .@ "stuff".

(**
  In this case we want the invariant to incapsulate ownership of [l]
  as well as its posible values.
*)
Definition prog_inv (l : loc) : iProp Σ :=
  ∃ v, l ↦ v ∗ (⌜v = #0⌝ ∨ ⌜v = #1⌝).

Lemma wp_prog : {{{ True }}} prog {{{ v, RET v; ⌜v = #0⌝ ∨ ⌜v = #1⌝ }}}.
Proof.
  iIntros "%Φ _ HΦ".
  rewrite /prog.
  wp_alloc l as "Hl".
  wp_pures.
  (**
    To create an invariant we use the lemma
    [inv_alloc : ▷P -∗ |={E}=> inv N P].
    In order to deal with the udpdate modality, we will use the iMod
    tactic rather than [iPoseProof] or [iDestruct].
  *)
  iMod (inv_alloc N _ (prog_inv l) with "[Hl]") as "#I".
  {
    iNext.
    iExists #0.
    iFrame.
    by iLeft.
  }
  (**
    As the invariant is persistent, we can now share it between the
    threads.
  *)
  wp_apply wp_fork.
  - (**
      We can use the [iInv] to access the resources in the invariant.
    *)
    iInv "I" as "(%v & Hl & _)".
    (**
      Opening invariants have certain restrictions. It is only
      posible to open invariants over an atomic step, and after this
      step, we must reestablish the invariant.
      Further more, the [@ ⊤ \ ↑N], signifies that the [N] namespace
      has been opened. As such we wont be able to open it twice at the same step.
    *)
    wp_store.
    iSplitL; last done.
    iIntros "!> !>".
    iExists #1.
    iFrame.
    by iRight.
  - wp_pures.
    iInv "I" as "(%v & Hl & #Hv)".
    wp_load.
    iModIntro.
    iSplitL "Hl".
    + iExists v.
      by iFrame.
    + by iApply "HΦ".
Qed.

End proofs.

(**
  Let's look at another program. This program will create a thread to
  increment a counter. While the main thread will read the counter at
  some point. As such, this program should produce some none negative
  number. However, we will only prove that it returns a number. Later,
  we will see other tools that will allow us to refine this.
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
Let N := nroot .@ "other stuff".

(**
  Our invariant wil simply be that the location points to an integer.
*)
Definition prog2_inv (l : loc) : iProp Σ :=
  ∃ i : Z, l ↦ #i.

Lemma prog2_spec : {{{ True }}} prog2 {{{ (i : Z), RET #i; True }}}.
Proof.
  iIntros "%Φ _ HΦ".
  rewrite /prog2.
  wp_alloc l as "Hl".
  wp_pures.
  (**
    Like before, we allocate the invariant.
  *)
  iMod (inv_alloc N _ (prog2_inv l) with "[Hl]") as "#I".
  { iNext. by iExists 0. }
  wp_apply wp_fork.
  - wp_pure.
    (** We use löb induction to accent the recursive calls *)
    iLöb as "IH".
    wp_pures.
    (** If we now try to open the invariant: *)
    iInv "I" as "[%i Hl]".
    (**
      We run into something different to earlier. This new subgoal
      [Atomic] is a typeclass, stating that the program should only
      consist of a single atomic operation. In this case the typeclass
      search fails, because the program infact consists of two
      operations. So it is not atomic.
    *)
    Undo.
    (**
      To get around this, we will use wp_bind to split the program
      into atomic parts.
      Notice that the [%E] is necesary to use the notation.
    *)
    wp_bind (! _)%E.
    iInv "I" as "[%i Hl]".
    wp_load.
    iModIntro.
    iSplitL "Hl".
    { by iExists i. }
    wp_pures.
    (**
      As we know need access to [l] again, we have to do the same
      trick again.
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

(**
  This time we'll use the par operator, to do 2 parallel fetch and
  adds. Again we will only prove that r ends up even.
*)
Definition parallel_add : expr :=
  let: "r" := ref #0 in
  (FAA "r" #2)
  |||
  (FAA "r" #6)
  ;;
  !"r".

Section parallel_add.
Context `{!heapGS Σ, !spawnG Σ}.

(** The invariant is thus that r points to an even integer. *)
Definition parallel_add_inv (r : loc) : iProp Σ :=
  ∃ n : Z, r ↦ #n ∗ ⌜Zeven n⌝.

Lemma parallel_add_spec :
  {{{ True }}} parallel_add {{{ n, RET #n; ⌜Zeven n⌝ }}}.
Proof.
  iIntros "%Φ _ HΦ".
  rewrite /parallel_add.
  wp_alloc r as "Hr".
  wp_pures.
  iMod (inv_alloc nroot _ (parallel_add_inv r) with "[Hr]") as "#I".
  {
    iNext.
    iExists 0.
    iFrame.
  }
  (**
    We don't need information back from the threads, so we will simply
    use [λ _, True] as the post conditions.
  *)
  wp_apply (wp_par (λ _, True%I) (λ _, True%I)).
  - iInv "I" as "(%n & Hr & >%Hn)".
    wp_faa.
    iModIntro.
    iSplitL=>//.
    iModIntro.
    iExists (n + 2)%Z.
    iFrame.
    iPureIntro.
    by apply Zeven_plus_Zeven.
  (* FILL IN HERE *) Admitted.

End parallel_add.
