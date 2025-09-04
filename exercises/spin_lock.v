From iris.algebra Require Import excl.
From iris.base_logic.lib Require Export invariants token.
From iris.heap_lang Require Import lang proofmode notation.

(* ################################################################# *)
(** * Case Study: Spin Lock *)

(* ================================================================= *)
(** ** Implementation *)

(**
  A spin-lock consists of a pointer to a boolean. This boolean tells us
  whether the lock is currently locked or not.

  To make a new lock, we simply allocate a new boolean which is
  initially [false], signifying that the lock is unlocked.
*)
Definition mk_lock : val :=
  λ: <>, ref #false.

(**
  To acquire the lock, we use [CAS l false true] (compare and set). This
  instruction atomically writes [true] to location [l] if [l] contains
  [false]. The [CAS] instruction then returns a boolean, signifying
  whether [l] was updated. If the [CAS] fails, it means that the lock is
  currently acquired somewhere else. So we simply try again until the lock
  is free.
*)
Definition acquire : val :=
  rec: "acquire" "l" :=
  if: CAS "l" #false #true then
    #()
  else
    "acquire" "l".

(**
  To release a lock, we simply update the boolean to [false]. As such,
  it is only safe to call release when we are the ones who locked it.
*)
Definition release : val :=
  λ: "l", "l" <- #false.

(* ================================================================= *)
(** ** Representation Predicates *)

(**
  Intuitively, a lock protects resources. For instance, it can protect a
  location in memory by allowing only one thread to access it at a time.
  In terms of ownership, when the lock is unlocked and no thread is
  trying to access the protected resource, then the resource is _owned
  by the lock_. When a thread acquires the lock, ownership of the
  protected resource is transferred to the acquiring thread. Once said
  thread releases the lock, it must transfer the protected resources
  back to the lock.

  Therefore, our representation predicate will be parametrised by an
  arbitrary predicate [P], which describes the resources the lock should
  protect.
*)

Section proofs.
Context `{heapGS Σ}.

(**
  We use ghost state to describe that the lock is only ever acquired
  once at a time. The core property we are after here is exclusivity. So
  naturally, we will use the exclusive RA. Recall that this resource
  algebra is generic. However, we just need one exclusive element, so we
  will instantiate the exclusive RA with the unit OFE: [exclR unitO].
  Note that this is exactly the resource algebra we used to define
  tokens. As such, we will reuse tokens here but rename them to clarify
  their intent.
*)
Context `{!tokenG Σ}.

(**
  The knowledge that we have acquired the lock is then represented by
  ownership of the token.
*)
Definition locked γ : iProp Σ := token γ.

(**
  Allocation and exclusivity of the [locked] predicate then follows
  directly from the properties of the token.
*)
Lemma locked_alloc : ⊢ |==> ∃ γ, locked γ.
Proof. apply token_alloc. Qed.

Lemma locked_excl γ : locked γ -∗ locked γ -∗ False.
Proof. apply token_exclusive. Qed.

(**
  We will need our representation predicate for the lock, [is_lock], to
  be persistent so that it can be shared among participating threads.
  Therefore, we will be needing an invariant. The invariant states that
  the location representing the lock, [l], maps to a boolean [b], and if
  [b] is [false], meaning the lock is unlocked, then the invariant owns
  both the protected resources and the [locked] predicate.
*)
Let N := nroot .@ "lock".

Definition lock_inv γ l P : iProp Σ :=
  ∃ b : bool, l ↦ #b ∗
  if b then True
  else locked γ ∗ P.

(**
  The representation predicate then just asserts that the value
  representing the lock is a location which satisfies the lock
  invariant.
*)
Definition is_lock γ v P : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ inv N (lock_inv γ l P).

(* ================================================================= *)
(** ** Specifications *)

(**
  Making a new lock consists of giving away ownership of the resources
  to be protected, [P], to the lock.
*)
Lemma mk_lock_spec P :
  {{{ P }}} mk_lock #() {{{ γ v, RET v; is_lock γ v P }}}.
Proof.
  iIntros "%Φ HP HΦ".
  wp_lam.
  wp_alloc l as "Hl".
  iMod locked_alloc as "[%γ Hγ]".
  iMod (inv_alloc N _ (lock_inv γ l P) with "[HP Hl Hγ]") as "I".
  {
    iNext.
    iExists false.
    iFrame.
  }
  iModIntro.
  iApply "HΦ".
  iExists l.
  by iFrame.
Qed.

(**
  Acquiring the lock should grant access to the protected resources as
  well as knowledge that the lock has been locked.
*)
Lemma acquire_spec γ v P :
  {{{ is_lock γ v P }}} acquire v {{{ RET #(); locked γ ∗ P }}}.
Proof.
  iIntros "%Φ (%l & -> & #I) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (CmpXchg _ _ _).
  iInv "I" as ([]) "[Hl Hγ]".
  - wp_cmpxchg_fail.
    iModIntro.
    iSplitL "Hl Hγ".
    {
      iNext.
      iExists true.
      iFrame.
    }
    wp_pures.
    wp_apply ("IH" with "HΦ").
  - wp_cmpxchg_suc.
    iModIntro.
    iSplitL "Hl".
    {
      iNext.
      iExists true.
      iFrame.
    }
    wp_pures.
    iModIntro.
    iApply ("HΦ" with "Hγ").
Qed.

(**
  Releasing the lock consists of transferring back the protected
  resources and the [locked] predicate to the lock.
*)
Lemma release_spec γ v P :
  {{{ is_lock γ v P ∗ locked γ ∗ P }}} release v {{{ RET #(); True }}}.
Proof.
  (* exercise *)
Admitted.

(* ================================================================= *)
(** ** Example Client *)

(** Consider the following client of lock. *)
Definition prog : expr :=
  let: "x" := ref #0 in
  let: "l" := mk_lock #() in
  Fork (
    acquire "l";;
    "x" <- #7;;
    "x" <- #1;;
    release "l"
  );;
  acquire "l";;
  !"x".

(**
  [x] can take on the values of [0], [1], and [7]. However, we should
  not observe [7], as it is overwritten before the lock is released.
*)
Lemma prog_spec : ⊢ WP prog {{ v, ⌜v = #0 ∨ v = #1⌝}}.
Proof.
  rewrite /prog.
  wp_alloc x as "Hx".
  wp_pures.
  (**
    For this program, the resource to be protected is the points-to
    predicate for [x], but where the value pointed to by [x] can be only
    [0] or [1].
  *)
  wp_apply (mk_lock_spec (∃ v, x ↦ v ∗ ⌜v = #0 ∨ v = #1⌝) with "[Hx]").
  {
    iExists #0.
    iFrame.
    by iLeft.
  }
  iIntros "%γ %l #Hl".
  wp_pures.
  wp_apply wp_fork.
  - wp_apply (acquire_spec with "Hl").
    iIntros "(H & %v & Hx & _)".
    wp_pures.
    wp_store.
    wp_store.
    wp_apply (release_spec with "[$Hl $H Hx]"); last done.
    iExists #1.
    iFrame.
    by iRight.
  - wp_pures.
    wp_apply (acquire_spec with "Hl").
    iIntros "(_ & %v & Hx & Hv)".
    wp_pures.
    wp_load.
    done.
Qed.

End proofs.
