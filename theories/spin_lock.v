From iris.algebra Require Import excl.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.

(**
  A spin-lock consists of a pointer to a boolean. This boolean tells us
  whether the lock is currently locked or not.

  To make a new lock, we simply allocate a new boolean.
*)
Definition mk_lock : val :=
  λ: <>, ref #false.

(**
  To acquire the lock, we use [CAS l false true] (compare and set).
  This is an atomic operation that updated l to true if l was false.
  [CAS] then evaluates to whether l was updated.
  If the [CAS] fails, it means that the lock is currently acquired
  somewhere else. So we simply again, until the lock is free.
*)
Definition acquire : val :=
  rec: "acquire" "l" :=
  if: CAS "l" #false #true then
    #()
  else
    "acquire" "l".

(**
  To release a lock, we simply update the boolean to false. As such
  it is only safe to call release when we are the ones who locked it.
*)
Definition release : val :=
  λ: "l", "l" <- #false.

Section proofs.
Context `{heapGS Σ}.
Let N := nroot .@ "lock".

(**
  We use ghost state to describe that the lock is only ever acquired
  once at a time. To do this we simply need ghost state that is
  exclusive. So naturally we will use the exclusive camera. This
  camera is generic over state, however, we don't need this feature. So
  we will instantiate it with the unit type.
*)
Context `{!inG Σ (exclR unitO)}.

(**
  We will think of the name of our ghost state as the name of the
  lock. Its invariant will be that l maps to a boolean b, and if
  b is false, meaning the lock is unlocked, then the invariant owns
  both the resource and the critical area protected by the lock.
*)
Definition lock_inv γ l P : iProp Σ :=
  ∃ b : bool, l ↦ #b ∗
  if b then True
  else own γ (Excl ()) ∗ P.

Definition is_lock γ v P : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ inv N (lock_inv γ l P).

(**
  The knowledge that we have acquired is then represented by
  ownership of the resource.
*)
Definition locked γ : iProp Σ := own γ (Excl ()).

(**
  We need the ghost state to prove that this is exclusive.
*)
Lemma locked_excl γ : locked γ -∗ locked γ -∗ False.
Proof.
  iIntros "H1 H2".
  iPoseProof (own_valid_2 with "H1 H2") as "%H".
  cbv in H.
  done.
Qed.

(**
  Making a new lock consists of giving away ownership of the critical
  area to the lock.
*)
Lemma mk_lock_spec P : {{{ P }}} mk_lock #() {{{ γ v, RET v; is_lock γ v P }}}.
Proof.
  iIntros "%Φ HP HΦ".
  wp_lam.
  wp_alloc l as "Hl".
  iMod (own_alloc (Excl ())) as "[%γ Hγ]".
  { done. }
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
  Acquiring the lock should result in access to the critical area,
  as well as knowledge that the lock has been locked.
*)
Lemma acquire_spec γ v P : {{{ is_lock γ v P }}} acquire v {{{ RET #(); locked γ ∗ P }}}.
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

Lemma release_spec γ v P : {{{ is_lock γ v P ∗ locked γ ∗ P }}} release v {{{ RET #(); True }}}.
Proof.
  iIntros "%Φ ((%l & -> & I) & Hγ & HP) HΦ".
  wp_lam.
  iInv "I" as "(%b & Hl & _)".
  wp_store.
  iModIntro.
  iSplitL "Hγ Hl HP".
  - iNext.
    iExists false.
    iFrame.
  - by iApply "HΦ".
Qed.

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
  x can take on the values of 0, 1, and 7. However, we should not
  observe 7, as it is overridden before the lock is released.
*)
Lemma prog_spec : ⊢ WP prog {{ v, ⌜v = #0 ∨ v = #1⌝}}.
Proof.
  rewrite /prog.
  wp_alloc x as "Hx".
  wp_pures.
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
