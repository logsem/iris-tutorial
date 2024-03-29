From iris.algebra Require Import excl.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.

(** HeapLang's primitive concurrency mechanism is the [Fork] construct. The
    operation takes an expression [e] as an argument and spawns a new thread that
    executes [e] concurrently. The operation itself returns the unit value on
    the spawning thread.

    [Fork] does not have dedicated tactical support. Instead, we simply apply
    the lemma [wp_fork]. This lemma is more general than what we need for our
    current use cases, but its specification is as follows:

      [WP e {{_, True}} -∗ ▷ Φ #() -∗ WP Fork e {{v, Φ v}}]

    That is, to show the weakest precondition of [Fork e] we have to show the
    weakest precondition of [e] for a trivial postcondition. The key point is
    that we only require the forked-off thread to be safe---we do not care about
    its return value, hence the trivial postcondition.

    We can use the [Fork] construct to implement other common concurrency
    operators such as [spawn] and [join]. *)

Definition spawn : val :=
  λ: "f",
    let: "c" := ref NONE in
    Fork ("c" <- SOME ("f" #()));;
    "c".

Definition join: val :=
  rec: "join" "c" :=
    match: !"c" with
      NONE => "join" "c"
    | SOME "x" => "x"
    end.

(** [spawn] creates a new thread and a "shared channel" which is used to signal
    when it is done, and the [join] function listens on the channel until the
    spawned thread is done. In contrast to plain [Fork], these two functions
    allow us to wait for a forked-off thread to finish. *)

(** We can then use [spawn] and [join] to define a classical parallel
    composition operator [par]. *)
Definition par : val :=
  λ: "f1" "f2",
  let: "h" := spawn "f1" in
  let: "v2" := "f2" #() in
  let: "v1" := join "h" in
  ("v1", "v2").

(** ... and introduce convenient notation that hides the thunks. *)
Notation "e1 ||| e2" := (par (λ: <>, e1)%V (λ: <>, e2)%V) : val_scope.

(** Our desired specification for [par] is going to look as follows:

    [[
      {{{ P1 }}} e1 {{{ v, RET v; Ψ1 v }}} -∗
      {{{ P2 }}} e2 {{{ v, RET v; Ψ2 v }}} -∗
      {{{ P1 ∗ P2 }}} e1 ||| e2 {{{ v1 v2, RET (v1, v2); Ψ1 v1 ∗ Ψ2 v2 }}}
    ]]

    The rule states that we can run [e1] and [e2] in parallel if they have
    _disjoint_ footprints and that we can verify the two components separately.
    The rule is this reason sometimes also referred to as the _disjoint
    concurrency rule_.

    To show the rule, we will first show separate specifications for the
    auxiliary functions [spawn] and [join]. Since we are using a shared channel
    we will use an invariant to allow the two (concurrently running) threads to
    access it.
*)

Section threads.
Context `{!heapGS Σ}.
Let N := nroot .@ "handle".

(** An initial attempt at stating this invariant looks like follows. *)
Definition handle_inv1 (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ v : val, l ↦ v ∗ (⌜v = NONEV⌝ ∨ ∃ w : val, ⌜v = SOMEV w⌝ ∗ Ψ w).

Definition join_handle1 (v : val) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ inv N (handle_inv1 l Ψ).

(** The stated invariant governs the shared channel (some location [l]) and
    states that either no value has been sent yet, or some value has been sent
    that satisfies the predicate [Ψ].

    Let us try this out. *)

Lemma join_spec (v : val) (Ψ : val → iProp Σ) :
  {{{ join_handle1 v Ψ }}} join v {{{ v, RET v; Ψ v }}}.
Proof.
  iIntros (Φ) "(%l & -> & #I) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (! _)%E.
  iInv "I" as "(%v & Hl & [>-> | (%w & >-> & HΨ)])".
  - wp_load.
    iModIntro.
    iSplitL "Hl".
    {
      iNext.
      iExists NONEV.
      iFrame.
      by iLeft.
    }
    wp_pures.
    by iApply "IH".
  - wp_load.
    iModIntro.
    (** Now we need [HΨ] to reestablish the invariant but we also need it for
        the postcondition. We are stuck... *)
Abort.

(** We need a way to keep track of whether [Ψ w] has been "taken out" of the
    invariant or not. However, we do not have any program state to link it to.
    Instead, we will use _ghost state_ instead to track this information. Iris
    supports different kinds of ghost state, but we will only need one property,
    namely that our ghost state is _exclusive_.

    We will use the camera [excl A]. This is the exclusive camera. It has the
    valid states [Excl a]. Importantly, this state is exclusive, meaning [Excl a
    ⋅ Excl b] is not valid. As we don't care about the value of the state, we
    will simply let [A:=()]. *)
Context `{!inG Σ (excl ())}.

Definition handle_inv (γ : gname) (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ v, l ↦ v ∗ (⌜v = NONEV⌝ ∨ ∃ w, ⌜v = SOMEV w⌝ ∗ (own γ (Excl ()) ∨ Ψ w)).

Definition join_handle (v : val) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ γ (l : loc), ⌜v = #l⌝ ∗ own γ (Excl ()) ∗ inv N (handle_inv γ l Ψ).

Lemma token_alloc : ⊢ |==> ∃ γ, own γ (Excl ()).
Proof. by iApply own_alloc. Qed.

(** Due to the exclusivity of [Excl ()] ownership becomes exclusive as well. *)
Lemma token_excl γ : own γ (Excl ()) -∗ own γ (Excl ()) -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %?.
  cbv in H.
  done.
Qed.

Lemma token_lock (γ : gname) (P : iProp Σ) :
  own γ (Excl ()) -∗ (own γ (Excl ()) ∨ P) -∗ own γ (Excl ()) ∗ P.
Proof.
  iIntros "H1 [H2 | HP]".
  - iExFalso. iApply (token_excl with "H1 H2").
  - iFrame.
Qed.

Lemma spawn_spec (P : iProp Σ) (Ψ : val → iProp Σ) (f : val) :
  {{{ P }}} f #() {{{ v, RET v; Ψ v }}} -∗
  {{{ P }}} spawn f {{{ v, RET v; join_handle v Ψ }}}.
Proof.
  iIntros "#Hf %Φ !> HP HΦ".
  wp_lam.
  wp_alloc l as "Hl".
  wp_pures.
  iMod token_alloc as "[%γ Hγ]".
  iMod (inv_alloc N _ (handle_inv γ l Ψ) with "[Hl]") as "#I".
  {
    iNext.
    iExists NONEV.
    iFrame.
    by iLeft.
  }
  wp_apply (wp_fork with "[Hf HP]").
  - iNext.
    wp_apply ("Hf" with "HP").
    iIntros "%v HΨ".
    wp_pures.
    iInv "I" as "(%w & Hl & _)".
    wp_store.
    iModIntro.
    iSplitL; last done.
    iNext.
    iExists (SOMEV v).
    iFrame.
    iRight.
    iExists v.
    by iFrame.
  - wp_pures.
    iModIntro.
    iApply "HΦ".
    iExists γ, l.
    by iFrame "Hγ I".
Qed.

Lemma join_spec (Ψ : val → iProp Σ) (h : val) :
  {{{ join_handle h Ψ }}} join h {{{ v, RET v; Ψ v }}}.
Proof.
  iIntros (Φ) "(%γ & %l & -> & Hγ & #I) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (! #l)%E.
  iInv "I" as "(%_ & Hl & [>-> | (%w & >-> & [>Hγ' | HΨ])])".
  - wp_load.
    iModIntro.
    iSplitL "Hl".
    {
      iNext.
      iExists NONEV.
      iFrame.
      by iLeft.
    }
    wp_pures.
    iApply ("IH" with "Hγ HΦ").
  - iPoseProof (token_excl with "Hγ Hγ'") as "[]".
  - wp_load.
    iModIntro.
    iSplitL "Hγ Hl".
    {
      iNext.
      iExists (SOMEV w).
      iFrame.
      iRight.
      iExists w.
      by iFrame.
    }
    wp_pures.
    by iApply "HΦ".
Qed.

Lemma par_spec (P1 P2 : iProp Σ) (e1 e2 : expr) (Q1 Q2 : val → iProp Σ) :
  {{{ P1 }}} e1 {{{ v, RET v; Q1 v }}} -∗
  {{{ P2 }}} e2 {{{ v, RET v; Q2 v }}} -∗
  {{{ P1 ∗ P2 }}} (e1 ||| e2)%V {{{ v1 v2, RET (v1, v2); Q1 v1 ∗ Q2 v2 }}}.
Proof.
  iIntros "#H1 #H2 %Φ !> [HP1 HP2] HΦ".
  rewrite /par.
  wp_pures.
  wp_apply (spawn_spec P1 Q1 with "[] HP1").
  {
    iIntros "%Φ1 !> HP1  HΦ1".
    wp_pures.
    iApply ("H1" with "HP1 HΦ1").
  }
  iIntros "%h Hh".
  wp_pures.
  wp_apply ("H2" with "HP2").
  iIntros "%v2 HQ2".
  wp_pures.
  wp_apply (join_spec with "Hh").
  iIntros "%v1 HQ1".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

End threads.
