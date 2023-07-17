From iris.algebra Require Import excl.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.

(**
  Heaplang has concurency in the form of a fork operation. This
  operation takes an expresion and runs it in a seperate thread.
  Meanwhile, the initial thread continues execution with a unit value.
  Fork does not have a reduction tactic. Instead we need to use it's
  specification explicitly via `wp_fork`. This lemma is more general
  than we need for our current use cases, but it esentially states
  that:
  [WP e {{_, True}} -∗ ▷ Φ #() -∗ WP Fork e {{v, Φ v}}]

  We can use fork to implement other common concurency operators such
  as [spawn] and [join].
*)
Definition spawn: val :=
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

(**
  We can then use the function to define the par operator.
*)
Definition par: val :=
  λ: "f1" "f2",
  let: "h" := spawn "f1" in
  let: "v2" := "f2" #() in
  let: "v1" := join "h" in
  ("v1", "v2").

(** The notation for the par operator then hides the thunks *)
Notation "e1 ||| e2" := (par (λ: <>, e1)%E (λ: <>, e2)%E) : expr_scope.
(**
  Lambda expresions actually canonicalize as lambda values. Thus we
  need to refer to this canonical form when proving our specifications
*)
Notation "e1 ||| e2" := (par (λ: <>, e1)%V (λ: <>, e2)%V) : val_scope.


(**
  Our desired specification for [par] is going to be:
  {{{ P1 }}} e1 {{{ v, RET v; Ψ1 v }}} -∗
  {{{ P2 }}} e2 {{{ v, RET v; Ψ2 v }}} -∗
  {{{ P1 ∗ P2 }}} e1 ||| e2 {{{ v1 v2, RET (v1, v2); Ψ1 v1 ∗ Ψ2 v2 }}}


  To achieve this we need specifications for [spawn] and [join]. For
  this we need a predicate [join_handle] for the result of the join.
  {{{ P }}} f #() {{{ v, RET v; Ψ v }}} -∗
  {{{ P }}} spawn f {{{ v, RET v; join_handle v Ψ }}}

  {{{ join_handle v Ψ }}} join v {{{ v, RET v; Ψ v }}}
*)


Section threads.
Context `{!heapGS Σ}.
Let N := nroot .@ "handle".


Definition handle_inv1 (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ v, l ↦ v ∗ (⌜v = NONEV⌝ ∨ ∃ w, ⌜v = SOMEV w⌝ ∗ Ψ w).

Definition join_handle1 (v : val) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ inv N (handle_inv1 l Ψ).


Lemma join_spec (v : val) (Ψ : val → iProp Σ) :
  {{{ join_handle1 v Ψ }}} join v {{{ v, RET v; Ψ v }}}.
Proof.
  iIntros "%Φ (%l & -> & #I) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (! _)%E.
  iInv "I" as "(%v & Hl & [>->|(%w & >-> & HΨ)])".
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
    (**
      Now we need HΨ to reestablish the invariant. However we also
      need it for the post-condition. As such, we are stuck.
    *)
Abort.

(**
  To fix this we need a way to keep track of whether Ψ is in the
  invariant. However we don't have any program state to link it to.
  Therefor we will use a different kind of state, called ghost state.
  Iris supports many kinds of ghost state, but we will only need one
  property, namely that our ghost state be exclusive.

  We will use the camera [excl A]. This is the exclusive camera. It
  has the valid states [Excl a]. Importantly this state is exclusive,
  meaning [Excl a ⋅ Excl b] isn't valid. As we don't care about the
  value of the state, we will let [A:=()].
*)
Context `{!inG Σ (exclR unitO)}.

Definition handle_inv (γ : gname) (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ v, l ↦ v ∗ (⌜v = NONEV⌝ ∨ ∃ w, ⌜v = SOMEV w⌝ ∗ (own γ (Excl ()) ∨ Ψ w)).

Definition join_handle (v : val) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ γ (l : loc), ⌜v = #l⌝ ∗ own γ (Excl ()) ∗ inv N (handle_inv γ l Ψ).

Lemma token_alloc : ⊢ |==> ∃ γ, own γ (Excl ()).
Proof. by iApply own_alloc. Qed.

Lemma token_excl γ : own γ (Excl ()) -∗ own γ (Excl ()) -∗ False.
Proof.
  iIntros "H1 H2".
  iPoseProof (own_valid_2 with "H1 H2") as "%H".
  cbv in H.
  done.
Qed.

Lemma token_lock (γ : gname) (P : iProp Σ) : own γ (Excl ()) -∗ (own γ (Excl ()) ∨ P) -∗ own γ (Excl ()) ∗ P.
Proof.
  iIntros "H1 [H2|HP]".
  - iPoseProof (token_excl with "H1 H2") as "[]".
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
  {{{join_handle h Ψ}}} join h {{{v, RET v; Ψ v}}}.
Proof.
  iIntros "%Φ (%γ & %l & -> & Hγ & #I) HΦ".
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
  {{{P1}}} e1 {{{v, RET v; Q1 v}}} -∗
  {{{P2}}} e2 {{{v, RET v; Q2 v}}} -∗
  {{{P1 ∗ P2}}} (e1 ||| e2)%V {{{v1 v2, RET (v1, v2); Q1 v1 ∗ Q2 v2}}}.
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
