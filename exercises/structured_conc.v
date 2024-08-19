From iris.algebra Require Import excl.
From iris.base_logic.lib Require Export invariants token.
From iris.heap_lang Require Import lang proofmode notation.

(* ################################################################# *)
(** * Structured Concurrency *)

(* ================================================================= *)
(** ** Introduction *)

(**
  As the reader might recall from the HeapLang chapter, the only
  construct for concurrency supported natively by HeapLang is [Fork].
  The [Fork] construction is an example of _unstructured_ concurrency.
  When we use [Fork] to create a new thread, there are no control flow
  constructs to reason about the termination of the forked thread – it
  just runs until it is done and, upon completion, disappears. 

  When such control flow constructs are available, we call it
  _structured_ concurrency. It turns out that we can implement
  structured concurrency from unstructured concurrency, and we have
  already seen two such examples: [spawn] and [par]. Both of these
  constructs are part of HeapLang's library, but under the hood, they
  are simply HeapLang programs defined in terms of the [Fork] primitive.

  The library definitions additionally give and prove specifications for
  the constructs, which we have used in previous chapters. In this
  chapter, we will define the constructs from scratch, and write our own
  specifications for them.
*)

(* ================================================================= *)
(** ** The Fork Construct *)

(**
  Let us begin by revisiting the [Fork] construct. The operation takes
  an expression [e] as an argument and spawns a new thread that executes
  [e] concurrently. The operation itself returns the unit value on the
  spawning thread.

  [Fork] does not have dedicated tactical support. Instead, we simply
  apply the lemma [wp_fork] – the specification for [Fork]. The lemma is
  as follows.
*)

About wp_fork.

(**
  For convenience, we included it here as well in `simplified' form.

    [WP e {{_, True}} -∗ ▷ Φ #() -∗ WP Fork e {{v, Φ v}}]

  That is, to show a weakest precondition of [Fork e] we have to show
  the weakest precondition of [e] for a trivial postcondition. The key
  point is that we only require the forked-off thread to be safe – we do
  not care about its return value, hence the trivial postcondition.
*)

(* ================================================================= *)
(** ** The Spawn Construct *)

(**
  The first structured concurrency construct we study is [spawn]. This
  consists of two functions: [spawn], which spawns a thread and returns
  a `handle', and [join], which uses the handle to wait for a thread to
  finish.

  We define the functions as follows.
*)

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

(**
  The idea with [spawn] is to create a `shared channel' which can be
  used to signal when the forked-off thread has terminated. In this
  case, the shared channel is simply a location containing an optional
  value. When forking off the function ["f"], we wrap it around a store
  operation, which writes the result of ["f"] into the location. The
  location is then returned to the spawning thread, which can use this
  so-called `handle' in the [join] function. The [join] function
  continuously checks if the location has been updated to contain a
  value. If this happens, the spawning thread knows that the forked-off
  thread has finished, so it can extract the return value from the
  location.

  Considering this behaviour, we give [spawn] the specification:

  [[
    {{{ P }}} f #() {{{ v, RET v; Ψ v }}} -∗
    {{{ P }}} spawn f {{{ h, RET h; join_handle h Ψ }}}
  ]]

  This states that, to get a specification for [spawn f], we first must
  prove a specification for [f] which captures which resources [f]
  needs, [P], and what the value [f] terminates at satisfies, [Ψ]. If we
  can prove such a specification for [f], then, given [P], we can also
  run [spawn f], which will return a value [h] which satisfies a
  `join-handle' predicate. This predicate is a promise that, if we
  invoke [join] with [h], then the value we get back satisfies [Ψ]. This
  is reflected in the specification for [join]:

  [[
    {{{ join_handle h Ψ }}} join h {{{ v, RET v; Ψ v }}}.
  ]]

  Let us now prove these specifications.
*)

Section spawn.

Context `{!heapGS Σ}.
Let N := nroot .@ "handle".

(**
  Since we are using a shared channel we will use an invariant to allow
  the two (concurrently running) threads to access it. An initial
  attempt at stating this invariant looks as follows.
*)
Definition handle_inv1 (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ v : val, l ↦ v ∗ (⌜v = NONEV⌝ ∨ ∃ w : val, ⌜v = SOMEV w⌝ ∗ Ψ w).

(**
  The stated invariant governs the shared channel (some location [l])
  and states that either no value has been sent yet, or some value has
  been sent that satisfies the predicate [Ψ].

  We can then use the invariant to define the [join_handle] predicate.
*)
Definition join_handle1 (h : val) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ l : loc, ⌜h = #l⌝ ∗ inv N (handle_inv1 l Ψ).

(** Let us now attempt to prove the specification for [join]. *)
Lemma join_spec (h : val) (Ψ : val → iProp Σ) :
  {{{ join_handle1 h Ψ }}} join h {{{ v, RET v; Ψ v }}}.
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

(* 
  TODO: rewrite, and mention that we use token from library which is
  similar to the tokens we defined in resource algebra chapter.
*)

(**
  We need a way to keep track of whether [Ψ w] has been `taken out' of
  the invariant or not. However, we do not have any program state to
  link it to. Instead, we will use _ghost state_ to track this
  information. Iris supports different kinds of ghost state, but we will
  only need one property, namely that our ghost state is _exclusive_.

  We will use the camera [excl A]. This is the exclusive camera. It has
  the valid states [Excl a]. Importantly, this state is exclusive,
  meaning [Excl a ⋅ Excl b] is not valid. As we don't care about the
  value of the state, we will simply let [A:=()].
*)
Context `{!tokenG Σ}.

Definition handle_inv (γ : gname) (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ v, l ↦ v ∗ (⌜v = NONEV⌝ ∨ (∃ w, ⌜v = SOMEV w⌝ ∗ Ψ w) ∨ token γ).

Definition join_handle (h : val) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ γ (l : loc), ⌜h = #l⌝ ∗ token γ ∗ inv N (handle_inv γ l Ψ).

Lemma token_lock (γ : gname) (P : iProp Σ) :
  token γ -∗
  (token γ ∨ P) -∗
  token γ ∗ P.
Proof.
  iIntros "H1 [H2 | HP]".
  - iExFalso. iApply (token_exclusive with "H1 H2").
  - iFrame.
Qed.

Lemma spawn_spec (P : iProp Σ) (Ψ : val → iProp Σ) (f : val) :
  {{{ P }}} f #() {{{ v, RET v; Ψ v }}} -∗
  {{{ P }}} spawn f {{{ h, RET h; join_handle h Ψ }}}.
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
    iLeft.
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
  iInv "I" as "(%_ & Hl & [>-> | [(%w & >-> & HΨ) | >Hγ']])".
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
  - wp_load.
    iModIntro.
    iSplitL "Hγ Hl".
    {
      iNext.
      iExists (SOMEV w).
      iFrame.
    }
    wp_pures.
    by iApply "HΦ".
  - iPoseProof (token_exclusive with "Hγ Hγ'") as "[]".
Qed.

End spawn.

(* TODO: show example client of spawn. *)

(* ================================================================= *)
(** ** The Par Construct *)

(* TODO: rewrite *)

(**
  With [spawn] and [join] defined and their specifications proved, we
  can move on to study a classical parallel composition operator: [par].
  Its definition is quite straightforward.
*)
Definition par : val :=
  λ: "f1" "f2",
  let: "h" := spawn "f1" in
  let: "v2" := "f2" #() in
  let: "v1" := join "h" in
  ("v1", "v2").

(** We introduce familiar notation for [par] that hides the thunks. *)
Notation "e1 ||| e2" := (par (λ: <>, e1)%E (λ: <>, e2)%E) : expr_scope.
Notation "e1 ||| e2" := (par (λ: <>, e1)%V (λ: <>, e2)%V) : val_scope.

(**
  Our desired specification for [par] is going to look as follows:

  [[
    {{{ P1 }}} e1 {{{ v, RET v; Ψ1 v }}} -∗
    {{{ P2 }}} e2 {{{ v, RET v; Ψ2 v }}} -∗
    {{{ P1 ∗ P2 }}} e1 ||| e2 {{{ v1 v2, RET (v1, v2); Ψ1 v1 ∗ Ψ2 v2 }}}
  ]]

  The rule states that we can run [e1] and [e2] in parallel if they have
  _disjoint_ footprints and that we can verify the two components
  separately. The rule is this reason sometimes also referred to as the
  _disjoint concurrency rule_.
  TODO: Mention that it is slightly different from the par spec we have seen earlier [wp_par], but that this is mostly a notational difference.
*)

Section par.
(* TODO: mention that we must include the resource algebra that spawn relies on. *)
Context `{!heapGS Σ, !tokenG Σ}.

(* TODO: some text explaining the proof might be nice. *)
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

End par.

(**
  Let us try to use the par specification to prove a specification for a
  simple client. The client performs two `fetch and add' operations on
  the same location in parallel. The expression [FAA "l" #i] atomically
  fetches the value at location [l], adds [i] to it, and stores the
  result back in [l].

  Our specification will state that the resulting value is even.
*)

Definition parallel_add : expr :=
  let: "r" := ref #0 in
  (FAA "r" #2)
  |||
  (FAA "r" #6)
  ;;
  !"r".

Section parallel_add.
(**
  The par operator needs more resources than are available in
  [heapGS]. So to use it we also need to add [spawnG Σ].
*)
Context `{!heapGS Σ, !tokenG Σ}.

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
    use [λ _, True] as the post conditions. Similarly, we only need the
    invariant to prove the threads, and since this is in the persistent
    context, we let the preconditions be [True].
  *)
  wp_apply (par_spec (True%I) (True%I) _ _ (λ _, True%I) (λ _, True%I)).
  - iIntros (Φ') "!> _ HΦ'".
    iInv "I" as "(%n & Hr & >%Hn)".
    wp_faa.
    iModIntro.
    iSplitL "Hr".
    {
      iModIntro.
      iExists (n + 2)%Z.
      iFrame.
      iPureIntro.
      by apply Zeven_plus_Zeven.
    }
    by iApply "HΦ'".
  (* exercise *)
Admitted.

End parallel_add.
