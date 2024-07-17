From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang proofmode notation par.

(* ################################################################# *)
(** * Persistently *)

Section persistently.
Context `{!heapGS Σ}.

(* ================================================================= *)
(** ** Introduction *)

(**
  In separation logic, propositions are generally not duplicable. This
  is because resources are generally exclusive. However, resources do
  not _have_ to be exclusive. A great example of this is `read only
  memory'. There is no danger in letting many threads access the same
  location simultaneously if they can only read from it. Hence, it would
  not make sense to require that ownership of those locations be
  exclusive. Motivated by this, we introduce a new modality denoted the
  persistently modality, written [□ P], for propositions [P]. The
  proposition [□ P] describes the same resources as [P], except it does
  not claim that the resources are exclusive – hence [□ P] can be
  duplicated. Persistent propositions hence act like propositions in an
  intuitionistic logic, which is why they are also sometimes referred to
  as intuitionistic.

  A propositions is persistent when [P ⊢ □ P]. That is, assuming [P], we
  need to show that [P] does not rely on any exclusive resources.
  Persistency is preserved by most connectives, so proving that a
  proposition is persistent is usually a matter of showing that the
  mentioned resources are shareable. Which resources are shareable
  depends on the specific notions of resources being used. For the
  resource of heaps, a location can be marked as read-only, making it
  shareable. The associated points-to predicate hence becomes
  persistent. We will see an example of this later.

  Propositions that do not rely on resources altogether are trivially
  persistent. We have already given those types of propositions a name:
  _pure_. This is also why we do not have to split the non-spatial
  context when using [iSplitL]/[iSplitR]; all pure propositions are
  persistent, hence duplicable.

  Of course, not all persistent propositions are pure (e.g. persistent
  points-to predicates). Thus, the Iris Proof Mode provides a third
  context just for persistent propositions, called the persistent
  context. Pure propositions can go in all three contexts. Persistent
  propositions can go in the spatial context or the persistent context.
  And all other propositions are limited to the spatial context only.
  Iris uses the typeclass [Persistent] to identify persistent
  propositions.
*)

Lemma pers_context (P Q : iProp Σ) `{!Persistent P} : P -∗ Q -∗ P ∗ Q.
Proof.
  (**
    The introduction pattern "#_" allows us to place a persistent
    hypothesis into the persistent context.
  *)
  iIntros "#HP HQ".
  iSplitR "HQ".
  (**
    Notice that after splitting, both the non-spatial and persistent
    contexts are duplicated. In particular, [HP] is available in both
    subgoals.
  *)
  - iApply "HP".
  - iApply "HQ".
Qed.

(**
  Note that all propositions in the spatial context are treated as
  non-persistent, regardless of whether they are persistent.
*)

Lemma not_in_pers_context (P Q : iProp Σ) `{!Persistent P} : P -∗ Q -∗ P ∗ Q.
Proof.
  (** We introduce [HP] to the spatial context. *)
  iIntros "HP HQ".
  iSplitR "HQ".
  (** [HP] is no longer duplicated. *)
  - iApply "HP".
  - iApply "HQ".
Qed.

(** Exercise: prove that persistent propositions are duplicable. *)

Lemma pers_dup (P : iProp Σ) `{!Persistent P} : P ⊢ P ∗ P.
Proof.
  (* exercise *)
Admitted.

(**
  Persistent propositions satisfy a lot of nice properties, simply by
  being duplicable [P ⊢ P ∗ P]. For example, [P ∧ Q] and [P ∗ Q]
  coincide, when either [P] or [Q] is persistent. Likewise, [P → Q] and
  [P -∗ Q] coincide, when [P] is persistent.
*)

Check bi.persistent_and_sep.
Check bi.impl_wand.

(**
  The Iris Proof Mode knows these facts and allows [iSplit] to introduce
  [∗] when one of its arguments is persistent.
*)


(* ================================================================= *)
(** ** Proving Persistency *)

(**
  To prove a proposition [□ P], we have to prove [P] without assuming
  any exclusive resources. In other words, we have to throw away the
  spatial context when proving [P].
*)

Lemma pers_intro (P Q : iProp Σ) `{!Persistent P} : P ∗ Q ⊢ □ P.
Proof.
  iIntros "[#HP HQ]".
  (**
    The [iModIntro] tactic introduces a modality in the goal. In this
    case, since the modality is a [□], it throws away the spatial
    context.
  *)
  iModIntro.
  iApply "HP".
Qed.

(**
  Since the only difference between [□ P] and [P] is that the former
  does not claim the resources are exclusive, it follows that the
  persistently modality is idempotent.
*)

Lemma pers_idemp (P : iProp Σ) : □ □ P ⊣⊢ □ P.
Proof.
  iSplit.
  - iIntros "HP".
    (**
      Iris already knows that [□] is idempotent, so it automatically
      removes all persistently modalities from a proposition when adding
      it to the persistent context. One may think of all propositions in
      the persistent context as having an implicit [□] in front.
    *)
    iDestruct "HP" as "#HP".
    done.
  - iIntros "#HP".
    (** Similarly, we do not have to introduce [□] before proving it. *)
    done.
Qed.

(**
  Only propositions that are instances of the [Persistent] typeclass can
  be added to the persistent context. As with the typeclasses for pure,
  the [Persistent] typeclass can automatically identify most persistent
  propositions.
*)

Lemma pers_sep (P Q : iProp Σ) : □ P ∗ □ Q ⊣⊢ □ (P ∗ Q).
Proof.
  iSplit.
  - (**
      The [Persistent] typeclass detects that [□ P ∗ □ Q] is persistent.
    *)
    iIntros "#HPQ".
    iDestruct "HPQ" as "[#HP #HQ]".
    iModIntro.
    (**
      By default, [iFrame] will not frame propositions from the
      persistent context. To make it do so, we have to give it the
      argument "#".
    *)
    iFrame "#".
  - (* exercise *)
Admitted.

(** Persistency is preserved by quantifications. *)

Lemma pers_all `{A} (P : A → iProp Σ) : (∀x, □ P x) ⊢ ∀y, P y ∗ P y.
Proof.
  iIntros "#Hp %y".
  iSplitL; iApply ("Hp" $! y).
Qed.

(**
  For simple predicates, such as [myPredicate] below, the [Persistent]
  typeclass can automatically infer that it is persistent. However, we
  can still manually make propositions instances of [Persistent].
*)

Definition myPredicate (x : val) : iProp Σ := ⌜x = #5⌝.

Local Instance myPredicate_persistent x : Persistent (myPredicate x).
Proof.
  (**
    As mentioned in the beginning of the chapter, a proposition [P] is
    persistent when [P ⊢ □ P]. This is almost what [Persistent] requires
    us to prove.
  *)
  rewrite /Persistent.
  (**
    Our actual goal is of the form [P ⊢ <pers> P]. Technically, there is
    a small discrepancy between [□] and [<pers>], but we will ignore
    that here.

    As pure propositions are persistent, we quite easily prove this.
  *)
  rewrite /myPredicate.
  iIntros "#H".
  iModIntro.
  iApply "H".
Qed.

(** Iris is quite smart, so we do not have to spell out the proof. *)
Local Instance myPredicate_persistent' x : Persistent (myPredicate x).
Proof. apply _. Qed.

(**
  For more complicated predicates, such as ones defined as a fixpoint,
  [Persistent] cannot automatically infer its persistence. The following
  predicate asserts that all values in a given list is equal to [5].
*)

Fixpoint myPredFix (xs : list val) : iProp Σ :=
  match xs with
  | [] => True
  | x :: xs' => ⌜x = #5⌝ ∗ myPredFix xs'
  end.

(**
  This predicate only consists of pure propositions, so it should of
  course be persistent, but when we try to add it to the persistent
  context, Iris complains that it is not `intuitionistic' (i.e.
  persistent).
*)
Lemma first_is_5 (x : val) (xs : list val) :
  myPredFix (x :: xs) -∗ ⌜x = #5⌝ ∗ myPredFix (x :: xs).
Proof.
  Fail iIntros "#H".
Abort.

(**
  For such predicates, we have to prove that it is persistent manually,
  as we did for [myPredicate] above.
*)

Local Instance myPredFix_persistent xs : Persistent (myPredFix xs).
Proof.
  (** We prove it by induction in [xs]. *)
  induction xs as [| x xs' IH ].
  - (** [True] is persistent *)
    apply _.
  - (**
      By IH, [myPredFix xs'] is persistent. As ⌜x = #5⌝ is also persistent,
      it follows that [myPredFix (x :: xs')] is persistent.
    *)
    apply _.
Qed.

(** Now, Iris recognises [myPredFix] as persistent. *)

Lemma first_is_5 (x : val) (xs : list val) :
  myPredFix (x :: xs) -∗ ⌜x = #5⌝ ∗ myPredFix (x :: xs).
Proof.
  iIntros "#H".
  (**
    [iPoseProof] is similar to [iDestruct], but it does not throw away
    the hypothesis being destructed, if it is persistent.
  *)
  iPoseProof "H" as "[Hx _]".
  iFrame "H Hx".
Qed.

(* ================================================================= *)
(** ** Examples of Persistent Propositions *)

(**
  Thus far, the only basic persistent propositions we have seen are pure
  propositions, such as equalities. In this section we introduce two
  additional examples of persistent propositions: Hoare triples and
  persistent points-to predicates.
*)

(* ----------------------------------------------------------------- *)
(** *** Hoare Triples *)

(**
  All Hoare triples are persistent. This probably does not come as a
  surprise, if the reader recalls how we defined Hoare triples in the
  [specifications] chapter. As a reminder, here is the definition again.
      [□( ∀ Φ, P -∗ ▷ (∀ r0 .. rn, Q -∗ Φ v) -∗ WP e {{v, Φ v }})]
  The outermost part of the definition is the persistently modality! As
  such, Hoare triples can be duplicated and reused.

  Intuitively, we should also expect Hoare triples to be persistent. A
  Hoare triple [{{{ P }}} e {{{ Φ }}}] does not actually claim ownership
  of any resources; it merely states that _if_ we own the resources
  described by [P], then we can safely run [e], and we get the resources
  described by [Φ] in case of termination. Of course, if we can get
  ownership of the resources described by [P] multiple times, we should
  be able to run [e] multiple times.

  As an example, consider a function [counter], which is parametrised
  by an increment function.
*)

Example counter (inc : val) : expr :=
  let: "c" := ref #0 in
  inc "c" ;;
  inc "c" ;;
  !"c".

(**
  If [inc] is a function which adds [1] to the contents of a given
  location, we would expect the above program to return [2]. We express
  this by describing the specification for [inc] in the precondition of
  the specification for [counter].
*)

Lemma counter_spec (inc : val) :
  {{{
    ∀ (l : loc) (z : Z),
      {{{ l ↦ #z }}} inc #l {{{ v, RET v; l ↦ #(z + 1) }}}
  }}}
    counter inc
  {{{ v, RET v; ⌜v = #2⌝ }}}.
Proof.
  (* exercise *)
Admitted.

(* ----------------------------------------------------------------- *)
(** *** Persistent Points-to *)

Context `{spawnG Σ}.

(**
  The resource of heaps is more sophisticated than what we have been
  letting on. The general shape of a points-to predicate is actually
  [l ↦ dq v], where [dq] is a `discarded fraction'. We return to the
  `discarded' part momentarily, but for now, we assume that [dq] is a
  fraction in the interval (0; 1]. The predicate [l ↦ v] is a special
  case, where the fraction [dq] is [1]. The basic idea is that points-to
  predicates can be split up and recombined, allowing ownership of
  points-to predicates to be shared.
*)

Lemma pt_split l v : l ↦ v ⊣⊢ (l ↦{# 1/2 } v) ∗ (l ↦{# 1/2 } v).
Proof.
  iSplit.
  - iIntros "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    iFrame.
  - iIntros "[Hl1 Hl2]".
    iCombine "Hl1" "Hl2" as "Hl".
    iFrame.
Qed.

(**
  Crucially, a store operation can only take place if the _entire_
  fraction is owned, i.e. [dq = 1]. However, load operations can occur
  for any fraction.
*)

Lemma only_read (l : loc) (v : val) :
  {{{ l ↦ v }}} #l <- #2 ;; !#l ;; #l <- #3 {{{ w, RET w; l ↦ #3 }}}.
Proof.
  iIntros (Φ) "Hl HΦ".
  wp_store.
  (** Throw away half of the points-to predicate. *)
  iDestruct "Hl" as "[Hl1 _]".
  (** We can still load. *)
  wp_load.
  wp_seq.
  (** But we can no longer update the pointer. *)
  Fail wp_store.
Abort.

(**
  Fractional points-to predicates are especially useful in scenarios
  where a location is read by multiple threads in parallel, but later
  only used by a single thread.
*)

Example par_read_write (l : loc) : expr :=
  let: "r" := (!#l ||| !#l) in
  #l <- #5.

Lemma par_read_write_spec (l : loc) (v : val) :
  {{{ l ↦ v }}}
    par_read_write l
  {{{ RET #(); l ↦ #5 }}}.
Proof.
  iIntros (Φ) "[Hl1 Hl2] HΦ".
  rewrite /par_read_write.
  (**
    The idea is to give each thread half of the points-to predicate, and
    assert that both will return their halves afterwards.
  *)
  set t_post := (λ w : val, (⌜w = v⌝ ∗ l ↦{#1 / 2} v)%I).
  wp_pures.
  wp_apply (wp_par t_post t_post with "[Hl1] [Hl2]").
  (**
    Each thread has a fraction of the points-to predicate, so both can
    perform the load.
  *)
  1, 2: wp_load; by iFrame.
  (** The threads return their fractions. *)
  iIntros (v1 v2) "[[-> Hl1] [-> Hl2]]".
  iNext.
  wp_let.
  (** We combine them, allowing us to perform the store. *)
  iCombine "Hl1 Hl2" as "Hl".
  wp_store.
  by iApply "HΦ".
Qed.

(**
  Let us now turn to the `discarded' part. If one owns a fraction of a
  points-to predicate, one can decide to _discard_ the fraction. This
  means that it is no longer possible to recombine points-to predicates
  to get the full fraction. As such, the value in the points-to
  predicate can never be changed again – the location has become
  read-only. We write [l ↦□ v] for a points-to predicate whose fraction
  has been discarded. As the [□] suggests, this predicate is persistent.
  Persistent points-to predicates are great if your program has a
  read-only location, as it becomes trivial to give all threads access
  to the associated points-to predicate, and it ensures that no thread
  can sneakily update the location.

  The [pointsto_persist] lemma asserts that we can update any points-to
  predicate [l ↦{dq} v] into a persistent one [l ↦□ v].
*)

Check pointsto_persist.

(**
  There are some caveats as to when we can discard fractions; the
  proposition [P ==∗ Q] is equivalent to [P -∗ (|==> Q)], where [|==>]
  is the update modality, the details of which we defer to later. For
  now, we remark that the [iMod] tactic can remove the update modality
  in many cases. For instance, if the goal is a weakest precondition.
*)

Lemma pt_persist (l : loc) (v : val) :
  l ↦ v -∗ WP !#l {{ w , ⌜w = v⌝ ∗ l ↦□ v }}.
Proof.
  iIntros "Hl".
  (** Make the points-to predicate persistent. *)
  iMod (pointsto_persist with "Hl") as "#Hl".
  wp_load.
  by iFrame "#".
Qed.

(**
  Exercise: finish the proof of the [par_read_spec] specification.
*)

Example par_read : expr :=
  let: "l" := ref #7 in
  let: "r" := ( (!"l" + #14) ||| (!"l" * #3) ) in
  Fst "r" + Snd "r".

Lemma par_read_spec :
  {{{ True }}} par_read {{{ v, RET v; ⌜v = #42⌝ }}}.
Proof.
  iIntros (Φ _) "HΦ".
  rewrite /par_read.
  (** Both threads have the same postcondition, [t_post]. *)
  set t_post := (λ v, (⌜v = #21⌝)%I : iProp Σ).
  (* exercise *)
Admitted.

End persistently.
