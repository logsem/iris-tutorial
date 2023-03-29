From iris.algebra Require Import dfrac.
From iris.bi Require Import fractional.
From iris.base_logic Require Import iprop own.
From iris.proofmode Require Import proofmode.

(*
  Let us define a new ghost theory. This theory will consist of 2
  connectives:
  - `key γ dq` representing fractional ownership of a key named γ
  - `gLock γ P` representing a proposition locked behind a key named γ
  
  The key is going to satisfy the standard properties of fractional
  ownership along with allocation. The lock can be constructed via
  ownership of `P` as `P -∗ gLock γ P`. To unlock it we simply need
  partial ownership of the key `key γ dq -∗ gLock γ P -∗ key γ dq ∗ P`.
  Importantly we get the key fragment back, meaning the key isn't lost.

  Finally we will allow the construction of a lock by locking the
  entire key inside it `key γ (DfracOwn 1) -∗ gLock γ P`. This is
  sound as the lock cannot be opened.
*)

(*
  First we define a class containing the resources we need for our
  theory. In this case we need a dfrac to model our key.
  We will consider the specific resources an implementation detail, so
  we will only register key_inG as an instance localy.
*)
Class keyG Σ := KeyG {
  key_inG : inG Σ dfrac;
}.
Local Existing Instance key_inG.

(*
  Next we define a list of gfunctors containing the necesary
  resources. This allows the user to specify a Σ for their proofs.
*)
Definition keyΣ : gFunctors :=
  #[ GFunctor dfracR ].

(*
  We prove that any Σ containing keyΣ satisfies our keyΣ so that the
  user can simply include keyΣ in their final Σ.
*)
Global Instance subG_keyΣ Σ :
  subG keyΣ Σ → keyG Σ.
Proof. solve_inG. Qed.

(*
  To keep our connective truely opaque we will use the seal type along
  with local definitions. This makes the definitions opaque to
  everything outside this module.

  The definition part of these connectives postfixed by _def.
  The rest of the definitions are specified by the sealing pattern.
*)
Section definitions.
Context `{!keyG Σ}.

(* The key is implemented as ownership of dq. *)
Local Definition key_def (γ : gname) (dq : dfrac) : iProp Σ := own γ dq.
Local Definition key_aux : seal (@key_def).
Proof. by eexists. Qed.
Definition key := key_aux.(unseal).
Local Definition key_unseal : @key = @key_def := key_aux.(seal_eq).

(*
  As we'll see it's enough to define our lock as a disjunction of its
  constructors.
*)
Local Definition gLock_def (γ : gname) (P : iProp Σ) : iProp Σ := P ∨ own γ (DfracOwn 1).
Local Definition gLock_aux : seal (@gLock_def).
Proof. by eexists. Qed.
Definition gLock := gLock_aux.(unseal).
Local Definition gLock_unseal : @gLock = @gLock_def := gLock_aux.(seal_eq).

End definitions.

(* We'll define a tactic to quickly unseal all our definitions *)
Local Ltac unseal := rewrite
  ?key_unseal /key_def
  ?gLock_unseal /gLock_def.

Section lemmas.
Context `{!keyG Σ}.

(*
  It is usually a good idea to export timelessness of connectives when
  posible.
*)
Global Instance key_timeless γ dq : Timeless (key γ dq).
Proof. unseal. apply _. Qed.
Global Instance gLock_timeless γ P : Timeless P → Timeless (gLock γ P).
Proof. unseal. apply _. Qed.

(*
  gLock has a time dependent parameter P, so we should export that
  gLock preserves time
*)
Global Instance gLock_ne γ : NonExpansive (gLock γ).
Proof. unseal. solve_proper. Qed.
Global Instance gLock_proper γ : Proper ((≡) ==> (≡)) (gLock γ).
Proof. apply ne_proper, _. Qed.

(* Allocation of keys follows directly from `own_alloc` *)
Lemma key_alloc : ⊢ |==> ∃ γ, key γ (DfracOwn 1).
Proof. unseal. by apply own_alloc. Qed.

(*
  Our key should satisfy all the rules for fractinal ownership. So
  let's prove them.
*)

(* The owned fraction should be valid *)
Lemma key_valid γ dq : key γ dq -∗ ⌜✓ dq⌝.
Proof.
  unseal.
  iIntros "H".
  iPoseProof (own_valid with "H") as "%H".
  done.
Qed.
(* Composition of keys should be composition of fractions *)
Lemma key_op γ dq1 dq2 : key γ (dq1 ⋅ dq2) ⊣⊢ key γ dq1 ∗ key γ dq2.
Proof. unseal. apply own_op. Qed.
(* The discarded key should be persistent *)
Global Instance key_persistent γ : Persistent (key γ DfracDiscarded).
Proof. unseal. apply _. Qed.
(* Finaly, it should be posible to discard a key through an update. *)
Lemma key_persist γ dq : key γ dq ==∗ key γ DfracDiscarded.
Proof.
  unseal.
  apply own_update.
  apply dfrac_discard_update.
Qed.

(*
  These lemmas are the nessesary proporties for dfractional ownership.
  However to make dfractional ownership more ergonomic, one should add
  certain instances to help the proofmode handle these things
  automaticly.

  Most of the ergonomics is handled by Fractional and AsFractional.
  These allow iCombine to combine DfracOwn and turn the dot into
  addition, as well allowing introduction patterns to split fractions
  by halfing.
*)
Global Instance key_fractional γ : Fractional (λ q, key γ (DfracOwn q)).
Proof.
  intros q1 q2.
  apply (key_op _ (DfracOwn q1) (DfracOwn q2)).
Qed.
Global Instance key_as_fractional γ q : AsFractional (key γ (DfracOwn q)) (λ q, key γ (DfracOwn q)) q.
Proof. split; [done|apply _]. Qed.

(* Let's see the halfing in action. *)
Lemma key_half γ q : key γ (DfracOwn q) ⊣⊢ key γ (DfracOwn (q / 2)) ∗ key γ (DfracOwn (q / 2)).
Proof.
  iSplit.
  - iIntros "[H1 H2]".
    iFrame.
  - iIntros "[H1 H2]".
    iCombine "H1 H2" as "H".
    iFrame.
Qed.

(*
  However dfrac has more values than owned fractions, so we have to
  make a fallback for combining arbitrary dfracs.
*)
Global Instance key_combine_as γ dq1 dq2 :
  CombineSepAs (key γ dq1) (key γ dq2) (key γ (dq1 ⋅ dq2)) | 60.
Proof.
  rewrite /CombineSepAs.
  by rewrite key_op.
Qed.

(*
  Combining keys also gives the knowledge that the fractions are
  composable. This can be encoded using CombineSepGives and retrived
  using `iCombine "_ _" give "_"`.
*)
Global Instance key_combine_gives γ dq1 dq2 :
  CombineSepGives (key γ dq1) (key γ dq2) (⌜✓ (dq1 ⋅ dq2)⌝).
Proof.
  rewrite /CombineSepGives.
  iIntros "[H1 H2]".
  iCombine "H1 H2" as "H".
  iPoseProof (key_valid with "H") as "%H".
  by iModIntro.
Qed.

Lemma key_1_excl_l γ dq : key γ (DfracOwn 1) -∗ key γ dq -∗ False.
Proof.
  iIntros "H1 Hdq".
  iCombine "H1 Hdq" gives "%H".
  by apply dfrac_valid_own_l in H.
Qed.

(*
  Now let us prove that our lock works as intented.
  The lock can be defined in terms of the key. This lemma along with
  the lemmas about about keys will be enough to prove everything we
  want to show about locks.
*)

Local Lemma gLock_unfold γ P : gLock γ P = (P ∨ key γ (DfracOwn 1))%I.
Proof. unseal. done. Qed.

Lemma gLock_intro γ P : P -∗ gLock γ P.
Proof.
  rewrite !gLock_unfold.
  (* FILL IN HERE *) Admitted.

Lemma gLock_key γ P : key γ (DfracOwn 1) -∗ gLock γ P.
Proof.
  rewrite !gLock_unfold.
  (* FILL IN HERE *) Admitted.

Lemma gLock_unlock γ dq P : key γ dq -∗ gLock γ P -∗ key γ dq ∗ P.
Proof.
  rewrite !gLock_unfold.
  (* FILL IN HERE *) Admitted.

(*
  At this point we have a nice working ghost theory, but for advanced usecases of the gLock we need to know how it interacts with the other connectives of our language.
*)

Lemma gLock_mono γ P Q : (P -∗ Q) -∗ gLock γ P -∗ gLock γ Q.
Proof.
  rewrite !gLock_unfold.
  (* FILL IN HERE *) Admitted.

Lemma gLock_and γ P Q : gLock γ (P ∧ Q) ⊣⊢ gLock γ P ∧ gLock γ Q.
Proof.
  rewrite !gLock_unfold.
  (* FILL IN HERE *) Admitted.

Lemma gLock_sep γ P Q : gLock γ P ∗ gLock γ Q -∗ gLock γ (P ∗ Q).
Proof.
  rewrite !gLock_unfold.
  (* FILL IN HERE *) Admitted.

Lemma gLock_impl γ P Q : (P → Q) -∗ gLock γ P → gLock γ Q.
Proof.
  rewrite !gLock_unfold.
  apply bi.impl_intro_l.
  apply bi.impl_elim_l'.
  apply bi.or_elim.
  - apply bi.impl_intro_r.
    trans Q; last apply bi.or_intro_l.
    apply bi.impl_elim_r.
  - apply bi.impl_intro_r.
    trans (key γ (DfracOwn 1)); last apply bi.or_intro_r.
    apply bi.and_elim_l.
Qed.

Lemma gLock_iff γ P Q : (P ↔ Q) -∗ gLock γ P ↔ gLock γ Q.
Proof. apply bi.and_mono; apply gLock_impl. Qed.

End lemmas.
