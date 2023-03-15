From iris.algebra Require Import agree auth frac gmap numbers.
From iris.bi Require Import fractional.
From iris.base_logic Require Import iprop own.
From iris.proofmode Require Import proofmode.

(*
  Resources are incoded using `cmra` pronounced camera.
  Each cmra represents some kind of resource.
  `iProp` cannot talk about all resources do to size isues.
  Instead we parameterize `iProp` over a list of cmras `Σ`.
  However if we only proved our lemmas for a specific list of cmras, we would run into problems as soon as we need a new kind.
  To fix this, we instead make our proofs generic over `Σ` and require that the resources we need are present somewere inside `Σ`.
  This is done using the typeclass `inG Σ A`, stating that the cmra `A` is present in `Σ`.

  Instead of using the resources directly, we usually define new predicates and connectives around them, and prove the nessesary theorems on these.
  Usually, when you need a resource, you have a set of connectives and properties already in mind. The cmra is then chosen to satisfy these requirements rather than the other way around.

  It is possible to define your own cmras, but that can get rather cumbersome.
  Instead, Iris ships with a long list of predefined cmras and generators of cmras.
  As such, it is usually prosible to build a cmra satisfying your desired properties, just by combining preexisting cmras in clever ways.
*)

(*
  To see cmras in action, lets look at frac.
  This cmra consists of fractions in the interval (0, 1].
  Composition of fractions is defined as addition, and validity is defined as the fraction remaining in the interval.
*)
Section frac.
Context `{!inG Σ frac}.

(* To define ownership of part of a fraction named `γ` we define this connective *)
Definition own_frac (γ : gname) (q : frac) := own γ q.

(* Most of the properties we care about follow from `own`, the generic ownership predicate for owning a resource. *)

(*
  To create a new fraction, we need to modify the state of resources. This is done through the basic update modality.
  After the update we have a new fraction with a new name. We cannot choose this name ahead of time, because it needs to be fresh, so that it does not clash with existing fractions.
  Futher more, it is only possible to own valid resources, so we also have to prove that the newly allocated resource is valid.
  In this case, validity
*)
Lemma own_frac_alloc : ⊢ |==> ∃ γ, own_frac γ 1.
Proof.
  apply own_alloc.
  do 2 red =>/=.
  (* As validity on frac is defined as `q ≤ 1`, this becomes a rather trivial proof. *)
  reflexivity.
Qed.

(*
  As previously stated, all owned resources must be valid.
  As such you'd expect that validity follows from ownership.
*)
Lemma own_frac_valid γ q : own_frac γ q -∗ ⌜q ≤ 1⌝%Qp.
Proof.
  rewrite -(uPred.discrete_valid q).
  apply own_valid.
Qed.

(*
  Lastly `own_frac` does not mean you own the entire of the fraction.
  It only means you own a fragment of the fraction. This means that your fraction can be split into smaller fractions.
*)
Lemma own_frac_split γ q1 q2 : own_frac γ (q1 + q2) ⊣⊢ own_frac γ q1 ∗ own_frac γ q2.
Proof. exact (own_op γ q1 q2). Qed.

(*
  These properties, makes fractions a great way to talk about shared ownership, where `1` would be complete ownership.
  `frac` is in fact so common, that Iris has a typeclass `Fractional` that describe predicates that satisfy the splitting property.
*)

(*
  Show that 1 represents exclusive ownership using `own_frac_valid` and `own_frac_split`.
*)
Lemma own_frac_1_exclusive γ q : own_frac γ 1 -∗ own_frac γ q -∗ False.
Proof.
  (**)
Abort.

End frac.

(*
  To use fractions as ownership, we incorporate them into other cmras.
  One such case is ghost variables. These are build on the camera `frac * agree A` for some type `A`.
  The `agree A` cmra is composed of values in `A`. Composition is defined such that `x ⋅ y` is `x` when `x = y` and invalid otherwise.

  For now let's keep `A` to `nat`.
*)
Section ghost_var.
Context `{!inG Σ (frac * agree nat)%type}.

(* Much like before, we need a name and an element *)
Definition ghost_var (γ : gname) (q : frac) (n : nat) := own γ (q, to_agree n).

(* We need similar properties *)
Lemma ghost_var_alloc (n : nat) : ⊢ |==> ∃ γ, ghost_var γ 1 n.
Proof. by apply own_alloc. Qed.

(*
  Here we use `Fractional` instead of proving composition.
  This allows Iris proofmode to decompose and combine ownership of ghost variables automatically.
*)
Global Instance ghost_var_fractional γ n : Fractional (λ q, ghost_var γ q n).
Proof.
  intros p q.
  rewrite /ghost_var.
  rewrite -own_op -pair_op.
  rewrite agree_idemp.
  reflexivity.
Qed.
Global Instance ghost_var_as_fractional γ q n : AsFractional (ghost_var γ q n) (λ q, ghost_var γ q n) q.
Proof. split; [done|]. apply _. Qed.

(* Validity is described like before, except our definition ensures that the agreement part is already valid *)
Lemma ghost_var_valid γ q n : ghost_var γ q n -∗ ⌜q ≤ 1⌝%Qp.
Proof.
  iIntros "H".
  iPoseProof (own_valid with "H") as "%H".
  iPureIntro.
  by destruct H.
Qed.

(* To capture validity of agreement, we instead describe when the composit of two `ghost_var` are valid. *)
Lemma ghost_var_agree γ q1 n1 q2 n2 : ghost_var γ q1 n1 -∗ ghost_var γ q2 n2 -∗ ⌜n1 = n2⌝.
Proof.
  rewrite /ghost_var.
  iIntros "H1 H2".
  iCombine "H1 H2" as "H".
  iPoseProof (own_valid with "H") as "%H".
  iPureIntro.
  destruct H as [_ H].
  cbn in H.
  by apply to_agree_op_inv in H.
Qed.

(*
  If we ended it here, `ghost_var` wouldn't be very useful.
  What makes them useful is their ability to update.
  Updates of a resource are governed by what are called frame preserving updates `a ~~> b`.
  These are updates that don't invalidate other knowledge that may exist.
  This means that if `a ⋅ c` is valid for some `c` then `b ⋅ c` must also be valid.

  Ghost variables makes use of the fact the `1` has no frames, meaning `(1, n)` can update to anything as long as it remains valid.
*)
Lemma ghost_var_update γ n1 n2 : ghost_var γ 1 n1 -∗ |==> ghost_var γ 1 n2.
Proof.
  apply own_update.
  apply cmra_update_exclusive.
  done.
Qed.

End ghost_var.

(*
  This is esentially the definition used to define ghost variables in iris.
  However instead of using `frac` Iris uses `dfrac`. `dfrac` are `frac` with the extension of a discarded state.
  This allows us to define a slightly extended notion of ownership, where discarded means the resource can never be exclusively owned again.
  This knowledge is infact persistant, making it very nice to work with.

  Predicates over `dfrac` use a shared syntactic convention to specify the discardable fraction.
  Take for instance the mapsto predicate `l ↦ v`. This predicate has 4 variations on the notation.
  - `l ↦{# dq} v` : Explicitly stated discardable fraction of type `dfrac`
  - `l ↦{q} v` : Explicitly stated fraction of type `frac`
  - `l ↦□ v` : The fraction is discarded
  - `l ↦ v` : The fraction is 1

  This allows you to only specify ownership when neccesary.
*)

(*
  Next let's take a look at the authoritative camera `auth A`.
  We'll instantiate is with the camera `nat` of natural numbers with addition.

  The authoritative camera has to parts. The authoritative part `●{# dq} n` and the fragment `◯ n`.
  The authoritative part describes the entirety of the resource with fractional ownership. While the fragments are fragments of this whole.

  The authoritative camera is therefor useful when you need a way to talk about the entirety of the resource.

  For now let's ignore the fractionality of the authoritative part.
*)
Section auth_nat.
Context `{!inG Σ (auth nat)}.

Definition auth_nat_auth (γ : gname) (n : nat) := own γ (● n).
Definition auth_nat_frag (γ : gname) (n : nat) := own γ (◯ n).

(* We only allocate the authoritative part at 0, as the rest follows from it*)
Lemma auth_nat_auth_alloc : ⊢ |==> ∃ γ, auth_nat_auth γ 0.
Proof.
  apply own_alloc.
  apply auth_auth_valid.
  done.
Qed.

(*
  Both predicates are always valid on their own, so instead we will consider validity of combinations.
  Inclusion `⪯` for the natural numbers means less than or equal `≤`, so the authoritative part must be at least as much as the fragment.
*)
Lemma auth_nat_auth_frag_valid (γ : gname) (n1 n2 : nat) : auth_nat_auth γ n1 -∗ auth_nat_frag γ n2 -∗ ⌜n2 ≤ n1⌝.
Proof.
  rewrite /auth_nat_auth /auth_nat_frag.
  iIntros "H1 H2".
  iCombine "H1 H2" as "H".
  iPoseProof (own_valid with "H") as "%H".
  iPureIntro.
  apply auth_both_dfrac_valid_discrete in H.
  destruct H as (_&H&_).
  by apply nat_included.
Qed.

Lemma auth_nat_auth_exclusive (γ : gname) (n1 n2 : nat) : auth_nat_auth γ n1 -∗ auth_nat_auth γ n2 -∗ False.
Proof.
  rewrite /auth_nat_auth.
  iIntros "H1 H2".
  iCombine "H1 H2" as "H".
  iPoseProof (own_valid with "H") as "%H".
  apply auth_auth_op_valid in H.
  done.
Qed.

(* The authoritative part can be incremented by making a fragment containing the increment. *)
Lemma auth_nat_add γ (n m : nat) : auth_nat_auth γ n ==∗ auth_nat_auth γ (m + n) ∗ auth_nat_frag γ m.
Proof.
  rewrite -own_op.
  apply own_update.
  apply auth_update_alloc.
  apply nat_local_update.
  rewrite Nat.add_0_r.
  apply comm, _.
Qed.

(* The authoritative part can be decremented by consumming a fragment containing the difference. *)
Lemma auth_nat_sub γ (n m : nat) : auth_nat_auth γ (m + n) -∗ auth_nat_frag γ m ==∗ auth_nat_auth γ n.
Proof.
  iIntros "H1 H2".
  iCombine "H1 H2" as "H".
  iApply (own_update with "H").
  apply auth_update_dealloc.
  apply nat_local_update.
  rewrite Nat.add_0_r.
  apply comm, _.
Qed.

Lemma auth_nat_alloc_n n : ⊢ |==> ∃ γ, auth_nat_auth γ n.
Proof.
  (**)
Abort.

End auth_nat.

(*
  The iris representation of heaps is build using the cmra `auth (gmap K (dfrac * agree V))`.
  Here a `gmap K A` is a finite partial function (finite map) from `K` to `A`. With pointwise validity and composition.

  The keys in the map represents locations, with the values describing what is at that location.
  If a key is not present in the map, it means it is not allocated.

  We'll use natural numbers for locations and values.
*)
Section heap.
Context `{!inG Σ (auth (gmap nat (dfrac * agree nat)))}.

Definition heap_auth (γ : gname) (heap : gmap nat nat) : iProp Σ :=
  own (inG0:=inG0) γ (● ((λ v, (DfracOwn 1, to_agree v)) <$> heap)). 

Definition mapsto (γ : gname) (dq : dfrac) (l v : nat) :=
  own γ (◯ ({[l:=(dq, to_agree v)]})).



End heap.