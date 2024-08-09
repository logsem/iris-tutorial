From iris.algebra Require Import cmra dfrac excl agree dfrac_agree.
From iris.heap_lang Require Import lang proofmode notation.

(*########## CONTENTS PLAN ##########
- INTRODUCTION TO RESOURCE ALGEBRA
- BASIC DEFINITION AND COMPONENTS (FROM ILN)
  + DEFINITION
  + DFRAC RUNNING EXAMPLE
  + FRAME PRESERVING UPDATE
- EXAMPLE RESOURCE ALGEBRA
  + EXCLUSIVE
    * TOKENS (custom definition, not from lib)
  + AGREE
  + PRODUCTS
- GHOST STATE
  + HOW TO ACCESS THEM IN COQ. CONTEXT, Σ
  + ENRICHING IRIS WITH RESOURCES FROM RA
    * 'own'
    * OWN-OP, OWN-VALID
    * EXAMPLE: TOKENS
      ** owning a token
      ** combining two of the same token with own-op
      ** using own-valid to conclude that said element must be valid
      ** knowing from RA that said element must be invalid, hence contradiction
  + UPDATE MODALITY
  + ALLOC, UPDATE
#####################################*)

(* ################################################################# *)
(** * Resource Algebra *)

(* ================================================================= *)
(** ** Introduction *)

(**
  The resource of heaps is a widely used notion of a resource,
  applicable in many circumstances (pretty much every time your program
  interacts with the heap). However, as it turns out, it is not the
  solution to all our problems; some programs require other notions of
  resources to be reasoned about. Instead of adding rules to the logic
  for each of the notions of resources we can think of, we treat
  resources uniformly – we define a fixed set of criteria that a notion
  of resource must satisfy in order to be used in the logic. If the
  notion satisfies those criteria, then it is a `resource algebra'
  (often shorted to `RA'). We can then have a small handful of rules for
  resource algebras in general, and we hence do not need to change the
  logic every time we wish to use a new notion of a resource.

  In this way, resource algebras are oblivious to the existence of Iris
  – they exist as a separate thing. Iris then has a mechanism to embed
  arbitrary resource algebras into the logic and reason about them. This
  mechanism is called `ghost state', and we study it in the last section
  of this chapter.

  A small side note: in Iris, resource algebras are specialisations of
  the more general structure `CMRA'. In particular, resource algebras
  are `discrete' CMRAs, meaning they do not have a notion of time. In
  turn, CMRAs are built on top of `Ordered Families of Equations'. The
  exact details of these concepts are not important for this chapter,
  but we mention them as they appear a few times throughout the chapter.
  CMRAs and OFEs are covered in more detail in later chapters. The focus
  point in this chapter is discrete CMRAs – resource algebra.
*)

(* ================================================================= *)
(** ** Basic Concepts of Resource Algebra *)

(* ----------------------------------------------------------------- *)
(** *** Definition of Resource Algebra *)

(**
  A resource algebra consists of just a few components:
  - A set of elements [A], called the carrier.
  - An equivalence relation [Equiv A] on the elements of [A].
  - An operation [Op A] on the elements of [A].
  - A subset of elements [Valid A], called valid.
  - A partial function [PCore A], called the core.

  These components must satisfy certain properties, but before listing
  those, let us discuss the purpose of each component.

  Firstly, the elements of the carrier intuitively correspond to the
  resources of the resource algebra.

  Secondly, the equivalence relation, written [x ≡ y] for resources
  [x, y ∈ A], tells us which resources are considered equivalent.

  Thirdly, the operation, written [x ⋅ y] for resources [x, y ∈ A],
  shows us how to combine resources.

  Fourthly, we distinguish between valid and invalid resources, writing
  [✓ x] to denote that [x] is valid. Intuitively, validity captures that
  the combination of some resources should not be allowed. In the logic,
  if we combine two valid resources and their combination is invalid,
  then we will be able to derive falsehood.

  Finally, the core, written [pcore x] for a resource [x], is a partial
  function which extracts exactly the _shareable_ part of a resource. We
  handle partiality in Coq by letting the core return an option. We
  write [pcore x = Some y] to mean that the shareable part of resource
  [x] is [y]. Similarly, we write [pcore x = None] to mean that [x] has
  no shareable part. For resources [x] that are entirely shareable, we
  have that [pcore x = Some x].

  Having discussed the purpose of each of the components, we are now
  ready to see which properties we impose on them. In Iris, all resource
  algebras are records in the shape described by [RAMixin]. This
  structure describes the properties the components should satisfy.
*)

Print RAMixin.

(**
  For convenience, we include the definition of [RAMixin] here as well.

  Record RAMixin A `{Equiv A, PCore A, Op A, Valid A} := {
    (* setoids *)
    ra_op_proper (x : A) : Proper ((≡) ==> (≡)) (op x);
    ra_core_proper (x y : A) cx :
      x ≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡ cy;
    ra_validN_proper : Proper ((≡@{A}) ==> impl) valid;
    (* monoid *)
    ra_assoc : Assoc (≡@{A}) (⋅);
    ra_comm : Comm (≡@{A}) (⋅);
    ra_pcore_l (x : A) cx : pcore x = Some cx → cx ⋅ x ≡ x;
    ra_pcore_idemp (x : A) cx : pcore x = Some cx → pcore cx ≡ Some cx;
    ra_pcore_mono (x y : A) cx :
      x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy;
    ra_valid_op_l (x y : A) : ✓ (x ⋅ y) → ✓ x
  }.

  The `setoids' rules state that equivalence of elements is respected by
  the operation, the core, and validity. For instance, [ra_op_proper]
  expresses that, if [y ≡ z], then [x ⋅ y ≡ x ⋅ z], for all [x].

  The fields [ra_assoc] and [ra_comm] assert that the operation [⋅]
  should be associative and commutative. This in effect makes [A] a
  commutative semigroup, which means that we can make all resource
  algebras a preorder through the extension order, written [x ≼ y]. The
  extension order is defined as:
        [x ≼ y = ∃z, y ≡ x ⋅ z]
  Intuitively, the resource [x] is _included_ in [y], if we can express
  [y] in terms of [x] and some [z].

  The fields [ra_pcore_l] and [ra_pcore_idemp] capture the idea that the
  core extracts the shareable part of a resource, and how shareable
  resources behave. [ra_pcore_l] expresses that including the same
  shareable resource multiple times does not change a resource, and
  [ra_pcore_idemp] states that invoking the core on a resource twice
  gives the same resource as invoking the core once.

  [ra_pcore_mono] captures the relationship between the core and the
  extension order.

  Finally, [ra_valid_op_l] asserts that all parts of a valid resource
  are themselves valid.

  All resource algebra satisfy the properties of [RAMixin], and when
  creating a new resource algebra, one must show that it is an [RAMixin]
  record. However, in this chapter, and in most real-world scenarios for
  that matter, we will not create resource algebras from scratch. We can
  utilise existing resource algebras and compose them to create a
  resource algebra that suitably models our desired notion of a
  resource. This allows us to forgo proving the properties of [RAMixin].
  We refer to chapter [Custom Resource Algebra] for an introduction to
  creating resource algebras from scratch.
*)

(* ----------------------------------------------------------------- *)
(** *** An Example Resource Algebra : dfrac *)

(**
  That was a lot of abstract information, so let us get a bit more
  concrete and study the definition of resource algebra through a
  familiar example: discardable fractions (shortened to dfrac). We saw
  discardable fractions when we introduced the persistent points-to
  predicate in the persistently chapter. As it turns out, the resource
  of heaps is actually composed of other resource algebras, one of which
  is dfrac.

  As dfrac is a resource algebra, it is an instance of [RAMixin].
*)

Check dfrac_ra_mixin : RAMixin dfrac.

(**
  As such, it has a carrier, an equivalence relation, an operation, a
  core, and a subset of valid elements, and these satisfy the properties
  specified in the fields of [RAMixin]. We proceed to discuss each of
  these in turn. The full definitions of the components can be found at
  https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/algebra/dfrac.v
*)

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(** **** The Carrier (the [A]) *)

(**
  In dfrac, a resource is either a fraction, knowledge that a fraction
  has been discarded, or a combination of the two.

  When the resource is a fraction [Qp], we write [DfracOwn Qp]. When the
  resource is knowledge that a fraction has been discarded, we write
  [DfracDiscarded]. Finally, when the resource is a fraction _and_ the
  knowledge that a fraction has been discarded, we write [DfracBoth Qp].
  The carrier is denoted [dfrac].
*)

Print dfrac.

(** For instance, [DfracOwn (1/2)] is a resource in dfrac. *)
Check DfracOwn (1/2) : dfrac.

(** And so is knowledge of a fraction having been discarded. *)
Check DfracDiscarded : dfrac.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(** **** Equivalence of Resources (the [Equiv A]) *)

(**
  For dfrac, we simply use Leibniz equality [=] as our equivalence
  relation [≡].
*)

Lemma dfrac_equiv_leibniz (dp dq : dfrac) : (dp = dq) ↔ (dp ≡ dq).
Proof. done. Qed.

(**
  This means that we can use [=] to express equivalence of elements. For
  instance, if two fractions are equivalent, then the corresponding
  resources are equivalent.
*)

Lemma dfrac_frac_equiv : DfracOwn (1/2) = DfracOwn (2/4).
Proof. compute_done. Qed.

(**
  Here, the tactic [compute_done] reduces expressions and solves the
  goal if the expressions are equal.
*)

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(** **** Operation (the [Op A]) *)

(**
  The operation [⋅] is defined by considering all possible combinations of
  the three kinds of dfrac resources.
*)

Print dfrac_op_instance.

(**
  For instance, if the two resources are fractions, then the operation
  adds the fractions together.
*)

Lemma dfrac_op : DfracOwn (1/2) ⋅ DfracOwn (1/4) = DfracOwn (3/4).
Proof. compute_done. Qed.

Lemma dfrac_op2 : DfracOwn (2/3) ⋅ DfracOwn (2/3) = DfracOwn (4/3).
Proof. compute_done. Qed.

(**
  If the resources are both knowledge that a fraction has been
  discarded, then the operation simply returns this knowledge.
*)

Lemma dfrac_op_disc : DfracDiscarded ⋅ DfracDiscarded = DfracDiscarded.
Proof. compute_done. Qed.

(**
  If one of the resources is knowledge of a discarded fraction
  [DfracDiscarded] and the other a fraction [DfracOwn Qp], the operation
  turns the fraction into [DfracBoth Qp].
*)

Lemma dfrac_op_both : DfracOwn (2/3) ⋅ DfracDiscarded = DfracBoth (2/3).
Proof. compute_done. Qed.

(**
  Exercise: reduce the following expressions.
*)

Lemma dfrac_op_both_disc : ∃ x : dfrac,
  DfracBoth (2/3) ⋅ DfracDiscarded = x.
(* SOLUTION *) Proof.
  exists (DfracBoth (2/3)).
  compute_done.
Qed.

Lemma dfrac_op_frac_both : ∃ x : dfrac,
  DfracOwn (1/4) ⋅ DfracBoth (2/4) = x.
(* SOLUTION *) Proof.
  exists (DfracBoth (3/4)).
  compute_done.
Qed.

(**
  As dfrac is a record of type [RAMixin], we know that [⋅] must be
  associative and commutative. We can refer to these properties through
  record projection.
*)

Lemma dfrac_op_assoc (dq1 dq2 dq3 : dfrac) :
  dq1 ⋅ dq2 ⋅ dq3 = dq1 ⋅ (dq2 ⋅ dq3).
Proof.
  rewrite dfrac_ra_mixin.(ra_assoc _).
  done.
Qed.

Lemma dfrac_op_comm (dq1 dq2 : dfrac) :
  dq1 ⋅ dq2 = dq2 ⋅ dq1.
(* SOLUTION *) Proof.
  rewrite dfrac_ra_mixin.(ra_comm _).
  done.
Qed.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(** **** Valid Elements (the [Valid A]) *)

(**
  The idea with using fractions as resources is to be able to split up
  ownership into smaller parts. As such, we let the fraction [1]
  represent total ownership, and fractions less than [1] denote partial
  ownership. In this way, fractions greater than [1] are nonsensical and
  are thus not valid. Likewise for fractions smaller than or equal to
  [0]. In other words, only fractions in the interval (0; 1] are valid.
  Knowledge that a fraction has been discarded is also valid. The
  function [dfrac_valid_instance] defines this formally.
*)

Print dfrac_valid_instance.

(**
  Note that for [DfracBoth q], we require that [q] is _strictly_ smaller
  than [1], reflecting that a fraction has been discarded, making it
  impossible to have total ownership.
*)

(**
  The lemma [dfrac_valid] converts a validity assertion into the
  corresponding propositions as defined by [dfrac_valid_instance].
*)

Lemma dfrac_valid_own : ✓ (DfracOwn (2/3)).
Proof.
  rewrite dfrac_valid.
  done.
Qed.

Lemma dfrac_valid_discarded : ✓ (DfracDiscarded).
(* Solution *) Proof.
  rewrite dfrac_valid.
  done.
Qed.

Lemma dfrac_invalid_own : ¬ (✓ (DfracOwn (2/3) ⋅ DfracOwn (2/3))).
Proof.
  rewrite dfrac_op2.
  rewrite dfrac_valid.
  auto.
Qed.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(** **** The Core (the [PCore A]) *)

(**
  For dfrac, ownership of a fraction should be exclusive, while
  knowledge that a fraction has been discarded should be freely
  shareable. We manifest this desire through the definition of the core.
*)

Print dfrac_pcore_instance.

(**
  That is, the core of a [DfracOwn] resource is [None].
*)
Lemma dfrac_core_own (q : Qp) : pcore (DfracOwn q) = None.
Proof. compute. done. Qed.

(**
  The core of [DfracDiscarded] is [Some DfracDiscarded].
*)
Lemma dfrac_core_discarded : pcore (DfracDiscarded) = Some DfracDiscarded.
Proof. compute. done. Qed.

(**
  And the most interesting case, the core of a [DfracBoth] resource is
  just [Some DfracDiscarded].
*)
Lemma dfrac_core_both (q : Qp) : pcore (DfracBoth q) = Some DfracDiscarded.
Proof. compute. done. Qed.

(**
  Recall that, in general, the core extracts _exactly_ the shareable
  part of a resource. Since only knowledge of a fraction having been
  discarded should be shareable, the image of the core should only
  contain [DfracDiscarded]. In particular, because all resources
  [DfracBoth q] can be written as [DfracDiscarded ⋅ DfracOwn q], the
  core of a [DfracBoth] resource should be just the shareable part:
  [DfracDiscarded].
*)

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(** **** The preorder (the [≼]) *)

(**
  Unlike the other components, the preorder is defined for us as the
  extension order: [x ≼ y = ∃z, y ≡ x ⋅ z]. The proposition [x ≼ y]
  expresses that [x] is included in [y].
*)

Lemma dfrac_pre_own : DfracOwn (1/4) ≼ DfracOwn (3/4).
Proof.
  exists (DfracOwn (2/4)).
  compute_done.
Qed.

Lemma dfrac_pre_disc_both : DfracDiscarded ≼ DfracBoth (3/4).
(* Solution *) Proof.
  exists (DfracOwn (3/4)).
  compute_done.
Qed.

Lemma dfrac_pre_own_both : DfracOwn (2/4) ≼ DfracBoth (3/4).
(* Solution *) Proof.
  exists (DfracBoth (1/4)).
  compute_done.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Frame Preserving Update *)

(**
  The final core ingredient we need for resource algebra is a way to
  update resources – resources are used to reason about programs, and
  programs update resources. One has to be careful with how resources
  are allowed to be updated; in Iris, only _valid_ resources can be
  owned. It should always be the case that, if we combine the resources
  owned by all threads in the system, the resulting resource should be
  valid. Otherwise, we could easily derive falsehood. Hence, when a
  thread updates its resources, it must ensure that it does not
  introduce the possibility of obtaining an invalid element. We call
  such an update a `frame preserving Update', and write [x ~~> y] to
  mean that we can perform a frame preserving update from resource [x]
  to resource [y]. The formal definition for this notion turns out to be
  quite succinct:

                [x ~~> y = ∀z, ✓(x ⋅ z) → ✓(y ⋅ z)]

  This proposition ensures that every resource that is valid with [x] is
  also valid with [y]. If this is the case, then it is okay to update
  [x] to [y]. Since [z] is forall quantified, [z] also represents the
  resource we get by combining the resources from all other threads.
  That is to say, [x ~~> y] ensures that, if the combination of all
  resources was valid before the update, it still is after. As [z]
  represents all the other resources, it is called the `frame', and the
  proposition [x ~~> y] expresses that the validity of [z] – the frame –
  is preserved, hence `frame preserving update'.
*)

(**
  Due to some technicalities, when the core is not total (i.e. the core
  is [None] for some resources), we use a slightly more general
  definition of the frame preserving update:

                [x ~~> y = ∀mz, ✓(x ⋅? mz) → ✓(y ⋅? mz)]

  The only difference is that the frame [mz] is now an option, i.e.
  [None] or [Some z]. The operation [⋅] does not work with option
  elements, so we use [a ⋅? mb] instead, which returns [a] if [mb] is
  [None], and [a ⋅ b] if [mb] is [Some b].
*)

(**
  To complicate matters further, the frame preserving update works for
  CMRAs in general, not just resource algebra. Hence, the actual
  definition of [~~>] is slightly more complex than above.
*)

Print "~~>".

(**
  However, when the CMRA is discrete (hence a resource algebra), we can
  prove that the actual definition of [~~>] is equivalent to our
  definition above.
*)

About cmra_discrete_update.

(**
  Further, if the core is total, it is also equivalent to our first
  definition of the frame preserving update.
*)

About cmra_discrete_total_update.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(** **** Example with dfrac *)

(**
  The by far most commonly used update for dfrac resources is to discard
  a fraction. Intuitively, such an update is frame preserving as only
  fractions greater than [1] are considered invalid. If a thread
  discards its fraction, the sum total from all threads will only
  decrease. So if the frame was valid before (i.e. less than or equal to
  [1]), it will remain valid after discarding. As such, we can always
  discard fractions.
*)

Check dfrac_discard_update.

Example dfrac_update : DfracOwn (2/3) ~~> DfracDiscarded.
Proof. apply dfrac_discard_update. Qed.

Example dfrac_update_disc : DfracDiscarded ~~> DfracDiscarded.
Proof. apply dfrac_discard_update. Qed.

(**
  Recall that, in the persistently chapter, we used the
  [pointsto_persist] lemma to make points-to predicates persistent.
  Looking deep under the hood, [pointsto_persist] actually uses
  [dfrac_discard_update] to discard the dfrac in [l ↦{dq} v].
*)

(**
  Of course, there are also other frame preserving updates for dfrac.
  However, these we must prove manually. Since the core of dfrac is not
  total, we can only use the definition of frame preserving update with
  the frame being an option ([cmra_discrete_update]).

  For example, a trivial update is the identity.
*)

Lemma dfrac_update_ident (dq: dfrac): dq ~~> dq.
Proof.
  rewrite cmra_discrete_update.
  intros mz Hvalid.
  apply Hvalid.
Qed.

(**
  We can also update a fraction by decreasing it.
*)

Lemma dfrac_update_own_own : DfracOwn (3/4) ~~> DfracOwn (1/4).
Proof.
  rewrite cmra_discrete_update.
  intros mz Hvalid.
  rewrite <- dfrac_op in Hvalid.
  rewrite cmra_op_opM_assoc in Hvalid. (* helper lemma from [cmra] *)
  rewrite dfrac_ra_mixin.(ra_comm _) in Hvalid.
  apply dfrac_ra_mixin.(ra_valid_op_l _) in Hvalid.
  apply Hvalid.
Qed.

(**
  We can additionally get [DfracDiscarded] when updating a fraction by
  decreasing it.
  Exercise: finish the proof of the example.
  Hint: use [cmra_discrete_update] to rewrite [dfrac_discard_update].
*)

Lemma dfrac_update_own_both : DfracOwn (3/4) ~~> DfracBoth (1/4).
Proof.
  rewrite cmra_discrete_update.
  intros mz Hvalid.
  rewrite <- dfrac_op in Hvalid.
  assert ((DfracBoth (1 / 4)) = (DfracDiscarded ⋅? Some (DfracOwn (1 / 4)))) as ->.
  { compute_done. }
  rewrite cmra_opM_opM_assoc_L.
(* BEGIN SOLUTION *)
  assert (∀dq mz, ✓(dq ⋅? mz) → ✓(DfracDiscarded ⋅? mz)) as
    Hdfrac_discard_update_discrete.
  { intros dq. rewrite <- cmra_discrete_update. apply dfrac_discard_update. }
  apply (Hdfrac_discard_update_discrete (DfracOwn (1/2))).
  rewrite <- cmra_opM_opM_assoc_L.
  simpl.
  apply Hvalid.
Qed.
(* END SOLUTION BEGIN TEMPLATE
  (* exercise *)
Admitted.
END TEMPLATE *)

(* ================================================================= *)
(** ** Example Resource Algebra *)

(**
  We have been using dfrac as a running example to introduce the
  concepts of resource algebra. While dfrac has some use cases on its
  own, it is especially useful when composed with other resource algebra
  (e.g. it is used to define the points-to predicate). Hence, in this
  section, we will introduce some often used resource algebras.

  Unlike dfrac, the resource algebras we study in this section are
  parametrised by other resource algebras (or OFEs, or CMRAs). This
  makes them generic, enabling us to use them to define more complex
  resource algebras.

  The collection of resource algebras we present here is by no means
  exhaustive – Iris ships with a myriad of useful resource algebras,
  which can be found at
  https://gitlab.mpi-sws.org/iris/iris/-/tree/master/iris/algebra.
*)

(* ----------------------------------------------------------------- *)
(** *** Exclusive *)

Section exclusive.

(**
  Our first example is the `exclusive' resource algebra. The key idea is
  that it makes all combinations of resources from some resource algebra
  invalid. The exclusive RA is actually parametrised by an OFE, but
  since all resource algebras are OFEs, the exclusive RA also works for
  resource algebras.

  Below, we let [A] be some OFE, but we may think of it as being the
  carrier for some resource algebra.
*)

Context {A : ofe}.

(**
  The carrier of the exclusive RA, [excl], is the same as the carrier of
  the underlying resource algebra with the addition of a bottom element,
  denoted [ExclBot].
*)

Print excl.

(**
  The core is always undefined (nothing is shareable).
*)

Lemma excl_core (ea : excl A) : pcore ea ≡ None.
Proof. constructor. Qed.

(**
  Crucially, all elements except [ExclBot] are valid.
*)

Lemma excl_valid (a : A) : ✓ (Excl a).
Proof. constructor. Qed.

Lemma excl_bot_invalid : ¬ (✓ (ExclBot : excl A)).
Proof.
  intros contra.
  inversion contra.
Qed.

(**
  And the combination of any two elements gives the invalid [ExclBot].
*)

Lemma excl_op (ea eb : excl A) : ea ⋅ eb ≡ ExclBot.
Proof. constructor. Qed.

(**
  Let us return to our beloved dfrac. While the operation for dfrac adds
  two dfrac fractions together, the operation for two _exclusive_ dfrac
  fractions simply results in [ExclBot].
*)

Example excl_op_dfrac :
  (Excl (DfracOwn (1/4))) ⋅ (Excl (DfracOwn (2/4))) ≡ ExclBot.
Proof. constructor. Qed.

End exclusive.

(**
  So how is this resource algebra useful? While it is a key component in
  many fairly complex resource algebras, it has a super simple, yet
  extremely practical use case. Together with the OFE [unitO], we can
  create the resource algebra of `tokens'.
*)

Section token.

(** The [unitO] OFE has just one element [()], called the unit. *)
Check () : unitO.

(** A token is then simply an exclusive unit. *)
Definition tok := Excl ().

(** The token is valid... *)
Lemma token_valid : ✓ tok.
Proof. apply excl_valid. Qed.

(** ... but having the token twice gives the bottom element... *)
Lemma token_token_bot : tok ⋅ tok ≡ ExclBot.
Proof. apply excl_op. Qed.

(* ... which is invalid. *)
Lemma token_exclusive : ¬ ✓ (tok ⋅ tok).
Proof. rewrite token_token_bot. apply excl_bot_invalid. Qed.

(**
  As only valid resources can be owned in Iris, and the contribution
  from all threads should yield a valid resource, we know that only a
  single token can be owned at any one time. Among others, this resource
  algebra is useful to reason about programs whose correctness rely on
  only one thread accessing some critical section of memory at a time.
  We will see concrete examples of this in later chapters.
*)

End token.

(* ----------------------------------------------------------------- *)
(** *** Agree *)

Section agree.

Context {A : ofe}.

(**
  The agree construction is parametrised by an ofe [A] (again, think
  carrier of resource algebra), and all it cares about is whether two
  resources are equivalent. That is, whether they _agree_. As such, the
  carrier of agree is the same as the carrier of the underlying resource
  algebra, and all resources in [agree A] are valid – irregardless of
  their validity in the original resource algebra.
*)

Lemma agree_valid (a : A) : ✓ (to_agree a).
Proof. constructor. Qed.

(**
  Additionally, we make all resources shareable.
*)

Lemma agree_core (a : agree A) : pcore a ≡ Some a.
Proof. constructor. done. Qed.


(**
  The key idea is that only resources that are equivalent in the
  original resource algebra can be combined.
*)

About to_agree_op_valid.

(**
  For instance, if the resources are dfrac fractions, the fractions have
  to be the same.
*)

Lemma agree_dfrac :
  ✓ (to_agree (DfracOwn (1/2)) ⋅ to_agree (DfracOwn (2/4))).
Proof.
  apply to_agree_op_valid.
  compute_done.
Qed.

Lemma disagree_dfrac :
  ¬ ✓ (to_agree (DfracOwn (1/4)) ⋅ to_agree (DfracOwn (2/4))).
Proof.
  intros contra.
  apply to_agree_op_valid in contra.
  inversion contra.
Qed.

(**
  If the composition of two elements is valid, it hence just amounts to
  composing a resource with itself. Since we only care about which
  resources are equivalent, we define composition as to be idempotent.
*)

About agree_idemp.

Lemma agree_dfrac_op :
  to_agree (DfracOwn (1/2)) ⋅ to_agree (DfracOwn (2/4)) ≡
  to_agree (DfracOwn (1/2)).
Proof.
  rewrite <- dfrac_frac_equiv.
  apply agree_idemp.
Qed.

(**
  As a result, if a composition is valid, the result is simply one of
  the two (equivalent) resources.
*)

Lemma agree_valid_opL (a b : A) : ✓ (to_agree a ⋅ to_agree b) →
  to_agree a ⋅ to_agree b ≡ to_agree a.
(* Solution *) Proof.
  intros Hvalid.
  apply to_agree_op_valid in Hvalid.
  rewrite Hvalid.
  apply agree_idemp.
Qed.

(**
  Due to idempotency and the fact that the combination of equivalent
  resources is valid, we get that the extension order coincides with
  equivalence.
*)

Local Lemma to_agree_included (a b : A) :
  to_agree a ≼ to_agree b ↔ a ≡ b.
Proof.
  split.
(* BEGIN SOLUTION *)
  - intros [c Hequiv].
    apply to_agree_op_valid.
    rewrite Hequiv.
    rewrite assoc.
    rewrite agree_idemp.
    rewrite <- Hequiv.
    apply agree_valid.
  - intros ->.
    done.
Qed.
(* END SOLUTION BEGIN TEMPLATE
  (* exercise *)
Admitted.
END TEMPLATE *)

(**
  The usefulness of the agree construction is demonstrated by the fact
  that it is used to define the resource of heaps. The inclusion of the
  agree RA allows us to conclude that, if we have two points-to
  predicates for the same location, [l ↦{dq1} v1] and [l ↦{dq2} v2],
  then they _agree_ on the value stored at the location: [v1 = v2].
*)

About pointsto_agree.

End agree.

(* ----------------------------------------------------------------- *)
(** *** Product *)

Section product.

(**
  While Iris supports reasoning about multiple different notions of
  resources simultaneously, it is sometimes useful to combine them at
  the level of resource algebras. To this end, we have the `product'
  resource algebra, [prodR], which is parametrised by _two_ CMRAs.
*)

Context {A B : cmra}.

(**
  Elements of the product resource algebra are pairs of elements from
  [A] and [B].
*)

Context {a : A} {b : B}.

Check (a, b) : prodR A B.

(**
  For the product RA, the two CMRAs are largely treated in parallel. For
  instance, pairs are composed component-wise.
*)

About pair_op.

(**
  A pair is valid exactly when its components are valid.
*)

About pair_valid.

(**
  A pair is included in another pair, if the components of the first are
  included in the components of the second.
*)

About pair_included.

(**
  When the core is defined for both of the components of a pair, the
  core of the pair is simply the core of the components.
*)

Lemma pair_pcore_some (ca : A) (cb : B) :
  pcore a = Some ca ->
  pcore b = Some cb ->
  pcore (a, b) = Some (ca, cb).
Proof.
  intros Hcore_a Hcore_b.
  rewrite pair_pcore.
  rewrite Hcore_a Hcore_b.
  simpl.
  reflexivity.
Qed.

(**
  However, if the core of just one of the components is undefined, then
  the core of the pair is also undefined.
*)

Lemma pair_pcore_dfrac : pcore (DfracOwn (1/2), b) = None.
Proof.
  rewrite pair_pcore.
  simpl.
  reflexivity.
Qed.

(**
  The product RA is often used in conjunction with dfrac and agree, with
  the first component being a dfrac, and the second being an element of
  some resource algebra wrapped in agree. This pattern is common enough
  that it has been added to Iris' library of resource algebras.
*)

Print dfrac_agreeR.

(**
  This construction is a simple way to make the resources of some
  resource algebra [A] shareable between threads in a safe way.
*)

End product.

(* ================================================================= *)
(** ** Ghost State *)

Section ghost.

(**
  In the previous sections, we duly studied the key concepts of resource
  algebras and a handful of basic examples. It is due time we put all
  that theory to use. In this section, we will see how to use resource
  algebras inside the Iris logic.
*)

(* ----------------------------------------------------------------- *)
(** ** Accessing Resource Algebras in Coq *)

(**
  To use a resource algebra inside the Iris logic, we first need to make
  the resource algebra available. As we have stated before, propositions
  in Iris have type [iProp Σ]. The [Σ] can be thought of as a global
  list of resource algebras that are available in the logic. The [Σ] is
  always universally quantified to enable composition of proofs.
  However, we may put _restrictions_ on [Σ], to specify that the list
  must contain some specific resource algebra of our choosing. The
  typeclass [inG Σ R] expresses that the resource algebra [R] is in the
  [G]lobal list of resource algebras [Σ]. If we add this to the Coq
  Context, then we may assume that [Σ] contains [R], which allows us to
  use [R] inside the logic.

  For instance, let us say that we want to use the resource algebra of
  exclusive unit. The resources algebra for exclusive is denoted
  [exclR], and we here instantiate it with the [unitO] OFE.
*)

Context `{!inG Σ (exclR unitO)}.

(**
  Similarly, if we want to use the resource algebra of discardable
  fractions, we assert that [Σ] must contain [dfracR] – the name of the
  resource algebra in Coq.
*)

Context `{!inG Σ dfracR}.

(**
  Libraries often bundle the resource algebras they need into their own
  typeclasses so that they do not have to expose the details of the
  resource algebras to clients. For instance, the [spawn] library
  includes its required resource algebras in the [spawnG Σ] typeclass.
  As such, adding this to the Coq Context makes the resource algebras
  required by [spawn] available.
*)

Context `{!spawnG Σ}.

(**
  Similarly, the [heapGS Σ] typeclass asserts that the resource of heaps
  is present in [Σ].
*)

Context `{!heapGS Σ}.

(**
  For additional information, please consult:
  https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/resource_algebras.md
*)

(* ----------------------------------------------------------------- *)
(** *** Ownership of Resources *)

(**
  Now that we have ensured that [Σ] contains our desired resource
  algebras, we can start using them inside the logic. Iris provides
  exactly one way of embedding a resource [r] from some resource algebra
  [R] into the logic: the proposition [own γ r] asserts _ownership_ of
  the resource [r] in an instance of the resource algebra [R] named [γ].
  That is to say, in Iris, once we have added a [R] to [Σ], we may
  create multiple instances of [R], so that the same resource in [R] may
  be owned multiple times. To distinguish between instances, we use
  `ghost names' (sometimes also called `ghost variables' or `ghost
  locations'), which is usually written with a lower-case gamma: [γ].

  For instance, as we have added [(exclR unitO)] to [Σ], we can define
  tokens as ownership of the single valid resource in the resource
  algebra.
*)

Definition token (γ : gname) := own γ (Excl ()).

(**
  We can have multiple tokens, each of which is associated with its own
  instance of the resource algebra. In this way, the [γ] serves as a
  name for the token.
*)

(**
  Looking under the hood, the points-to predicate [l ↦ v] is also
  defined in terms of [own]. That is, [l ↦ v] is just notation denoting
  ownership of a resource in the resource of heaps! But where is the
  ghost name [γ]? When adding the resource of heaps to [Σ], we do it
  with the [heapGS Σ] typeclass. Here, the [S] stands for `singleton',
  and signifies that only _one_ instance of the resource of heaps
  exists. As such, we do not need ghost names to distinguish between
  instances.
*)

(**
  If one owns multiple resources from the same instance of a resource
  algebra, then these resources may be combined with the [iCombine]
  tactic. Conversely, if one owns a resource that is composed of other
  resources, one may split up the ownership into the constituent
  resources with [iDestruct].

  That is, we have the following rule:

      [own γ a ∗ own γ b ⊣⊢ own γ (a ⋅ b)]

  Let's see an example of this.
*)

Lemma own_op_dfrac (γ : gname) :
  own γ (DfracOwn (1/4)) ∗ own γ (DfracBoth (1/4)) ∗-∗ 
  own γ (DfracBoth (1/2)).
Proof.
  iAssert (⌜DfracOwn (1 / 4) ⋅ DfracBoth (1 / 4) = DfracBoth (1 / 2)⌝)%I
  as "%Heq".
  { iPureIntro. compute_done. }
  (**
    Note that, whereas ownership of resources is not pure, assertions
    about the resources themselves are.
  *)
  iSplit.
  - iIntros "[Hdq1 Hdq2]".
    iCombine "Hdq1" "Hdq2" as "Hdq".
    rewrite Heq.
    done.
  - iIntros "Hdq".
    rewrite <- Heq.
    iDestruct "Hdq" as "[Hdq1 Hdq2]".
    iFrame.
Qed.

(**
  In Iris, all owned resources are valid. This knowledge can be
  extracted via the [iCombine] tactic. For instance, we can use it to
  prove that token ownership is exclusive.
*)

Lemma own_token_exclusive (γ : gname) :
  token γ ∗ token γ ⊢ False.
Proof.
  iIntros "[Htoken1 Htoken2]".
  iCombine "Htoken1 Htoken2" as "Hcombined" gives "%Hvalid".
  iPureIntro.
  apply token_exclusive.
  apply Hvalid.
Qed.

(**
  Todo: Persistency
*)

(* Todo: example with dfrac *)

(* ----------------------------------------------------------------- *)
(** *** Update Modality *)

(* TODO: do *)

(* ----------------------------------------------------------------- *)
(** *** Allocation and Updates *)

(* TODO: do *)

End ghost.
