From iris.algebra Require Import cmra dfrac.
From iris.heap_lang Require Import lang proofmode notation.

(*########## CONTENTS PLAN ##########
- INTRODUCTION TO RESOURCE ALGEBRA
- BASIC DEFINITION AND COMPONENTS (FROM ILN)
  + DEFINITION
  + DFRAC RUNNING EXAMPLE
  + FRAME PRESERVING UPDATE
- EXAMPLE RESOURCE ALGEBRA
- HOW TO ACCESS THEM IN COQ. CONTEXT, Σ
  + SEE https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/resource_algebras.md
- BASIC EXAMPLES
  + EXCLUSIVE
    * TOKENS (custom definition, not from lib)
  + AGREE
  + PRODUCTS
  + AUTH
- GHOST STATE
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
  are `discrete CMRAs', meaning they do not have a notion of time. In
  turn, CMRAs are built on top of `Ordered Families of Equations'. The
  exact details of these concepts are not important for this chapter,
  but we mention them as they appear a few times throughout the chapter.
  CMRAs and OFEs are covered in more detail in later chapters. The focus
  point in this chapter is discerete CMRAs – resource algebra.
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

  These components must satisfy certain properties, but before
  discussing those, let us discuss the purpose of each component.

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
  algebras are instances of the record [RAMixin], which describes the
  properties the components should satisfy.
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
  familiar example: discarded fractions (shortened to dfrac). We saw
  discarded fragments when we introduced the persistent points-to
  predicate in the persistently chapter. As it turns out, the resource of
  heaps is actually composed of other resource algebras, one of which is
  dfrac.

  As dfrac is a resource algebra, it is an instance of [RAMixin].
*)

Check dfrac_ra_mixin.

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

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(** **** Equivalence of Resources (the [Equiv A]) *)

(**
  For dfrac, we simply use leibniz equality [=] as our equivalence
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
Proof.
  (* exercise *)
Admitted.

Lemma dfrac_op_frac_both : ∃ x : dfrac,
  DfracOwn (1/4) ⋅ DfracBoth (2/4) = x.
Proof.
  (* exercise *)
Admitted.

(**
  As dfrac is an instance of [RAMixin], we know that [⋅] must be
  associative and commutative.
*)

Lemma dfrac_op_assoc (dq1 dq2 dq3 : dfrac) :
  dq1 ⋅ dq2 ⋅ dq3 = dq1 ⋅ (dq2 ⋅ dq3).
Proof.
  rewrite ra_assoc.
  - done.
  - apply dfrac_ra_mixin.
Qed.

Lemma dfrac_op_comm (dq1 dq2 : dfrac) :
  dq1 ⋅ dq2 = dq2 ⋅ dq1.
Proof.
  (* exercise *)
Admitted.

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

(* TODO: write explanatory text *)

(* TODO: relate to persistent points-to predicate from persistency chapter *)

Print dfrac_pcore_instance.

Lemma dfrac_core_own (q : Qp) : pcore (DfracOwn q) = None.
Proof. compute. done. Qed.

Lemma dfrac_core_discarded : pcore (DfracDiscarded) = Some DfracDiscarded.
Proof. compute. done. Qed.

(**
  Note that the core of a [DfracBoth] element is just [DfracDiscarded].
*)

Lemma dfrac_core_both (q : Qp) : pcore (DfracBoth q) = Some DfracDiscarded.
Proof. compute. done. Qed.

(**
  The reason is that we want the fraction [q] to be exclusive, whereas
  knowledge of a fraction having been discarded should be shareable. The
  element [DfracBoth q] consists of both the fraction [q] and the
  knowledge that a fraction has been discarded. Since the core extracts
  exactly the shareable part of an element, the core of a [DfracBoth]
  element should be [DfracDiscarded].
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

(* TODO: do *)

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(** **** Example with dfrac *)

(* TODO: do *)

Check dfrac_discard_update.

Example dfrac_update : DfracOwn (2/3) ~~> DfracDiscarded.
Proof. apply dfrac_discard_update. Qed.

Example dfrac_update_disc : DfracDiscarded ~~> DfracDiscarded.
Proof. apply dfrac_discard_update. Qed.

(**
  Recall that we used the [pointsto_persist] lemma to make points-to
  predicates persistent. Looking deep under the hood, [pointsto_persist]
  uses [dfrac_discard_update] to discard the dfrac in [l ↦{dq} v].
*)

(* ================================================================= *)
(** ** Example Resource Algebra *)

(**
  We have been using dfrac as a running example to introduce the
  concepts of resource algebra. While dfrac has some use cases on its
  own, it is especially useful when composed with other resource algebra
  (e.g. it is used to define the points-to predicate). Hence, in this
  section, we will introduce some often used resource algebras.

  Unlike dfrac, most of the resource algebras we study in this section
  are parametrised by other resource algebras (or OFEs, or CMRAs). This
  makes them generic, enabling us to use them to define more complex
  resource algebras.

  The collection of resource algebras we present here is by no means
  exhaustive – Iris ships with a myriad of useful resource algebras,
  which can be found at
  https://gitlab.mpi-sws.org/iris/iris/-/tree/master/iris/algebra.
*)

(* TODO: introductory text *)

(* ----------------------------------------------------------------- *)
(** *** Exclusive *)

(* TODO: do *)

(* TODO: also custom tokens (through unitO) *)

(* ----------------------------------------------------------------- *)
(** *** Agree *)

(* TODO: do *)

(* ----------------------------------------------------------------- *)
(** *** Product *)

(* TODO: do *)

(* ----------------------------------------------------------------- *)
(** *** Auth *)

(* TODO: do *)

(* ================================================================= *)
(** ** Accessing Resource Algebras in Coq *)

(* TODO: do *)

(**
  https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/resource_algebras.md
*)

(* ================================================================= *)
(** ** Ghost State *)

(* TODO: introductory text *)

(* ----------------------------------------------------------------- *)
(** *** Ownership of Resources *)

(* TODO: notation for ownership *)
(* TODO: multiple instances of the same algebra: Ghost names *)
(* TODO: combining ownership and validity *)

(* ----------------------------------------------------------------- *)
(** *** Update Modality *)

(* TODO: do *)

(* ----------------------------------------------------------------- *)
(** *** Allocation and Updates *)

(* TODO: do *)
