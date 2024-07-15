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

(* TODO: Explain in words what a RA is (see ILN). *)
(* TODO: In Iris, all RA are instances of the RAMixin record. *)

Print RAMixin.

(**
  TODO: explain RAMixin (essentially definition of RA)

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

  TODO: When creating a new resource algebra, one must show that it
  satisfies all of above. However, in this chapter, and in most
  scenarios for that matter, we will not create resource algebras from
  nothing. We can utilise existing resource algebra and compose them to
  create a resource algebra that suitably models our desired notion of a
  resource. This means that we do not have to prove all of the above lemmas.
*)

(* ----------------------------------------------------------------- *)
(** *** Definition of RA by Example: dfrac *)

(* TODO: introductory text. relate to points-to predicate *)

Check dfrac_ra_mixin.

(**
  https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/algebra/dfrac.v
*)

(** **** The Carrier (the [A])*)

Print dfrac.

(** **** Operation (the [Op A]) *)

Print dfrac_op_instance.

Lemma dfrac_op : DfracOwn (1/2) ⋅ DfracOwn (1/4) = DfracOwn (3/4).
Proof. compute_done. Qed.

Lemma dfrac_op2 : DfracOwn (2/3) ⋅ DfracOwn (2/3) = DfracOwn (4/3).
Proof. compute_done. Qed.

Lemma dfrac_op_disc : DfracDiscarded ⋅ DfracDiscarded = DfracDiscarded.
Proof. compute_done. Qed.

Lemma dfrac_op_both : DfracOwn (2/3) ⋅ DfracDiscarded = DfracBoth (2/3).
Proof. compute_done. Qed.

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

(** **** Valid Elements (the [Valid A]) *)

Print dfrac_valid_instance.

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

(** **** The Core (the [PCore A]) *)

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

(** **** Summary *)

(* TODO: do *)

(* ----------------------------------------------------------------- *)
(** *** Frame Preserving Update *)

(* TODO: do *)

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
