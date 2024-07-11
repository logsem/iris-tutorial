From iris.algebra Require Import cmra.
From iris.heap_lang Require Import lang proofmode notation.

(*########## CONTENTS PLAN ##########
- INTRODUCTION TO RESOURCE ALGEBRA
- BASIC DEFINITION AND COMPONENTS (FROM ILN)
  + DEFINITION
  + FRAME PRESERVING UPDATE
- MANY USEFUL RA ALREADY CREATED
- HOW TO ACCESS THEM IN COQ. CONTEXT, Σ
  + SEE https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/resource_algebras.md
- BASIC EXAMPLES
  + HEAPS (POINTS-TO PREDICATE)
  + DFRAC
  + AGREE
  + EXCLUSIVE
    * TOKENS (custom definition, not from lib)
  + PRODUCTS
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

(* TODO: explain ideas of RA. Relate to resource of heaps *)
(* TODO: Ra is oblivious to existence of Iris: it is a fundamental concept *)
(* TODO: Iris is `enriched' with RA through `ghost state'. We study this
in the last section of this chapter *)
(* TODO: Mention how RA's are defined from CMRA. See below. *)
(* TODO: Technically, RA is a special case of the more general
structure: CMRA. In particular, it is a `discrete' CMRA, meaning it does
not depend on time. Further, CMRA are defined in terms of `Ordered
Families of Equations' (OFE). Mention this for the cases where this
information bleeds through the RA abstraction. *)
(* TODO: We focus on discrete CMRA, i.e. RA, in this chapter. *)

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
(** *** Frame Preserving Update *)

(* ================================================================= *)
(** ** Example Resource Algebra *)

(* ----------------------------------------------------------------- *)
(** *** Dfrac *)

(* ----------------------------------------------------------------- *)
(** *** Exclusive *)

(* TODO: also custom tokens *)

(* ----------------------------------------------------------------- *)
(** *** Agree *)

(* ----------------------------------------------------------------- *)
(** *** Product *)

(* ----------------------------------------------------------------- *)
(** *** Gmap *)

(* ----------------------------------------------------------------- *)
(** *** Heap *)

(* TODO: Also mention how heap is defined in terms of other RA *)

(** *** Auth *)

(* ================================================================= *)
(** ** Accessing Resource Algebras in Coq *)

(* ================================================================= *)
(** ** Ghost State *)

(* ----------------------------------------------------------------- *)
(** *** Ownership of Resources *)

(* TODO: notation for ownership *)
(* TODO: multiple instances of the same algebra: Ghost names *)
(* TODO: combining ownership and validity *)


(* ----------------------------------------------------------------- *)
(** *** Update Modality *)

(* ----------------------------------------------------------------- *)
(** *** Allocation and Updates *)

