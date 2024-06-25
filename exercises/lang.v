From iris.heap_lang Require Import lang notation spawn par.
From iris.unstable.heap_lang Require Import interpreter.

(*########## CONTENTS PLAN ##########
- THIS FILE SHOULD ONLY INTRODUCE THE LANGUAGE
- POSSIBLY UTILISE THE HEAPLANG INTERPRETER FOR SOME EXAMPLES
- INTRODUCE BASIC CONSTRUCTS
  + EXAMPLES
- INTRODUCE HEAP
  + STORE
  + LOAD
  + CAS
  + EXAMPLES
- INTRODUCE CONCURRENCY PRIMITIVE (fork)
  + MENTION THAT MORE COMPLEX CONCURRENCY CONSTRUCTIONS ARE DERIVED FROM FORK, e.g. |||
#####################################*)

(* ################################################################# *)
(** * HeapLang *)

(* ================================================================= *)
(** ** Introduction *)

(**
  HeapLang is a concurrent programming language with a heap. It is an
  ML-like language, sporting many of the usual constructs such as
  let-expressions, λ-abstractions, and recursive functions. It also
  supports higher-order functions. The evaluation order is right to left
  and it is a call-by-value language.

  The syntax for HeapLang is fairly standard, but there are some quirks
  as we are working inside Coq. As the features of HeapLang are fairly
  standard, the focus in this file is manly on showcasing the syntax
  through simple examples for each of the basic constructs.
*)

Section heaplang.

(* ================================================================= *)
(** ** Pure Constructs *)

Example arith : expr :=
  #1 + #2 * #3.

Compute (exec 10 arith).

Example bools : expr :=
  #1 + #2 * #3 = #7.

Compute (exec 10 bools).

Example if_then_else : expr :=
  if: #1 + #2 * #3 = #7 then #() else #false.

Compute (exec 10 if_then_else).

Example lets : expr :=
  let: "a" := #4 in
  let: "b" := #2 in
  "a" + "b".

Compute (exec 10 lets).

Example pairs : expr :=
  let: "p" := (#40, #1 + #1) in
  Fst "p" + Snd "p".

Compute (exec 10 pairs).

Example tuples : expr :=
  let: "t1" := (#1, #2, #3, #4) in
  let: "t2" := (((#1, #2), #3), #4) in
  (Snd (Fst (Fst "t1")) = Snd (Fst (Fst "t2"))).

Compute (exec 10 tuples).

Example sums : expr :=
  let: "r" := InjR #1 in
  match: "r" with
    InjL "_" => #0
  | InjR "n" => "n" + #1
  end.

Compute (exec 10 sums).

Example lambda : expr :=
  (λ: "x", "x" + #5) #5.

Compute (exec 10 lambda).

Example recursion : expr :=
  let: "fac" :=
    rec: "f" "n" := if: "n" = #0 then #1 else "n" * "f" ("n" - #1)
  in
  ("fac" #4, "fac" #5).

Compute (exec 25 recursion).


(* ================================================================= *)
(** ** References *)

(** 
  References are dyncamically allocated through the [ref] instruction.
  Given a value, [ref] allocates a fresh cell on the heap, and stores
  the value in said cell. The location of the cell is returned.
*)

Example alloc : expr :=
  let: "l1" := ref (#0) in
  let: "l2" := ref (#0) in
  ("l1", "l2").

Compute (exec 10 alloc).

Example load : expr :=
  let: "l" := ref #5 in
  !"l".

Compute (exec 10 load).

Example store : expr :=
  let: "l" := ref #5 in
  "l" <- #6 ;;
  !"l".

Compute (exec 10 store).

Example cas : expr :=
  let: "l" := ref #5 in
  CAS "l" #6 #7 ;;  (* If "l" contains 6, set "l" to 7 *)
  let: "a" := !"l" in
  CAS "l" #5 #7 ;;  (* If "l" contains 5, set "l" to 7 *)
  let: "b" := !"l" in
  ("a", "b").

Compute (exec 10 cas).

(* ================================================================= *)
(** ** Concurrency *)

(** 
  HeapLang has only one primitive for concurrencty: [Fork]. The
  instruction [Fork e] creates a new thread which executes [e]. The
  invoking thread continues execution after creating the thread. If the
  computation of [e] terminates, then the resulting value is simply
  thrown away. Hence, [e] is only run for its side-effects.
*)

Example fork : expr :=
  let: "l" := ref #5 in
  Fork ("l" <- #7) ;;
  !"l".

(** 
  Unfortunately, in its current state, the interpreter does not support
  concurrency; the forked thread never executes its expression. Hence,
  the above program will always return [5]. Of course, this is only a
  limitation of this specific interpreter – HeapLang is still a
  concurrent programming language, and we still have to reason about
  forked threads inside the Iris logic.
*)

Compute (exec 10 fork).

(** 
  From the [Fork] primitive, we can implement several other
  constructions for concurrency. HeapLang ships with two such
  constructions, [spawn] and [par], which we will implement and prove
  correct later.
*)

(** 
  [spawn] takes a thunked experssions, and creates a new thread which
  executes said expression. Additionally, [spawn] returns a handle,
  which we can use in conjunction with [join] to wait for the result of
  the computation.
*)
Example spawn : expr :=
  let: "l" := ref #5 in
  let: "handle" := spawn (λ: "_", "l" <- #6;; #2) in
  let: "res" := spawn.join "handle" in
  let: "v" := !"l" in
  ("res", "v").
  (* Evaluates to [(2, 6)]. *)

(** 
  Using the [spawn] construct, we can define [par] which runs two
  expressions in parallell. We define the notation [e1 ||| e2] for
  [par], which states that [e1] and [e2] are run in parallel. Once both
  expressions have terminated, the resulting values are returned in a
  pair.
*)
Example par : expr :=
  let: "l" := ref #5 in
  let: "res" := (!"l" + #1) ||| (!"l" + #2) in
  Fst "res" + Snd "res". 
  (* Evaluates to [13]. *)

End heaplang.
