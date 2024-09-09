From iris.heap_lang Require Import lang notation spawn par.

(* ################################################################# *)
(** * HeapLang *)

(* ================================================================= *)
(** ** Introduction *)

(**
  HeapLang is an untyped concurrent programming language with a heap. It
  is an ML-like language, sporting many of the usual constructs such as
  let expressions, lambda abstractions, and recursive functions. It also
  supports higher-order functions. The evaluation order is right to left
  and it is a call-by-value language.

  The syntax for HeapLang is fairly standard, but there are some quirks
  as we are working inside Coq. As the features of HeapLang are fairly
  standard, the focus in this chapter is mainly on showcasing the syntax
  of the language through simple examples.
*)

(* ================================================================= *)
(** ** The HeapLang Interpreter (Optional) *)

(**
  HeapLang is primarily made to be reasoned about using Iris. However,
  there is a rudimentary interpreter for HeapLang located in
  [iris.unstable.heap_lang]. The interpreter provides the function
  [exec], which takes as input some fuel and an expression. The
  expression is then executed until it terminates at a value [v], the
  execution runs out of fuel, or the program gets stuck. In case of
  termination, [inl v] is returned. Otherwise [inr err] is returned,
  with [err] describing the error.
*)

(**
  By default, the interpreter is not installed as it can only be used
  with development versions of Iris. The interpreter is not required for
  the tutorial, but it can optionally be installed for this chapter. To
  install it, run:

    <<opam install coq-iris-unstable>>

  This also updates Iris to a development version. To access the
  interpreter, uncomment the import below.
*)

(* From iris.unstable.heap_lang Require Import interpreter. *)

(**
  To return to a release version of Iris known to be compatible with the
  rest of the tutorial, run:

    <<opam install . --deps-only>>

  This also uninstalls the interpreter.
*)

(* ================================================================= *)
(** ** Pure Constructs *)

Section heaplang.

(**
  HeapLang has native support for integers and booleans. With these, we
  can do basic arithmetic and control flow.
  Note that values in HeapLang are prefixed by a [#].
*)

Example arith : expr :=
  #1 + #2 * #3.

(**
  If the interpreter was installed, the expression can now be executed
  using [(exec 10 arith)], where [10] is the amount of fuel. To evaluate
  the execution inside Coq, we can use the [Compute] command. Uncomment
  the command below to see this in action.
*)
(* Compute (exec 10 arith). *)
(** Evaluates to [inl #7] *)

Example booleans : expr :=
  (arith = #7) && #true || (#true = #false).

(* Compute (exec 10 booleans). *)
(** Evaluates to [inl #true] *)

Example if_then_else : expr :=
  if: booleans then #() else #false.

(* Compute (exec 10 if_then_else). *)
(** Evaluates to [inl #()] *)

(**
  Heaplang supports let expressions. Technically, let expressions are
  not native to HeapLang. We get let expressions from the [notation]
  package, which defines them in terms of lambda abstractions.
  Note that variables in HeapLang are strings.
*)

Example lets : expr :=
  let: "a" := #4 in
  let: "b" := #2 in
  "a" + "b".

(* Compute (exec 10 lets). *)
(** Evaluates to [inl #6] *)

(**
  HeapLang has native support for pairs, with tuples being notation for
  nested pairs.
*)

Example pairs : expr :=
  let: "p" := (#40, #1 + #1) in
  Fst "p" + Snd "p".

(* Compute (exec 10 pairs). *)
(** Evaluates to [inl #42] *)

Example tuples : expr :=
  let: "t1" := (#1, #2, #3, #4) in
  let: "t2" := (((#1, #2), #3), #4) in
  (Snd (Fst (Fst "t1")) = Snd (Fst (Fst "t2"))).

(* Compute (exec 10 tuples). *)
(** Evaluates to [inl #true] *)

(**
  We can also do pattern matching using sums. A common use case of sums
  is the `option' construction. The [notation] package has us covered
  here as well.
*)

Example sums : expr :=
  let: "r" := InjR #1 in
  match: "r" with
    InjL "_" => #0
  | InjR "n" => "n" + #1
  end.

(* Compute (exec 10 sums). *)
(** Evaluates to [inl #2] *)

Example option : expr :=
  let: "r" := SOME #1 in
  match: "r" with
    NONE => #0
  | SOME "n" => "n" + #1
  end.

(* Compute (exec 10 option). *)
(** Evaluates to [inl #2] *)

(**
  Finally, we have lambda abstractions and recursive functions. As with
  let expressions, lambda abstractions are also a derived construct –
  they are recursive functions that do not recurse. In HeapLang,
  functions are first-class citizens, which gives support for
  higher-order functions.
*)

Example lambda : expr :=
  let: "add5" := (λ: "x", "x" + #5) in
  let: "double" := (λ: "x", "x" * #2) in
  let: "compose" := (λ: "f" "g", (λ: "x", "g" ("f" "x"))) in
  ("compose" "add5" "double") #5.

(* Compute (exec 10 lambda). *)
(** Evaluates to [inl #20] *)

Example recursion : expr :=
  let: "fac" :=
    rec: "f" "n" := if: "n" = #0 then #1 else "n" * "f" ("n" - #1)
  in
  ("fac" #4, "fac" #5).

(* Compute (exec 25 recursion). *)
(** Evaluates to [inl (#24, #120)] *)

(* ================================================================= *)
(** ** References *)

(**
  References are dynamically allocated through the [ref] instruction.
  Given a value, [ref] finds a fresh location on the heap and stores the
  value there. The location is then returned.
*)

Example alloc : expr :=
  let: "l1" := ref (#0) in
  let: "l2" := ref (#0) in
  ("l1", "l2").

(* Compute (exec 10 alloc). *)
(** Evaluates to [inl (#(Loc 1), #(Loc 2))] *)

(**
  After allocation, we can read and update the value at the returned
  location [l] with [!l] and [l <- v], respectively.
*)

Example load : expr :=
  let: "l" := ref #5 in
  !"l".

(* Compute (exec 10 load). *)
(** Evaluates to [inl #5] *)

Example store : expr :=
  let: "l" := ref #5 in
  "l" <- #6 ;;
  !"l".

(* Compute (exec 10 store). *)
(** Evaluates to [inl #6] *)

(**
  To allow for synchronisation between threads, HeapLang provides a
  single primitive called compare-and-exchange, written
  [CmpXchg l v1 v2]. This instruction atomically reads the contents of
  location [l], checks if it is equal to [v1], and, in case of equality,
  updates [l] to contain [v2]. The instruction returns a pair [(v, b)],
  with [v] being the original value stored at [l], and [b] a boolean
  indicating whether the location was updated.
*)

Example cmpxchg_fail : expr :=
  let: "l" := ref #5 in
  CmpXchg "l" #6 #7.

(* Compute (exec 10 cmpxchg_fail). *)
(** Evaluates to [inl (#5, #false)] *)

Example cmpxchg_suc : expr :=
  let: "l" := ref #5 in
  CmpXchg "l" #5 #7.

(* Compute (exec 10 cmpxchg_suc). *)
(** Evaluates to [inl (#5, #true)] *)

(**
  The [notation] package defines a variant of [CmpXchg] called
  compare-and-set, written [CAS l v1 v2]. The only difference is that
  [CAS] only returns the boolean [b].
*)

Example cas : expr :=
  let: "l" := ref #5 in
  if: CAS "l" #6 #7 then
    #()
  else
    let: "a" := !"l" in
    if: CAS "l" #5 #7 then
      let: "b" := !"l" in
      ("a", "b")
    else
      #().

(* Compute (exec 10 cas). *)
(** Evaluates to [inl (#5, #7)] *)

(* ================================================================= *)
(** ** Concurrency *)

(**
  HeapLang has only one primitive for concurrency: [Fork]. The
  instruction [Fork e] creates a new thread which executes [e]. The
  invoking thread continues execution after creation. If the computation
  of [e] terminates, then the resulting value is simply thrown away.
  Hence, [e] is only run for its side effects.
*)

Example fork : expr :=
  let: "l" := ref #5 in
  Fork ("l" <- #7) ;;
  !"l".

(**
  Unfortunately, in its current state, the HeapLang interpreter does not
  support concurrency; the forked thread never executes its expression.
  Hence, the above program will always return [5]. Of course, this is
  only a limitation of this specific interpreter – HeapLang is still a
  concurrent programming language, and we still have to reason about
  forked threads inside the Iris logic.
*)

(* Compute (exec 10 fork). *)
(** Evaluates to [inl #5] *)

(**
  From the [Fork] primitive, we can implement several other
  constructions for concurrency. HeapLang ships with two such
  constructions, [spawn] and [par], which we will implement and prove
  correct later.
*)

(**
  [spawn] takes a thunked expression and creates a new thread which
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
  expressions in parallel. We define the notation [e1 ||| e2] for
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
