From iris.heap_lang Require Import lang proofmode notation.

Section heaplang.
Context `{!heapGS Σ}.

(*
  Heaplang is a rather simple language defined on top of iris.
  It's a right to left call by value language reminisent of lambda calculus.
  However it is equiped with a heap as well as multithreading.

  To see the language in action, let's define a small toy program.
*)
Definition prog : expr :=
  let: "x" := ref #1 in (* Allocate the number 1 on the heap *)
  "x" <- !"x" + #2;; (* Increment x by 2 *)
  !"x" (* Read the value of x *).

(*
  This program should evaluate to 3.
  To prove this we'll use the weakest precondition `WP`.
  This let's us specify a post condition we expect to hold if and when the program halts.
*)
Lemma wp_prog : ⊢ WP prog {{ v, ⌜v = #3⌝ }}.
Proof.
  rewrite /prog.
  (*
    Heaplang has a set of tactics describing evaluation of the language.
    The initial step of the program is to allocate the reference to 1.
    To do this we call `wp_alloc` with a name for the location and a name for the knowledge that the location stores 1.
  *)
  wp_alloc l as "Hl".
  (*
    As pure steps don't require external knowledge `wp_pures` is able to evaluate them automatically.
  *)
  wp_pures.
  (*
    Next we load the location `l` using the knowledge that it stores 1.
  *)
  wp_load.
  (* Then we evaluate the addition *)
  wp_pures.
  (*
    Storing is handled by `wp_store`.
    Notice that this updates `Hl`. This only works because we are working in a seperation logic.
  *)
  wp_store.
  (* Finally we use `wp_load` again *)
  wp_load.
  (*
    Now that the program is concluded, we are left with a fancy update modality.
    You can usually ignore this modality and simply introduce it.
  *)
  iModIntro.
  (* Now we are left with a trivial proof that 1+2 = 3 *)
  done.
Qed.
End heaplang.

(*
  The full list of evaluation tactics can be found at https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/heap_lang.md
*)
