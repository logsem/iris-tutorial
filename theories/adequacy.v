From iris.algebra Require Import excl.
From iris.heap_lang Require Import adequacy lang proofmode notation par.
From iris_tutorial Require Import spin_lock.

(*
  Weakest precondiction of heaplang satisfies something called
  adequacy. This is the statement that `WP e {{ v, ⌜φ v⌝}}`, then
  all expresions that e reduces to are either value satifying φ, or
  they can be reduced further.

  Let's use the spin-lock program as an example.

  To show adequacy for prog, we have to specify a Σ containing the
  resources we require.
*)
Definition progΣ := #[
  heapΣ; (* The resources required for heaplang itself *)
  GFunctor (exclR unitO) (* The camera we used for spin-lock *)
].

Lemma prog_adequacy σ : adequate NotStuck prog σ (λ v _, v = #0 ∨ v = #1).
Proof.
  apply (heap_adequacy progΣ).
  iIntros "%_ _".
  unshelve iApply prog_spec.
  apply (subG_inG _ (GFunctor (exclR unitO))).
  apply subG_app_r, subG_refl.
Qed.
