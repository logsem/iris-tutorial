From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.

Section proofs.
Context {Σ : gFunctors}.

(*
  Iris is a step-indexed logic, meaning it has a build in notions of time.
  This can be expressed with the later modality `▷ P` signifying that `P` holds after one step.
*)


(*
  Iris allows induction on time steps using the tactic `iLöb`.
  `iLöb` allows us to conclude `((□ ▷ P) -∗ P) -∗ P`.
  Intuitively this is true because `▷ P` always holds at time 0,
  meaning `P` follows from `P 0` and `P n → P (S n)`, which is just induction on the natural numbers.
*)

(* Löb induction does however lead to a rather unintuitive fact. *)
Lemma later_false : ⊢@{iPropI Σ} ∃ n, ▷^ n False.
Proof.
  iLöb as "IH".
  iDestruct "IH" as "[%n IH]".
  iExists (S n).
  cbn.
  iApply "IH".
Qed.

(*
  A different time connective is except_0 writen `◇ P`. This is P, except true at time step 0.
  It's main use is in defining timeless propositions, meaning propositions that don't varry over time.
  It follows from the previous resoning that if `▷ P -∗ ◇ P` then all the timesteps of P are biimplicated.
  The ◇ here makes sure `P 0` does not need to hold simply by replacing it with `True`.
*)
Lemma except0_later (P : iProp Σ) : ◇ P -∗ ▷ P.
  iIntros "> H !>".
  iApply "H".
Qed.

End proofs.
