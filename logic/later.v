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

End proofs.
