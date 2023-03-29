From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.

Section proofs.
Context {Σ : gFunctors}.

(*
  Iris is a step-indexed logic, meaning it has a build in notions of
  time. This can be expressed with the later modality `▷ P` signifying
  that `P` holds after one step.
*)


(*
  Iris allows induction on time steps using the tactic `iLöb`. `iLöb`
  allows us to conclude `(▷ P -∗ P) -∗ P`. Intuitively this is true
  because `▷ P` always holds at time 0, meaning `P` follows from `P 0`
  and `P n → P (S n)`, which is just induction on the natural numbers.
*)

(*
  Löb induction does however lead to a rather unintuitive facts, like
  `∃ n, ▷^ n False`. This is true because existance works a little
  differently than you might expect. Instead of saying there exists
  some value such that the satement holds for all time steps. exists
  actually states that for each time step, there exists a value such
  that the statement holds up to that amount of time. This means that
  is need not be the same value for all time steps.

  In this case we are actually stating that for every timestep there
  is a later time step.
*)
Lemma later_false : ⊢@{iPropI Σ} ∃ n, ▷^ n False.
Proof.
  iLöb as "IH".
  iDestruct "IH" as "[%n IH]".
  iExists (S n).
  cbn.
  iApply "IH".
Qed.

(*
  A different time connective is except_0 writen `◇ P`. This is P,
  except true at time step 0. It's main use is in defining timeless
  propositions, meaning propositions that don't varry over time. It
  follows from the previous resoning that if `▷ P -∗ ◇ P` then all the
  timesteps of P are biimplicated. The ◇ here makes sure `P 0` does
  not need to hold simply by replacing it with `True`.
*)
Lemma except0_later (P : iProp Σ) : ◇ P -∗ ▷ P.
  iIntros "> H !>".
  iApply "H".
Qed.

(*
  Later is very benificial when defining propositions recursively as
  it acts like a guard. If you have experience with cofix in coq, you
  can think of later as a constructor guarding recursive calls.
  
  Iris propositions live in the category of cofes (Complete ordered
  family of equivalences). The details of this are not very important.
  It mainly means that functions used for fixpoints must be
  `NonExpansive` intuitively meaning that they preserve time. All the
  operations we've seen thus far are infact NonExpansive.

  Bodies of Iris fixpoints actually need to satisfy a slightly
  stronger property called Contractive intuitively stating that the
  recursive call happens later. As you would expect, ▷ is Contractive
  and is therefor useable as a guard.

  Like coq fixpoints, Iris fixpoints can have extra parameters, these
  parameters are useally specified using -d>. This special arrow tells
  Iris that the parameter of the function does not depend on time and
  can therfor be any coq type.
*)


End proofs.
