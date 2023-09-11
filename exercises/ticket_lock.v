From iris.algebra Require Import auth excl gset numbers.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.

(**
  Let's look at another implementation of a lock, namely a ticket
  lock. Instead of having every thread fight to acquire the lock. The
  ticket lock makes them wait in line. It does this by maintaining two
  counters representing queue positions. The first counter is the
  position next in line to access the critical region. While the
  second counter is the end of the line.
  A thread can acquire the lock by incrementing the second counter and
  keeping its previous value as a ticket for it's position in the
  queue. When the first counter reachest this ticket value, the thread
  gains access to the critical region. The thread can then release the
  lock by incrementing the first counter.
*)
Definition mk_lock : val :=
  λ: <>, (ref #0, ref #0).
Definition wait : val :=
  rec: "wait" "n" "l" :=
  let: "o" := !(Fst "l") in
  if: "o" = "n" then #() else "wait" "n" "l".
Definition acquire : val :=
  rec: "acquire" "l" :=
  let: "n" := !(Snd "l") in
  if: CAS (Snd "l") "n" ("n" + #1) then
    wait "n" "l"
  else
    "acquire" "l".
Definition release : val :=
  λ: "l", Fst "l" <- ! (Fst "l") + #1.

(**
  As a ticket lock is a lock. So we expect it to satisfy the same
  specification as the spin lick. This time you have to find the
  necessary resource and lock invariant by your self.
*)

Definition RA : cmra
  (* := insert your definition here *). Admitted.

Section proofs.
Context `{!heapGS Σ, !inG Σ RA}.
Let N := nroot .@ "ticket_lock".

Definition lock_inv (γ : gname) (lo ln : loc) (P : iProp Σ) : iProp Σ
  (* := insert your definition here *). Admitted.

Definition is_lock (γ : gname) (l : val) (P : iProp Σ) : iProp Σ :=
  ∃ lo ln : loc, ⌜l = (#lo, #ln)%V⌝ ∗ inv N (lock_inv γ lo ln P).

Definition locked (γ : gname) : iProp Σ
  (* := insert your definition here *). Admitted.

Definition issued (γ : gname) (x : nat) : iProp Σ
  (* := insert your definition here *). Admitted.

Lemma locked_excl γ : locked γ -∗ locked γ -∗ False.
Proof.
  (* exercise *)
Admitted.

Lemma mk_lock_spec P : {{{ P }}} mk_lock #() {{{ γ l, RET l; is_lock γ l P }}}.
Proof.
  (* exercise *)
Admitted.

Lemma wait_spec γ l P x : {{{ is_lock γ l P ∗ issued γ x }}} wait #x l {{{ RET #(); locked γ ∗ P }}}.
Proof.
  (* exercise *)
Admitted.

Lemma acquire_spec γ l P : {{{ is_lock γ l P }}} acquire l {{{ RET #(); locked γ ∗ P }}}.
Proof.
  (* exercise *)
Admitted.

Lemma release_spec γ l P : {{{ is_lock γ l P ∗ locked γ ∗ P }}} release l {{{ RET #(); True }}}.
Proof.
  (* exercise *)
Admitted.

End proofs.
