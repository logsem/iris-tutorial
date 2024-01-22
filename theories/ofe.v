From iris.algebra Require Export ofe.

(**
  In this file, we will look at streams of natural numbers and
  introduce the concept of an OFE (Ordered Family of Equivalences).
  These are types equipped with equivalences [_ ≡{n}≡ _] indexed by
  the natural numbers through the type-class [Dist]. The key intuition
  behind OFEs is that elements x and y are n-equivalent [x ≡{n}≡ y] if
  they cannot be distinguished by a program running for no more than n
  steps.

  The name [dist] may seem strange as we are not talking about
  distances, but it can be used to define an ultrametric by defining
  the distance as 1/n when x and y are at most n-equivalent. Note
  however, it is not necessary to know anything about metric spaces to
  understand OFEs.

  [iProp] is intuitively a kind of step-indexed propositions, meaning
  we can equip it with an OFE structure, such that [P ≡{n}≡ Q] when
  they agree on the first n steps. So [P ≡ Q] exactly when [P ⊣⊢ Q].

  There are two important classes of functions between OFEs:
  - [NonExpansive] functions that preserve [dist] defined as
    [∀ n, Proper (dist n ==> dist n) f]. Intuitively this means that
    f does not increase the steps it takes to distinguish elements.
    However, f is allowed to decrease or maintain the steps it takes
    to distinguish elements.
  - [Contractive] functions satisfying
    [∀ n, Proper (dist_later n ==> dist n) f]. Intuitively this means
    that f always decreases the amount of steps it takes to
    distinguish elements.
  
  Importantly, all the connectives we have seen on [iProp] are
  non-expansive. This means that when working on paper, we don't need
  To keep track of which functions are non-expansive because
  everything you can write is non-expansive. However, in this coq
  formalization, we can access the model of Iris and define new
  operations that may not be non-expansive. As such, we sometimes
  manually have to prove non-expansiveness.

  [▷ _] is contractive.

  A chain [c] is a cauchy sequence in the sense that
  [∀ n i, n ≤ i → c i ≡{n}≡ c n].

  A complete OFE or COFE is an OFE such that all cauchy sequences have
  a limit.

  If [A] is a COFE, then all contractive functions [f : A → A] have a
  unique fixpoint [fixpoint f]. A fixpoint here means a value
  satisfying [f x ≡ x]. With this, we can recursively define
  predicates in [iProp] by guarding the recursive calls behind a
  later.

  An element [x] is called discrete if
  [∀ y, x ≡{0}≡ y → x ≡ y]
  This implies that all n-equivalences are just equivalence when
  relating [x].


*)

(*
  We will look at stream over natural numbers. These are infinite
  sequences with [head] being the first value, and [tail] being the
  rest of the stream.
*)
CoInductive stream := SCons {
  head : nat;
  tail : stream
}.
Add Printing Constructor stream.

CoFixpoint zeros := SCons 0 zeros.

Global Instance stream_inhabited : Inhabited stream := populate zeros.

(*
  We can get the nth element of the stream by iterating through the
  stream until we find the index we are looking for.
*)
Fixpoint nth (s : stream) (n : nat) : nat :=
  match n with
  | 0 => head s
  | S n => nth (tail s) n
  end.

(*
  We can likewise define a stream from its nths elements
*)
CoFixpoint fun2stream (f : nat → nat) : stream :=
  SCons (f 0) (fun2stream (f ∘ S)).

Lemma fun2stream_nth (f : nat → nat) (n : nat) : nth (fun2stream f) n = f n.
Proof.
  induction n in f |- *; simpl.
  - done.
  - apply IHn.
Qed.

(*
  Now, to equip our stream type with an OFE structure, we will need to
  instantiate a couple of type-classes. to avoid polluting the
  type-class database, we will define these instances localy in a
  section. These instances will then only be exposed via the ofe
  structure.
*)
Section ofe.

(*
  We will say that two streams are equivalent when the elements are
  equal. We can define this using the following coinductive
  definition.
*)
CoInductive stream_equiv_instance : Equiv stream :=
  | stream_equiv_scons s1 s2 : head s1 = head s2 → tail s1 ≡ tail s2 → s1 ≡ s2.
Local Existing Instance stream_equiv_instance.

Lemma stream_equiv_head (s1 s2 : stream) : s1 ≡ s2 → head s1 = head s2.
Proof. by intros []. Qed.

Lemma stream_equiv_tail (s1 s2 : stream) : s1 ≡ s2 → tail s1 ≡ tail s2.
Proof. by intros []. Qed.

(*
  This is the same as saying that the nth's elements are equal for all
  n.
*)
Lemma stream_equiv_nth (s1 s2 : stream) :
  s1 ≡ s2 ↔ ∀ n, nth s1 n = nth s2 n.
Proof.
  split.
  - intros H n.
    induction n in s1, s2, H |- *; simpl.
    + by apply stream_equiv_head.
    + by apply IHn, stream_equiv_tail.
  - revert s1 s2.
    cofix IH.
    intros s1 s2 H.
    apply stream_equiv_scons.
    + apply (H 0).
    + apply IH.
      intros n.
      apply (H (S n)).
Qed.

(*
  Imagine a program that reads one element of the stream at every
  step. To this program two stream will look the same for n steps if
  the first n elements are the same. This defines a family of
  equivalence relations as follows:
*)
Local Instance stream_dist_instance : Dist stream := λ n s1 s2,
  ∀ i, i ≤ n → nth s1 i = nth s2 i.

(*
  These relations are written [s1 ≡{n}≡ s1] pronounced as
  "s1 and s2 are n-equivalent".

  Alternatively, we could have defined this inductively as follows:
*)
Lemma stream_dist_alt (n : nat) (s1 s2 : stream) : s1 ≡{n}≡ s2 ↔
  head s1 = head s2 ∧
  match n with
  | 0 => True
  | S n => tail s1 ≡{n}≡ tail s2
  end.
Proof.
  split.
  - intros H.
    split.
    { apply (H 0). lia. }
    destruct n.
    + done.
    + intros m Hm.
      apply (H (S m)).
      lia.
  - intros [H1 H2] m Hm.
    destruct m.
    + apply H1.
    + destruct n.
      * lia.
      * apply H2.
        lia.
Qed.

(*
  These relations should satisfy the following laws:

  - [dist_equivalence : ∀ n, Equivalence (dist n)]
    As you would expect: The n-equivalences are equivalence relations.
  - [equiv_dist : ∀ x y, x ≡ y ↔ (∀ n, x ≡{n}≡ y)]
    Intuitively this states that values are equivalent if and only if
    they cannot be distinguished by a program.
  - [dist_lt : ∀ n m x y, x ≡{n}≡ y → m < n → x ≡{m}≡ y]
    Intuitively this states that if x and y cannot be distinguished by
    programs running for n steps, then they cannot be distinguished by
    programs running for less than n steps.
*)

Lemma stream_ofe_mixin : OfeMixin stream.
Proof.
  split.
  - intros s1 s2.
    rewrite stream_equiv_nth.
    split.
    + intros H n i Hi.
      apply H.
    + intros H i.
      by apply (H i).
  - intros n.
    split.
    + intros s i Hi.
      done.
    + intros s1 s2 H i Hi.
      symmetry.
      by apply H.
    + intros s1 s2 s3 H1 H2 i Hi.
      trans (nth s2 i).
      * by apply H1.
      * by apply H2.
  - intros n m s1 s2 H Hm i Hi.
    apply H.
    lia.
Qed.

(*
  We can now package this together into an OFE.
*)
Canonical Structure streamO := Ofe stream stream_ofe_mixin.

End ofe.

(*
  To help with future proofs we will prove that the basic functions
  respect our equivalence. Thereby enabling the rewrite tactic.
*)
Global Instance head_proper : Proper ((≡) ==> (=)) head.
Proof. exact stream_equiv_head. Qed.

Global Instance tail_proper : Proper ((≡) ==> (≡)) tail.
Proof. exact stream_equiv_tail. Qed.

Global Instance nth_proper : Proper ((≡) ==> (=) ==> (=)) nth.
Proof.
  intros s1 s2 H n _ <-.
  by apply stream_equiv_nth.
Qed.

(*
  Some OFEs are complete (called a COFE), meaning all chains have a
  limit. Here a chain [c] is a sequence such that [c n ≡{n}≡ c i] when
  [n ≤ i]. This means that for [stream] the [i]th stream agrees with
  the first [i] values of all future streams. As such the limits [i]th
  value must be the [i]th value of the [i]th stream in the chain.
*)
Global Program Instance stream_cofe : Cofe streamO := {|
  compl c := fun2stream (λ i, nth (c i) i);
|}.
Next Obligation.
  intros n [c Hc] i Hi; simpl.
  rewrite fun2stream_nth.
  specialize (Hc i n Hi i).
  symmetry.
  by apply Hc.
Qed.

(*
  There are two important classes of functions between OFEs called
  [NonExpansive] and [Contractive]. [NonExpansive] functions are
  functions that preserve dist. This is encoded using the setoid
  library as [∀ n, Proper (dist n ==> dist n) f]. [Contractive]
  functions furthermore increase the "precision" one step. Encoded as
  [∀ n, Proper (dist_later n ==> dist n) f].

  [dist_later] is defined differently from what you might have seen
  elsewhere, but it is still equivalent to the usual definition.
  [dist_later n x y := ∀ m, m < n → x ≡{m}≡ y]
*)
Global Instance SCons_contractive x : Contractive (SCons x).
Proof.
  intros n s1 s2 [H] i Hi.
  destruct i as [|j].
  - simpl.
    done.
  - simpl.
    by apply (H j).
Qed.

(*
  All [Contractive] functions are also [NonExpansive], but this fact
  is not registered as an instance to improve type-class instance
  resolution. It is thus necessary to register this fact for your
  functions as well.
*)
Global Instance SCons_ne x : NonExpansive (SCons x).
Proof. apply contractive_ne, _. Qed.

Fixpoint sapp (l : list nat) (s : stream) : stream :=
  match l with
  | [] => s
  | x :: l => SCons x (sapp l s)
  end.

Global Instance sapp_ne (l : list nat) : NonExpansive (sapp l).
Proof.
  intros n s1 s2 H.
  induction l as [|x l IH]; simpl.
  - done.
  - by f_equiv.
Qed.

(*
  Now let's define a stream that simply repeats a list over and over
  again. Intuitively we should be able to define it as follows:
*)
Fail CoFixpoint repeat (l : list nat) : stream :=
  sapp l (repeat l).

(*
  However, this correctly fails. Consider the case in which the list
  is empty. No matter how many times you repeat an empty list, the
  result remains empty. So we will never end up with an infinite
  stream.

  To fix this we can insert a separator in between the repetitions of
  the list:
*)
Fail CoFixpoint repeat_with_sep (l : list nat) (x : nat) : stream :=
  sapp l (SCons x (repeat_with_sep l x)).

(*
  But this still fails with the same error. This is because Coq uses a
  simple syntactic check to validate co-fixpoint definitions.

  To satisfy this check we are forced to syntactically produce at least
  one element of the stream per recursive call, which is violated by
  the call to [sapp]. In practice, this means that we cannot reuse
  most of our existing operations when writing new recursively defined
  streams. We instead have to implement it from scratch as follows:
*)
CoFixpoint repeat_with_sep_helper (l : list nat) (x : nat) (helper : list nat) : stream :=
  match helper with
  | [] => SCons x (repeat_with_sep_helper l x l)
  | y :: helper => SCons y (repeat_with_sep_helper l x helper)
  end.
Definition repeat_with_sep (l : list nat) (x : nat) := 
  repeat_with_sep_helper l x l.

(*
  To be sure that this definition is correct, we can show that it
  still solves the fixpoint equation. To do this we first need to
  show that the helper function does what it is supposed to.
*)
Lemma repeat_with_sep_helper_unfold (l : list nat) (x : nat) (helper : list nat) :
  repeat_with_sep_helper l x helper ≡ sapp helper (SCons x (repeat_with_sep_helper l x l)).
Proof.
  induction helper as [|y helper IH].
  - constructor; simpl.
    + done.
    + done.
  - constructor; simpl.
    + done.
    + done.
Qed.

Lemma repeat_with_sep_unfold (l : list nat) (x : nat) :
  repeat_with_sep l x ≡ sapp l (SCons x (repeat_with_sep l x)).
Proof. apply repeat_with_sep_helper_unfold. Qed.

(*
  This can be non-trivial and requires code duplication, as mentioned
  previously. COFEs offer a way around these restrictions through
  guarded-fixpoints. Let us write the function as before, but with the
  result of a recursive call as the last argument:
*)
Definition repeat_with_sep_pre (l : list nat) (x : nat) (s : stream) :=
  sapp l (SCons x s).

(*
  We can then notice that this function is contractive with respect to
  this recursive argument [s], as [sapp] is [NonExpansive] and [SCons]
  is [Contractive].
*)
Global Instance repeat_with_sep_contractive (l : list nat) (x : nat) : Contractive (repeat_with_sep_pre l x).
Proof. solve_contractive. Qed.

(*
  We can now get a fixpoint, because the [stream] is a [COFE] with an
  inhabitant.
*)
Definition repeat_with_sep_alt (l : list nat) (x : nat) :=
  fixpoint (repeat_with_sep_pre l x).

(*
  And the fixpoint can be unfolded up to equivalence:
*)
Lemma repeat_with_sep_alt_unfold (l : list nat) (x : nat) : 
  repeat_with_sep_alt l x ≡ sapp l (SCons x (repeat_with_sep_alt l x)).
Proof. exact (fixpoint_unfold _). Qed.

(*
  Furthermore, any such fixpoint is unique, so we can prove that our
  two definitions are equivalent.
*)
Lemma repeat_with_sep_alt_correct (l : list nat) (x : nat) :
  repeat_with_sep l x ≡ repeat_with_sep_alt l x.
Proof.
  apply fixpoint_unique.
  apply repeat_with_sep_unfold.
Qed.
