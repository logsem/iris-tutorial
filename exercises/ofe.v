From iris.algebra Require Export ofe.

(**
  In this file, we will go into the details of OFEs, non-expansiveness,
  and, contractiveness. We will do this using streams of natural
  numbers. Streams are not important to the understanding of Iris.
  However, they form good intuition about the usefulness of OFEs.

  We will look at stream over natural numbers. These are infinite
  sequences with [head] being the first value, and [tail] being the
  rest of the stream. We define streams as a coinductive type. You
  should be able to follow this file without extensive knowledge of
  coinduction.
*)

CoInductive stream := SCons {
  head : nat;
  tail : stream;
}.
Add Printing Constructor stream.

(**
  Co-inductive values are allowed to be infinitely deep, meaning
  we can construct an infinite stream of zeroes as follows:
*)

CoFixpoint zeros := SCons 0 zeros.

(**
  [CoFixpoints] allows us to build coinductive values, in the same way
  that [Fixpoint] allows us to use inductive types recursively.

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
  (* exercise *)
Admitted.

Section ofe.

(*
  We will say that two streams are equivalent when the elements are
  equal. We can specify this using [nth].
*)
Local Instance stream_equiv_instance : Equiv stream := λ s1 s2,
  ∀ n, nth s1 n = nth s2 n.

(*
  Now for the OFE structure, we introduce the concept of approximate
  equivalence using the typeclass [Dist].

  This typeclass defines an family of equivalence relations written
  [[x ≡{n}≡ y]] where [n] is the precision. In our case this will
  decide how many of the elements of the stream we look at.
*)
Local Instance stream_dist_instance : Dist stream := λ n s1 s2,
  ∀ i, i ≤ n → nth s1 i = nth s2 i.

(*
  These relations should satisfy the following laws:

  - [dist_equivalence : ∀ n, Equivalence (dist n)]
    As you would expect: The n-equivalences are equivalence relations.
  - [equiv_dist : ∀ x y, x ≡ y ↔ (∀ n, x ≡{n}≡ y)]
    This states that, as the "precision" of the approximation
    approaches infinity, then the equivalences approach true
    equivalence.
  - [dist_lt : ∀ n m x y, x ≡{n}≡ y → m < n → x ≡{m}≡ y]
    This means reducing the precision can only make more things
    approximately equivalent.
*)
Lemma stream_ofe_mixin : OfeMixin stream.
Proof.
  split.
  (* exercise *)
Admitted.

(*
  We can now package this together into an OFE.
*)
Canonical Structure streamO := Ofe stream stream_ofe_mixin.

End ofe.

(*
  We can now ask the question of whether we can build values from a
  sequence of better and better approximations. To this end we use the
  concept of a chain. Here chains are sequences such that all elements
  after the n'th element are n-equivalent. An OFE is complete if all
  chains approach a value. This is also called a COFE for complete
  OFE.

  In the case of streams, we can find the completion by considering
  the n'th number in the n'th stream, as all streams after this point
  agrees on this value after this point.
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

(*
  Furthermore, all [NonExpansive] functions are also [Proper]. Meaning
  we only need to prove the strongest of these three properties and
  then use it for the rest.
*)
Global Instance SCons_proper x : Proper ((≡) ==> (≡)) (SCons x).
Proof. apply ne_proper, _. Qed.

(*
  We don't have any such nice properties for [tail] and [nth]. So we
  prove that they preserve the equivalence directly.
*)
Global Instance tail_proper : Proper ((≡) ==> (≡)) tail.
Proof.
  intros s1 s2 H n.
  exact (H (S n)).
Qed.

Global Instance nth_proper : Proper ((≡) ==> (=) ==> (=)) nth.
Proof.
  by intros s1 s2 H n _ <-.
Qed.

(*
  If we look at [tail] we notice that it isn't [NonExpansive] for the
  same reason that [SCons] is contractive. However, it is
  anti-contractive in that it decreases the "precision" by one step.
  These functions are rarely used as they aren't [NonExpansive] and
  therefore don't behave as well as we'd like. However, they can be
  used when constructing new functions by balancing anti-contractive
  functions with [Contractive] functions.
*)
Global Instance tail_anti_contractive : ∀ n, Proper (dist n ==> dist_later n) tail.
Proof.
  intros n s1 s2 H.
  constructor.
  intros m Hm i Hi.
  apply (H (S i)).
  lia.
Qed.
  

(*
  With the setup out of the way, we can now begin defining operations
  on streams. The first such operation will be appending a list to the
  front of a stream.
*)
Fixpoint sapp (l : list nat) (s : stream) : stream :=
  match l with
  | [] => s
  | x :: l => SCons x (sapp l s)
  end.

(*
  This operation is [NonExpansive] when we fix the list we wish to
  prepend. Furthermore, we can prove this without unfolding the
  definition of [dist], by using what we have proved so far.
*)
Global Instance sapp_ne (l : list nat) : NonExpansive (sapp l).
Proof.
  (* exercise *)
Admitted.

Global Instance sapp_proper (l : list nat) : Proper ((≡) ==> (≡)) (sapp l).
Proof. apply ne_proper, _. Qed.

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
  - intros [|n]; simpl.
    + done.
    + done.
  - intros [|n]; simpl.
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
  To get a fixpoint for such a function we need three things
  - The type we wish to produce an element of (stream) must have a
    COFE structure, which we defined earlier.
  - The function we wish to find a fixpoint for must be contractive,
    which we just proved.
  - Finally, the COFE must be inhabited, meaning there is an element
    of that type. We can use [zeroes] for this, as the choice of
    inhabitant doesn't matter.
*)
Global Instance stream_inhabited : Inhabited stream := populate zeros.

(*
  With all conditions met, we can now define the fixpoint as follows:
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

(*
  A common operation one could consider on streams is mapping. This
  luckily conforms to the rules of co-fixpoints, but we will also
  define it using guarded recursion.
*)
CoFixpoint stream_map (f : nat → nat) (s : stream) : stream :=
  SCons (f (head s)) (stream_map f (tail s)).

(*
  Notice that our recursive call takes different parameters. So we
  can't just build this as a fixpoint on streams. Instead, we need to
  build a fixpoint on [stream → stream]. However, this is not equipped
  with a canonical OFE structure. Instead, we need to write
  [stream -d> streamO]. Here "d" is short for discrete, meaning we
  don't consider any OFE structure on the domain. As such, we are
  allowed to change the parameter arbitrarily on recursive calls.
*)
Definition stream_map_pre (f : nat → nat) (map : stream -d> streamO) : stream -d> streamO :=
  λ s : stream, SCons (f (head s)) (map (tail s)).

Global Instance stream_map_pre_contractive (f : nat → nat) : Contractive (stream_map_pre f).
Proof. solve_contractive. Qed.

(*
  In this way, we can use guarded-fixpoints as an alternative to
  co-fixpoints. Allowing us to use existing functions in the
  fixpoint definitions.
*)
Definition stream_map_alt (f : nat → nat) := fixpoint (stream_map_pre f).

(*
  Rather than simply restating the fixpoint unfolding lemma directly,
  we will fully apply the function. 
*)
Lemma stream_map_alt_unfold (f : nat → nat) (s : stream) :
  stream_map_alt f s ≡ SCons (f (head s)) (stream_map_alt f (tail s)).
Proof. exact (fixpoint_unfold (stream_map_pre f) s). Qed.

Lemma stream_map_alt_correct (f : nat → nat) (s : stream) : stream_map f s ≡ stream_map_alt f s.
Proof.
  apply (fixpoint_unique (stream_map_pre f)).
  clear s; intros s.
  intros [|n]; simpl.
  + done.
  + done.
Qed.

Lemma stream_map_nth (f : nat → nat) (s : stream) (n : nat) :
  nth (stream_map f s) n = f (nth s n).
Proof.
  (* exercise *)
Admitted.

Global Instance stream_map_ne (f : nat → nat) : NonExpansive (stream_map f).
Proof.
  (* exercise *)
Admitted.

(*
  If we now wanted to create a stream of all the powers of 2, we would
  intuitively want something like this:
*)
Fail CoFixpoint power2 : stream :=
  SCons 1 (stream_map (λ n, n * 2) power2).

(*
  However, this again fails the syntactic check, as we are modifying
  the tail of the stream.

  To fix this we could instead define a stream starting with a number
  [n] doubling [n] at every step.
*)
CoFixpoint power2_helper (n : nat) : stream :=
  SCons n (power2_helper (n * 2)).
Definition power2 : stream :=
  power2_helper 1.

(*
  To know that these definitions are equivalent, we must again prove
  that [power2_helper] and [power2] satisfy respective fixpoint
  equations.
*)
Lemma power2_helper_unfold (n : nat) :
  power2_helper n ≡ SCons n (stream_map (λ n, n * 2) (power2_helper n)).
Proof.
  (* exercise *)
Admitted.

Lemma power2_unfold :
  power2 ≡ SCons 1 (stream_map (λ n, n * 2) power2).
Proof. apply power2_helper_unfold. Qed.

(*
  Now, just like before, we can instead define the function for which
  we wish to find a fixpoint:
*)
Definition power2_pre (s : stream) : stream :=
  SCons 1 (stream_map (λ n, n * 2) s).

(*
  This is again contractive in [s], because [SCons] is [Contractive]
  and [stream_map] is [NonExpansive].
*)
Global Instance power2_pre_contractive : Contractive power2_pre.
Proof. solve_contractive. Qed.

(* So we can now get a fixpoint, just as before *)
Definition power2_alt := fixpoint power2_pre.

Lemma power2_alt_unfold : power2_alt ≡ power2_pre power2_alt.
Proof. apply fixpoint_unfold. Qed.

(*
  Like before, we know that this fixpoint is unique, so it must be
  equivalent to the other definition.
*)
Lemma power2_alt_correct : power2 ≡ power2_alt.
Proof.
  apply fixpoint_unique.
  apply power2_unfold.
Qed.

(**
  [iProp] also has a COFE structure, but it is not a co-inductive
  type. This means that even though we can't use [CoFixpoint] to build
  propositions recursively, we can use [fixpoint]. Importantly, all
  the connectives of the logic are [NonExpansive]. To then use guarded
  fixpoints, we need a [Contractive] function like [SCons]. And for
  [iProp] this is later [▷ P]. We have already run into two
  connectives defined using the guarded-fixpoint, namely the weakest-
  precondition [WP], and invariants [inv]. This is why we can remove
  laters from premises when taking a step in the program, as this
  corresponds to unfolding the fixpoint, thus revealing a later.
*)
