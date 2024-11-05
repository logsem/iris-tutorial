(** * Section *)
Variant foo := bar. (* comments *)

(** ** Subsection *)
(** Documentations. *)
Example baz : forall f : foo, f = bar.
Proof.
  intros [].
  reflexivity.
Qed.
