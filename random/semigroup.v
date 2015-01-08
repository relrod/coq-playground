Require Import magma.

Generalizable Variables A o.

Class semigroup (A : Type) `{M : magma A o} : Prop := {
  dot_assoc : forall x y z,
                o x (o y z) = o (o x y) z
}.

Instance list_concat_semigroup {A : Type} : semigroup (list A).
Proof.
  split.
  intros.
  induction x.
  reflexivity.
  simpl.
  rewrite IHx.
  reflexivity.
Qed.