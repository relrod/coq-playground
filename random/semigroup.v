Require Import List.
Import ListNotations.

Open Scope list_scope.

Inductive semigroup (A : Type) (o : A -> A -> A) : Prop :=
| semigroup_c : (forall (x y z : A),
                  o x (o y z) = o (o x y) z) -> semigroup A o.

Theorem list_concat_semigroup : forall A, semigroup (list A) (@app A).
Proof.
  intros. apply semigroup_c. intros.
  induction x.
  reflexivity.
  simpl.
  f_equal.
  induction y.
  auto.
  rewrite IHx.
  reflexivity.
Qed.