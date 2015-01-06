Require Import List BinInt.
Import ListNotations.

Require Import ZArith.
Open Scope Z_scope.

Open Scope list_scope.

Class semigroup {A : Type} (o : A -> A -> A) : Prop := {
  dot_assoc : forall x y z : A,
                o x (o y z) = o (o x y) z
}.

Instance list_concat_semigroup {A : Type} : semigroup (@app A).
Proof.
  intros. apply Build_semigroup. intros.
  induction x.
  reflexivity.
  simpl.
  f_equal.
  induction y.
  auto.
  rewrite IHx.
  reflexivity.
Qed.