Require Import magma.
Require Import ZArith.
Require Import Coq.Arith.Mult.

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

Instance nat_mult_semigroup : semigroup nat.
Proof.
  split.
  intros.
  induction x.
  reflexivity.
  simpl.
  rewrite IHx.
  rewrite mult_plus_distr_r.
  reflexivity.
Qed.

Instance z_add_semigroup : semigroup Z.
Proof.
  split.
  apply Zplus_assoc.
Qed.