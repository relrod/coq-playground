Require Import semigroup.
Require Import ZArith.
Require Import Coq.Arith.Mult.

Generalizable Variables A o.

Class monoid (A : Type) `{S : semigroup A o} (e : A) : Prop := {
  left_unit : forall x,
                o e x = x
; right_unit : forall x,
                 o x e = x
}.

Instance list_concat_monoid {A : Type} : monoid (list A) nil.
Proof.
  split.
  intros.
  reflexivity.
  intros.
  induction x.
  reflexivity.
  simpl.
  rewrite IHx.
  reflexivity.
Qed.

Instance nat_mult_monoid : monoid nat 1%nat.
Proof.
  split.
  intros.
  rewrite mult_1_l.
  reflexivity.
  intros.
  rewrite mult_1_r.
  reflexivity.
Qed.

Instance z_add_monoid : monoid Z 0%Z.
Proof.
  split.
  intros.
  reflexivity.
  intros.
  induction x.
  reflexivity.
  simpl.
  reflexivity.
  reflexivity.
Qed.