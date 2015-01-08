Require Import semigroup.

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