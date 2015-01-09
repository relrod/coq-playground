Require Import monoid.
Require Import Coq.Arith.Mult.

Generalizable Variables A o.

Class group (A : Type) `{S : monoid A o} (e : A) (inv : A -> A) : Prop := {
  left_inverse : forall x,
                   o (inv x) x = e
; right_inverse : forall x,
                    o x (inv x) = e
}.