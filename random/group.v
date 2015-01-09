Require Import monoid.
Require Import Coq.Arith.Mult.

Generalizable Variables A o e.

Class group (A : Type) `{S : monoid A o e} (inv : A -> A) : Prop := {
  left_inverse : forall x,
                   o (inv x) x = e
; right_inverse : forall x,
                    o x (inv x) = e
}.