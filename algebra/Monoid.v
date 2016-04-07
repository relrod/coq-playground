Require Export Semigroup.

Set Primitive Projections.

Class Monoid {A} `(Semigroup A) (zero : A) :=
  { zero_left : forall x, dot zero x = x;
    zero_right : forall x, dot x zero = x;
  }.