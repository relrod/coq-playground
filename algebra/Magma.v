Set Primitive Projections.

Class Magma (A : Type) (dot : A -> A -> A) :=
  { dot := dot }.

Infix "<+>" := dot (at level 50, left associativity).