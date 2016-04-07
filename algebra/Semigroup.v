Require Export Magma.

Set Primitive Projections.

Class Semigroup {A} `(Magma A) :=
  { dot_assoc : forall x y z : A,
      dot x (dot y z) = dot (dot x y) z
  }.