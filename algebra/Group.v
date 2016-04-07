(* This is just something I started playing around with. *)
(* The proofs are probably very inefficient and bad. *)
(* Next steps are to be more pedantically accurate in the hierarchy (e.g. *)
(* semigroup, magma, etc.) and also begin formalizing subgroups. *)
(* If I keep having fun, I might start on formalizing some category theory *)
(* stuff as I go, too. *)

Require Export Monoid.

Class Group {G} `(Monoid G) (inverse : G -> G) :=
  { inverse_left : forall x : G, dot (inverse x) x = zero;
    inverse_right : forall x : G, dot x (inverse x) = zero
  }.

(* Useful for 1.1.24(1) below. *)
Lemma unique_unop `{Group} :
  forall x y z,
    dot x y = z -> x = dot z (inverse y).
  intros.
  rewrite <- H3.
  rewrite <- dot_assoc.
  rewrite inverse_right.
  rewrite zero_right.
  trivial.
Qed.

(* These are from Theorem 1.1.24 in Papantonopoulou. *)
(* 1.1.24(1) *)
Theorem identity_unique `{Group} :
  forall e x, dot e x = x -> e = zero.
Proof.
  intros.
  rewrite (unique_unop e x x).
  rewrite inverse_right.
  reflexivity.
  assumption.
Qed.

(* 1.1.24(2) *)
Theorem inverse_unique `{Group} :
  forall a b,
    a <+> b = zero -> a = inverse b /\ b = inverse a.
Proof.
  intros.
  assert ((a <+> b) <+> inverse b = zero <+> inverse b).
  rewrite H3.
  reflexivity.
  assert (inverse a <+> (a <+> b) = inverse a <+> zero).
  rewrite H3.
  reflexivity.
  rewrite <- dot_assoc in H4.
  rewrite inverse_right in H4.
  rewrite zero_right in H4.
  rewrite zero_left in H4.
  rewrite dot_assoc in H5.
  rewrite inverse_left in H5.
  rewrite zero_left in H5.
  rewrite zero_right in H5.
  split.
  assumption.
  assumption.
Qed.

(* 1.1.24(3) *)
Theorem inv_inv `{Group} :
  forall x, inverse (inverse x) = x.
Proof.
  intros.
  transitivity (dot (inverse (inverse x)) (dot (inverse x) x)).
  rewrite inverse_left.
  rewrite zero_right.
  reflexivity.
  rewrite dot_assoc.
  rewrite inverse_left.
  rewrite zero_left.
  reflexivity.
Qed.

(* 1.1.24(4) *)
Theorem inverse_over_product `{Group} :
  forall a b, inverse (a <+> b) = inverse b <+> inverse a.
Proof.
  intros.
  assert (a <+> b <+> (inverse b <+> inverse a) = zero) as Q.
  assert ((a <+> b) <+> (inverse b <+> inverse a)
          = a <+> (b <+> inverse b) <+> inverse a) as Q
      by (repeat rewrite dot_assoc; reflexivity).
  rewrite Q.
  rewrite inverse_right.
  assert (a <+> zero = a).
  rewrite zero_right.
  reflexivity.
  rewrite H3.
  rewrite inverse_right.
  reflexivity.
  destruct (inverse_unique _ _ Q).
  symmetry in H4.
  assumption.
Qed.

(* TODO: 1.1.24(5) - Cancellation Laws *)
Theorem cancel_left `{Group} :
  forall a b y,
    y <+> a = y <+> b -> a = b.
Proof.
  admit. (* TODO!! *)
Admitted.

Theorem cancel_right `{Group} :
  forall a b y,
    a <+> y = b <+> y -> a = b.
Proof.
  admit. (* TODO!! *)
Admitted.