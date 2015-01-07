Definition identity {A : Type} (x : A) := x.

Class functor (f : Type -> Type) :=
  { fmap : forall {a b}, (a -> b) -> f a -> f b

  ; identity_law : forall a (x : f a), fmap identity x = identity x
  }.

Fixpoint option_map {A B : Type} (f : A -> B) (o : option A): option B :=
  match o with
    | None => None
    | Some x => Some (f x)
  end.

Instance option_functor : functor option :=
  { fmap := @option_map
  }.
intros.
destruct x.
reflexivity.
reflexivity.
Qed.