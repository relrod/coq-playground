Definition identity {A : Type} (x : A) := x.

Class monad (m : Type -> Type) :=
  { bind : forall {a b}, m a -> (a -> m b) -> m b
  ; ret  : forall {a}, a -> m a

  ; law_1 : forall a b (f : a -> m b) (x : a), bind (ret x) f = f x
  ; law_2 : forall a (x : m a), bind x ret = x
  ; law_3 : forall a b c (x : m a) (f : a -> m b) (g : b -> m c),
              bind (bind x f) g = bind x (fun x => bind (f x) g)
  }.

Notation "f >>= x" := (bind f x) (at level 50).

Definition join {m} `{monad m} {a} (x : m (m a)) : m a :=
  x >>= identity.

Fixpoint option_flatmap {A B : Type} (o : option A) (f : A -> option B): option B :=
  match o with
    | None => None
    | Some x => f x
  end.

Definition option_return {A : Type} (o : A) := Some o.

Instance option_monad : monad option :=
  {
      bind := @option_flatmap
    ; ret := @Some
  }.
constructor.
intros.
destruct x.
reflexivity.
reflexivity.
intros.
destruct x.
reflexivity.
reflexivity.
Qed.