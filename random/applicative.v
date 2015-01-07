Require Import Coq.Program.Basics.

Definition identity {A : Type} (x : A) := x.

Class applicative (f : Type -> Type) :=
  { pure : forall {a}, a -> f a
  ; ap : forall {a b}, f (a -> b) -> f a -> f b

  ; identity_law : forall a (x : f a), ap (pure identity) x = identity x
  ; composition_law : forall a b (x : f (a -> b)) (y : f (a -> a)) (z : f a),
                        ap (ap (ap (pure compose) x) y) z = ap x (ap y z)
  ; homomorphism_law : forall a b (fn : a -> b) (x : a),
                         ap (pure fn) (pure x) = pure (fn x)
  ; interchange_law : forall a b (x : a) (u : f (a -> b)),
                        ap u (pure x) = ap (pure (fun f => f x)) u
  }.

Fixpoint option_ap {A B : Type} (f : option (A -> B)) (o : option A): option B :=
  match o with
    | None => None
    | Some x => match f with
                  | Some f' => Some (f' x)
                  | None => None
                end
  end.

Instance option_applicative : applicative option :=
  { ap := @option_ap
  ; pure := @Some
  }.
intros.
destruct x.
reflexivity.
reflexivity.
destruct x.
destruct y.
destruct z.
reflexivity.
reflexivity.
destruct z.
reflexivity.
reflexivity.
destruct z.
destruct y.
reflexivity.
reflexivity.
destruct y.
reflexivity.
reflexivity.
reflexivity.
destruct u.
reflexivity.
reflexivity.
Qed.