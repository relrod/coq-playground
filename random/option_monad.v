Fixpoint option_map {A B : Type} (f : A -> B) (o : option A): option B :=
  match o with
    | None => None
    | Some x => Some (f x)
  end.

Definition identity {A : Type} (x : A) := x.

Theorem functor_identity : forall {A : Type} (x : option A), option_map identity x = id x.
Proof.
  intros.
  induction x.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Fixpoint option_flatmap {A B : Type} (o : option A) (f : A -> option B): option B :=
  match o with
    | None => None
    | Some x => f x
  end.

Notation "f >>= x" := (option_flatmap f x) (at level 50).

Definition option_return {A : Type} (o : A) := Some o.

Theorem monad_left_id : forall {A B : Type} (x : A) (f : A -> option B),
                          option_flatmap (option_return x) f = f x.
Proof.
  intros.
  reflexivity.
Qed.

Theorem monad_right_id : forall {A: Type} (x : option A),
                           x >>= option_return = x.
Proof.
  intros.
  destruct x.
  reflexivity.
  reflexivity.
Qed.

Theorem monad_assoc : forall {A B C : Type} (x : option A) (f : A -> option B) (g : B -> option C),
                        (x >>= f) >>= g = x >>= fun x => f x >>= g.
Proof.
  intros.
  destruct x.
  reflexivity.
  reflexivity.
Qed.