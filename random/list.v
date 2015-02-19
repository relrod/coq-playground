Module foo.

Inductive list (a : Type) : Type :=
  | nil : list a
  | cons : a -> list a -> list a.

Infix "::" := cons (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition head {a : Type} (default : a) (l : list a) : a :=
  match l with
    | nil => default
    | cons h t => h
  end.

Definition tail {a : Type} (default : list a) (l : list a) : list a :=
  match l with
    | nil => default
    | cons h t => t
  end.

Fixpoint append {a : Type} (l1 l2 : list a) : list a :=
  match l1 with
    | nil => l2
    | cons h t => cons a h (append t l2)
  end.

Notation "xs ++ ys" := (append xs ys) (at level 60, right associativity).

Theorem app_is_assoc : forall (a : Type)
                              (xs ys zs : list a),
                         (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
Proof.
  intros.
  induction xs.
  simpl.
  reflexivity.
  simpl.
  rewrite IHxs.
  reflexivity.
Qed.

Fixpoint length {a : Type} (l : list a) : nat :=
  match l with
    | nil => 0
    | cons h t => 1 + length t
  end.

Theorem app_length : forall (a : Type)
                            (xs ys : list a),
                       length xs + length ys = length (xs ++ ys).
Proof.
  intros.
  induction xs.
  simpl.
  reflexivity.
  simpl.
  rewrite IHxs.
  reflexivity.
Qed.