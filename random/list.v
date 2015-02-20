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

Fixpoint map {a b : Type} (f : a -> b) (l : list a) : list b :=
  match l with
    | nil => nil b
    | cons h t => cons b (f h) (map f t)
  end.

Definition id' {a} x : a := x.

Theorem map_id_id_map : forall (a : Type)
                               (xs : list a),
                          map id' xs = xs.
Proof.
  intros.
  induction xs.
  simpl.
  reflexivity.
  simpl.
  rewrite IHxs.
  unfold id'.
  reflexivity.
Qed.

Definition compose {a b c} (f : a -> b) (g : b -> c) : a -> c :=
  fun x => g (f x).

Theorem map_f_g_compose : forall (a b c : Type)
                                 (f : a -> b)
                                 (g : b -> c)
                                 (xs : list a),
                            map (compose f g) xs = compose (map f) (map g) xs.
Proof.
  intros.
  induction xs.
  simpl.
  reflexivity.
  simpl.
  rewrite IHxs.
  reflexivity.
Qed.

Fixpoint fold_right {a b : Type} (f : a -> b -> b) (b' : b) (la : list a) : b:=
  match la with
    | nil => b'
    | cons h t => fold_right f (f h b') t
  end.

Definition flatten {a : Type} (xs : list (list a)) : list a :=
  fold_right append (nil a) xs.

Definition flat_map {a b : Type} (f : a -> list b) (l : list a) : list b :=
  flatten (map f l).