Require Import ZArith.
Require Import String.
Require Import Basics.
Require Import Program.Combinators.

Require Import Algae.Group.
Require Import Algae.Monoid.
Require Import Algae.Semigroup.

(* And here we play with the machinery because it's fun! *)

(* This is useless since N can't form a group. *)
Instance magma_nat : Magma nat plus.
Proof. reflexivity. Qed.

Instance semigroup_nat : Semigroup magma_nat.
Proof.
  split.
  intros.
  apply Plus.plus_assoc.
Qed.

Instance monoid_nat : Monoid semigroup_nat 0.
Proof.
  split.
  intros.
  apply Plus.plus_0_l.
  apply Plus.plus_0_r.
Qed.

Require Export Ascii.
Open Scope string_scope.


(* This is useless for us too - The free monoid over strings + string concat. *)
(* I couldn't find a built-in exported theorem for associativity of append. *)
Instance magma_str_concat : Magma string append.
Proof. reflexivity. Qed.

Lemma string_assoc :
  (forall a x y, (String a x) <+> y = String a (x <+> y)).
Proof. reflexivity. Qed.

Instance semigroup_str_concat : Semigroup magma_str_concat.
Proof.
  split.
  intros.
  induction x.
  reflexivity.
  rewrite string_assoc.
  rewrite IHx.
  reflexivity.
Qed.

Instance monoid_str_concat : Monoid semigroup_str_concat EmptyString.
Proof.
  split.
  intros.
  trivial.
  intros.
  induction x.
  trivial.
  rewrite string_assoc.
  rewrite IHx.
  reflexivity.
Qed.


(* Functions form a monoid under composition. *)
Variable A : Type.
Instance magma_functions  : Magma (A -> A) compose.
Proof. reflexivity. Qed.

Instance semigroup_functions : Semigroup magma_functions.
Proof.
  split.
  reflexivity.
Qed.

Definition id x : A := x.

Instance monoid_functions : Monoid semigroup_functions id.
Proof.
  split.
  intros.
  reflexivity.
  reflexivity.
Qed.

(* They only form a group if they are all isomorphisms in the respective *)
(* category (bijections in Set). So we can't say much here. *)


Instance magma_ints_add : Magma Z Z.add.
Proof. reflexivity. Qed.

Instance semigroup_ints_add : Semigroup magma_ints_add.
Proof.
  split.
  intros.
  rewrite Z.add_assoc.
  reflexivity.
Qed.

Instance monoid_ints_add : Monoid semigroup_ints_add Z0.
Proof.
  split.
  apply Z.add_0_l.
  apply Z.add_0_r.
Qed.

Instance group_ints : Group monoid_ints_add Z.opp.
Proof.
  split.
  intros.
  rewrite Z.add_comm.
  rewrite Z.add_opp_diag_r.
  reflexivity.
  intros.
  rewrite Z.add_comm.
  rewrite Z.add_opp_diag_l.
  reflexivity.
Qed.

Require Export Ascii.
Open Scope string_scope.
Eval compute in "aa" <+> "bb".