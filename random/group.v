Require Import monoid.
Require Import ZArith.
Require Import Coq.Arith.Mult.

Generalizable Variables A o e.

Class group (A : Type) `{S : monoid A o e} (inv : A -> A) : Prop := {
  left_inverse : forall x,
                   o (inv x) x = e
; right_inverse : forall x,
                    o x (inv x) = e
}.

Instance z_add_group : group Z Z.opp.
Proof.
  split.
  intros.
  rewrite Z.add_opp_l.
  rewrite Zminus_diag.
  reflexivity.
  intros.
  rewrite Z.add_opp_r.
  rewrite Zminus_diag.
  reflexivity.
Qed.