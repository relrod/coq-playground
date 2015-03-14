Require Import Coq.Strings.String.
Require Import Ascii.

Local Open Scope char.
Local Open Scope string.

Inductive regex_rule : Type :=
| Epsilon
| Literal : Ascii.ascii -> regex_rule
| Or : regex_rule -> regex_rule -> regex_rule
| Concat : regex_rule -> regex_rule -> regex_rule
| Star : regex_rule -> regex_rule.

Definition ε := Epsilon.

Fixpoint show_regex r : string :=
  match r with
    | Epsilon => "ε"
    | Literal c => String c ""
    | Or a b => "(" ++ show_regex a ++ "|" ++ show_regex b ++ ")"
    | Concat a b => "(" ++ show_regex a ++ show_regex b ++ ")"
    | Star a => "(" ++ show_regex a ++ ")"
  end.

Eval compute in show_regex (Concat (Concat (Concat (Literal "a") (Star (Literal "a"))) (Star (Literal "b"))) (Or (Literal "a") (Literal "c"))).