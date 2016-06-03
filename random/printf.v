Require Import Ascii String Zdiv.

Open Scope string.

Inductive format :=
| fmt_int : format -> format
| fmt_string : format -> format
| fmt_other : ascii -> format -> format
| fmt_end : format.

Fixpoint format_str s :=
  match s with
  | String "%" (String "d" s') => fmt_int (format_str s')
  | String "%" (String "s" s') => fmt_string (format_str s')
  | String c s' => fmt_other c (format_str s')
  | EmptyString => fmt_end
  end.

Fixpoint gen_format_type f :=
  match f with
  | fmt_int f' => Z -> gen_format_type f'
  | fmt_string f' => string -> gen_format_type f'
  | fmt_other _ f' => gen_format_type f'
  | fmt_end => string
  end.

(* I can't find a nicer way to convert Z -> string :( *)
Definition digit_to_string n : string :=
  match n with
  | 0%Z => "0"
  | 1%Z => "1"
  | 2%Z => "2"
  | 3%Z => "3"
  | 4%Z => "4"
  | 5%Z => "5"
  | 6%Z => "6"
  | 7%Z => "7"
  | 8%Z => "8"
  | 9%Z => "9"
  | _ => ""
  end.

Fixpoint z_to_string' n z acc : string :=
  match n with
  | 0 => acc
  | S n' =>
    let acc' := digit_to_string (Zmod z 10) ++ acc
    in match (Zdiv z 10) with
       | Z0 => acc'
       | z' => z_to_string' n' z' acc'
       end
  end.

Definition z_to_string z :=
  if Z.geb z 0
  then z_to_string' (Z.to_nat z) z ""
  else let z' := Zabs z
       in "-" ++ z_to_string' (Z.to_nat z') z' "".
(* end of laborious Z -> string stuff *)

Fixpoint to_fn f s : gen_format_type f :=
  match f with
  | fmt_int f' => fun i => to_fn f' (s ++ z_to_string i)
  | fmt_string f' => fun i => to_fn f' (s ++ i)
  | fmt_other a f' => to_fn f' (s ++ String a EmptyString)
  | fmt_end => s
  end.

Definition printf s := to_fn (format_str s) "".

Eval compute in printf "%s %s %d" "hi" "there" 123%Z.