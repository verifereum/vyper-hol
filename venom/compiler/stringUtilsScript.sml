(*
 * String Helpers for Compiler Passes
 *
 * Utilities for parsing/constructing variable and label names.
 *)

Theory stringUtils
Ancestors
  list string ASCIInumbers

Definition is_digit_def:
  is_digit c <=> #"0" <= c /\ c <= #"9"
End

Definition digit_val_def:
  digit_val c = ORD c - ORD #"0"
End

Definition parse_nat_chars_def:
  parse_nat_chars cs = FOLDL (λacc c. acc * 10 + digit_val c) 0 cs
End

Definition all_digits_def:
  all_digits cs <=> EVERY is_digit cs
End

Definition string_to_num_opt_def:
  string_to_num_opt s =
    let cs = EXPLODE s in
    if all_digits cs then SOME (parse_nat_chars cs) else NONE
End

Definition strip_percent_def:
  strip_percent s =
    case EXPLODE s of
      [] => NONE
    | (#"%"::rest) => SOME (IMPLODE rest)
    | _ => NONE
End

Definition take_while_def:
  take_while P [] = [] /\
  take_while P (x::xs) = if P x then x::take_while P xs else []
End

Definition drop_while_def:
  drop_while P [] = [] /\
  drop_while P (x::xs) = if P x then drop_while P xs else x::xs
End

Definition var_id_of_name_def:
  var_id_of_name name =
    case strip_percent name of
      NONE => NONE
    | SOME rest => string_to_num_opt rest
End

Definition label_id_of_name_def:
  label_id_of_name name =
    let cs = EXPLODE name in
    let prefix = take_while is_digit cs in
    if prefix = [] then NONE else SOME (parse_nat_chars prefix)
End

Definition mk_var_name_def:
  mk_var_name n = STRCAT "%" (num_to_dec_string n)
End

Definition mk_label_name_def:
  mk_label_name n suffix =
    if suffix = "" then num_to_dec_string n
    else STRCAT (STRCAT (num_to_dec_string n) "_") suffix
End

val _ = export_theory();
