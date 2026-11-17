(* String[N] to bool, as Vyper's to_bool: a source of at most 32 bytes is
   accepted whatever its value, and the result is false only for an empty or
   all-zero payload. *)
Theory vyperStringBoolConvertTest
Ancestors
  list vyperAST vyperValue vyperValueOperation vyperTypeSystem
Libs
  blastLib

Theorem string_bool_valid_bound:
  valid_conversion (BaseT (StringT n)) (BaseT BoolT) <=> n <= 32
Proof
  simp[valid_conversion_def]
QED

Theorem string_bool_bounds_eval:
  valid_conversion (BaseT (StringT 32)) (BaseT BoolT) /\
  valid_conversion (BaseT (StringT 0)) (BaseT BoolT) /\
  ~valid_conversion (BaseT (StringT 33)) (BaseT BoolT)
Proof
  EVAL_TAC
QED

Theorem string_bool_values_eval:
  evaluate_convert tenv (StringV "") (BaseT BoolT) = INL (BoolV F) /\
  evaluate_convert tenv (StringV "\000\000") (BaseT BoolT) = INL (BoolV F) /\
  evaluate_convert tenv (StringV "a") (BaseT BoolT) = INL (BoolV T) /\
  evaluate_convert tenv (StringV "\000b") (BaseT BoolT) = INL (BoolV T)
Proof
  EVAL_TAC >> blastLib.BBLAST_TAC
QED
