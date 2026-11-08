(* Bounded source fixture diagnostic; no general callee invariant. *)
Theory bodyPtrMakeArrayEmptyReturnProbe
Ancestors
  supportedProgram supportedExprs compileVyper
Libs finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset

val U = ``BaseT (UintT 256)``
val A = ``ArrayT ^U (Dynamic 1)``
val W = ``TupleT [BaseT (BytesT (Dynamic 64)); ^A]``
val N = ``TupleT [BaseT (BytesT (Dynamic 32)); ^A]``
val emptyW = ``Builtin ^W (MakeArray NONE (Fixed 2))
  [Literal (BaseT (BytesT (Dynamic 64))) (BytesL []);
   Builtin ^A (MakeArray (SOME ^U) (Dynamic 1)) []]``
val tops = ``[
  FunctionDecl Internal Pure F F "empty_wide" [] ([] : expr list) ^W
    [Return (SOME ^emptyW)];
  FunctionDecl External Pure F F "read_empty" [] ([] : expr list) ^N
    [Return (SOME (Call ^N (IntCall (NONE, "empty_wide")) [] NONE))]]``

Theorem empty_return_declaration_lookup:
  IS_SOME (supported_function_decl ^tops (NONE,"empty_wide") Internal)
Proof
  EVAL_TAC
QED

Theorem empty_return_program_rejected:
  ~supported_program ^tops
Proof
  EVAL_TAC
QED

(* The failing gate is already the INTERNAL declaration header: memory
   tuples containing a dynamic array are not supported_value_type. *)
Theorem empty_return_internal_type_rejected:
  ~supported_function_return ^tops Internal ^W /\
  ~supported_declaration_header ^tops (HD ^tops)
Proof
  EVAL_TAC
QED

Theorem empty_return_tuple_value_rejected:
  ~supported_value_type ^tops ^W /\
  ~EVERY supported_scalar_type
     [BaseT (BytesT (Dynamic 64)); ^A]
Proof
  EVAL_TAC
QED
