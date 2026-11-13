(*
 * Slice case of bodyPtrBytestringBuiltins' bytestring_builtin_expr_ptr_ok.
 *
 * TOP-LEVEL:
 *   slice_body_expr_ptr_ok
 *)
Theory bodyPtrBytestringBuiltinsSliceCase
Ancestors
  bodyPtrPreds vyperContext vyperAST vyperInterpreter

(* Code-source slices are handled separately by body_builtin_case_ptr. *)
Theorem slice_body_expr_ptr_ok:
  !cx ty n es.
    code_slice_source (Slice n) es = NONE /\
    (builtin_args_length_ok (Slice n) (LENGTH es) ==>
      body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty (Slice n) es)
Proof
  cheat
QED
