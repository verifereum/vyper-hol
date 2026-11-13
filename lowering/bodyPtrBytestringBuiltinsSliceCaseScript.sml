(*
 * Slice case of bodyPtrBytestringBuiltins' bytestring_builtin_expr_ptr_ok.
 *
 * TOP-LEVEL:
 *   slice_body_expr_ptr_ok
 *)
Theory bodyPtrBytestringBuiltinsSliceCase
Ancestors
  bodyPtrPreds vyperContext vyperAST

(* ADMITTED leaf: the pointer-safety case for slice, including its
   slice(x.code) branch, is not proved yet. *)
Theorem slice_body_expr_ptr_ok:
  !cx ty n es.
    (builtin_args_length_ok (Slice n) (LENGTH es) ==>
      body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty (Slice n) es)
Proof
  cheat
QED
