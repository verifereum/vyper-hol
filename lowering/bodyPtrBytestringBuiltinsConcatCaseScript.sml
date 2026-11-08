(*
 * Concat case of bodyPtrBytestringBuiltins' bytestring_builtin_expr_ptr_ok.
 *
 * TOP-LEVEL:
 *   concat_body_expr_ptr_ok
 *)
Theory bodyPtrBytestringBuiltinsConcatCase
Ancestors
  bodyPtrPreds vyperContext vyperAST

(* ADMITTED leaf: the pointer-safety case for concat is not proved yet. *)
Theorem concat_body_expr_ptr_ok:
  !cx ty n es.
    (builtin_args_length_ok (Concat n) (LENGTH es) ==>
      body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty (Concat n) es)
Proof
  cheat
QED
