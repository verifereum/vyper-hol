(*
 * Concat case of bodyPtrBytestringBuiltins' bytestring_builtin_expr_ptr_ok.
 *
 * TOP-LEVEL:
 *   concat_body_expr_ptr_ok
 *)
Theory bodyPtrBytestringBuiltinsConcatCase
Ancestors
  bodyPtrPreds vyperContext vyperAST bodyPtrBytestringBuiltinsConcatResult
  bodyPtrDefs exprPtrUnwrap
Theorem concat_body_expr_ptr_ok:
  !cx ty n es.
    (builtin_args_length_ok (Concat n) (LENGTH es) ==>
      body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty (Concat n) es)
Proof
  rpt gen_tac >> disch_tac >> simp[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty' (Builtin ty (Concat n) es) es'`
    suffices_by metis_tac[expr_sim_ptr_of_vv] >>
  irule concat_result_vv_sim_ptr >> simp[] >> metis_tac[]
QED
