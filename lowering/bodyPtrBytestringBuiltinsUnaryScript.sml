Theory bodyPtrBytestringBuiltinsUnary
Ancestors
  bodyPtrBytestringBuiltinsInterfaces exprSimSource

Theorem unary_builtin_operand_sim_ptr:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann bt [e]) es /\
  body_exprs_ptr_ok cx [e] /\
  expr_type e <> BaseT (BytesT (Dynamic 24576)) ==>
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_typed_arg >>
     fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     qexistsl_tac [`ann`, `[e]`, `bt`, `es`] >> simp[]) >>
  drule body_exprs_ptr_head >>
  simp[bodyPtrPredsTheory.body_expr_ptr_ok_def] >>
  metis_tac[]
QED
