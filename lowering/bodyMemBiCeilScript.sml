(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: ceil (S1: exprSimBuiltins' compile_ceil_case). *)
Theory bodyMemBiCeil
Ancestors
  bodyMemoryPreds exprSimSource exprSimDefs vyperTypeSystem
  vyperAST exprSimHypsDefs loweringShapeProps

Theorem ceil_body_pre[local]:
  expr_body_pre cenv cx env (Builtin ann Ceil args) es ==>
  ?e. args = [e] /\ ann = BaseT (IntT 256) /\
      expr_type e = BaseT DecimalT /\ expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `LENGTH args = 1 /\ ann = BaseT (IntT 256) /\
   HD (MAP expr_type args) = BaseT DecimalT` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `args` >- gvs[] >>
  Cases_on `t` >> gvs[] >>
  irule expr_body_pre_builtin_arg >>
  conj_tac >- gvs[expr_body_pre_def] >>
  qexistsl_tac [`BaseT (IntT 256)`, `[h]`, `Ceil`, `es`] >>
  gvs[expr_body_pre_def]
QED

Theorem ceil_body_operand_mem[local]:
  (builtin_args_length_ok Ceil (LENGTH [e]) ==> body_exprs_mem_ok cx [e]) ==>
  body_expr_mem_ok cx e
Proof
  simp[vyperContextTheory.builtin_args_length_ok_def, body_exprs_mem_ok_def]
QED

Theorem body_builtin_ceil_mem:
  !cx ty es.
    (builtin_args_length_ok Ceil (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty Ceil es)
Proof
  cheat
QED
