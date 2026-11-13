(*
 * Expression simulation: extract32(b, start).
 *
 * compile_extract32_case, the case lemma exprSimBuiltins re-exports for compile_expr_sim
 * (exprSimMain): from exprs_case of the operands, expr_vv_case of the
 * builtin.
 *)

Theory exprSimExtract32
Ancestors
  exprSimExtract32Ready exprSimExtract32Source exprSimHypsDefs vyperAST
  vyperTypeSystem

Theorem compile_extract32_case:
  !nocalls ctx func cenv cx ann t args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Extract32 t args)
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_vv_case_def] >> rpt gen_tac >> strip_tac >>
  drule extract32_body_pre_shape >> strip_tac >> gvs[] >>
  `well_typed_expr env (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off])` by
    metis_tac[expr_body_pre_def] >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[well_typed_expr_def, well_typed_type_builtin_args_def] >>
  strip_tac >>
  irule compile_extract32_ready_sim >>
  metis_tac[]
QED
