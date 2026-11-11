Theory bodyIntCallFamStmtMutationBytesMetadata
Ancestors
  bodyIntCallJointContract exprSimIfExpCompat memoryLocalRhsProps
  exprSimSource exprSimHypsDefs exprSimDefs bodySim
  supportedExprForms supportedExprs vyperTypeSystem vyperAST exprLowering compileEnv
Libs
  monadsyntax

Theorem intcall_bytes_lowered_class:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
  supported_expr tops e /\ is_bytestring_type (expr_type e) ==>
  is_bytestring_type (lowered_value_type ce e) /\
  type_memory_bytes ce (lowered_value_type ce e) <=
    type_memory_bytes ce (expr_type e)
Proof
  strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule_all ifexp_lowered_type_classify >> strip_tac
  >- gvs[]
  >- metis_tac[lowered_value_type_memory_bound] >>
  `supported_program tops /\
   ce.ce_func_return_type = build_func_return_type tops /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  qpat_x_assum `supported_expr _ _` mp_tac >>
  simp[supportedExprsTheory.supported_expr_def, supported_pure_expr_def,
       supported_effect_expr_def] >> strip_tac >>
  Cases_on `drv` >> gvs[supported_effect_expr_def, optionTheory.IS_SOME_EXISTS] >>
  PairCases_on `x` >>
  `?sig. FLOOKUP env.fn_sigs fid = SOME sig` by
    (Cases_on `fid` >>
     gvs[well_typed_expr_def, optionTheory.IS_SOME_EXISTS]) >>
  `expr_sim_inv ce cx env es` by gvs[expr_body_pre_def] >>
  drule_all supported_internal_signature_return >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  Cases_on `fid` >>
  simp[well_typed_expr_def, expr_type_def] >> strip_tac >>
  gvs[lowered_value_type_def, expr_type_def, type_widens_to_def] >>
  Cases_on `ty` >> gvs[is_bytestring_type_def] >>
  Cases_on `b` >> gvs[is_bytestring_type_def] >>
  Cases_on `sig.ret_ty` >> gvs[arg_type_fits_def] >>
  rename1 `arg_type_fits (BaseT bt) _` >>
  Cases_on `bt` >>
  gvs[arg_type_fits_def, is_bytestring_type_def,
      compileEnvTheory.type_memory_bytes_def] >>
  simp[arithmeticTheory.DIV_LE_MONOTONE] >>
  rename1 `arg_type_fits (BaseT (BytesT src)) (BaseT (BytesT dst))` >>
  Cases_on `dst` >> gvs[is_bytestring_type_def] >>
  Cases_on `src` >>
  gvs[is_bytestring_type_def, arg_type_fits_def, type_memory_bytes_def,
      arithmeticTheory.DIV_LE_MONOTONE]
QED

Theorem intcall_bytes_lowered_metadata:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
  supported_expr tops e /\ is_bytestring_type (expr_type e) /\
  type_memory_bytes ce (expr_type e) + 64 < dimword (:256) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, ee) ==>
  is_bytestring_type (lowered_value_type ce e) /\
  ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
       value_has_type tv v /\
       type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
       type_memory_size tv + 64 < dimword (:256)
Proof
  strip_tac >>
  drule_all intcall_bytes_lowered_class >> strip_tac >>
  `value_runtime_typed env (lowered_value_type ce e) v` by
    (irule memory_rhs_read_lowered_typed >>
     fs[body_inv_def] >> metis_tac[]) >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  simp[] >> goal_assum drule >> simp[]
QED
