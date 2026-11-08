Theory bodyPtrTypeBuiltinsEmptyWord
Ancestors
  bodyPtrTypeBuiltinsBoundWords exprSimAggregates gasContext vyperState
  exprSimHypsDefs vyperTypeSystem exprLowering exprSimHyps compileEnv
  valueEncoding
Libs monadsyntax

Theorem empty_explicit_bind:
  !cx ann t args es res ee.
    vyperState$bind (eval_expr cx (TypeBuiltin ann Empty t args)) (read_result cx) es = (res,ee) /\
    expr_res_ok res ==>
    ee = es /\ args = [] /\
    ?tv. evaluate_type (get_tenv cx) t = SOME tv /\ res = INL (default_value tv)
Proof
  mp_tac eval_expr_empty >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem empty_source_gas:
  !cx ann typ args es.
    gas_admissible
      (vyperState$bind (eval_expr cx (TypeBuiltin ann Empty typ args)) (read_result cx))
      expr_res_ok es ==>
    ?tv. evaluate_type (get_tenv cx) typ = SOME tv /\ args = [] /\
      !gs. vyperState$bind (eval_expr cx (TypeBuiltin ann Empty typ args)) (read_result cx)
        (es with gas_obs := gs) = (INL (default_value tv),es with gas_obs := gs)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `vyperState$bind (eval_expr cx (TypeBuiltin ann Empty typ args)) (read_result cx) es` >>
  rename1 `_ = (res,ee)` >>
  `expr_res_ok res` by
    (qpat_assum `gas_admissible _ _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[] >> metis_tac[]) >>
  drule_all empty_explicit_bind >> strip_tac >>
  qpat_x_assum `args = []` SUBST_ALL_TAC >>
  qexists_tac `tv` >> simp[] >> gen_tac >>
  Cases_on `vyperState$bind (eval_expr cx (TypeBuiltin ann Empty typ [])) (read_result cx)
    (es with gas_obs := gs)` >>
  rename1 `_ (es with gas_obs := gs) = (r2,ee2)` >>
  `expr_res_ok r2` by (drule_all gas_admissible_result >> simp[]) >>
  drule_all empty_explicit_bind >> strip_tac >> gvs[]
QED

Theorem empty_word_typed_literal:
  !cenv cx env ann typ args es tv ty sa op sb.
    is_word_type typ /\
    expr_sim_pre cenv cx env (TypeBuiltin ann Empty typ args) es /\
    evaluate_type (get_tenv cx) typ = SOME tv /\ args = [] /\
    lower_value compile_expr cenv ty (TypeBuiltin ann Empty typ args) sa = (op,sb) ==>
    sb = sa /\ is_word_type ann /\ op = Lit 0w /\
      !tv'. evaluate_type (get_tenv cx) ann = SOME tv' ==>
        typed_val_to_w256 tv' (default_value tv) = 0w
Proof
  rpt gen_tac >> strip_tac >>
  `ann = typ` by
    gvs[expr_sim_pre_def, well_typed_expr_def, type_builtin_result_ok_def] >>
  gvs[lower_value_def, compile_expr_type_builtin_dispatch, comp_bind_def] >>
  gvs[Once compile_expr_def, unwrap_value_def, comp_return_def] >>
  metis_tac[typed_val_to_w256_default_word]
QED
