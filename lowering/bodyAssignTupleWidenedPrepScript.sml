Theory bodyAssignTupleWidenedPrep
Ancestors
  bodyAssignTupleOther exprSimIfExpCompat exprSimHyps aggregateEvaluatedLayout
  vyperTypeSystem compileEnv valueEncoding list exprSimSource exprSimHypsDefs
  vyperTypeEnv vyperAST vyperTypeValues exprLowering vyperTypeInvariants stmtLowering
  vyperTypeArgFits

Theorem tuple_widened_physical_layout:
  expr_body_pre cenv cx env e es /\ expr_type e = TupleT tys /\
  lowered_value_type cenv e <> expr_type e ==>
  ?ltys ltvs. lowered_value_type cenv e = TupleT ltys /\
    arg_types_fit ltys tys /\
    evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
    ~is_memory_view e
Proof
  rpt strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent cenv.ce_struct_fields env.type_defs` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  drule ifexp_lowered_type_classify >>
  disch_then (qspec_then `cenv` mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  simp[is_bytestring_type_def] >> strip_tac >> gvs[] >>
  drule ifexp_body_pre_intcall_physical >> strip_tac >>
  gvs[expr_type_def] >>
  Cases_on `lowered_value_type cenv (Call (TupleT tys) (IntCall fid) args drv)` >>
  gvs[arg_type_fits_def] >>
  drule evaluate_type_TupleT_cases >> strip_tac >>
  gvs[is_memory_view_def]
QED

Theorem tuple_widened_component_bound:
  expr_body_pre cenv cx env e es /\ expr_type e = TupleT tys /\
  arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) ==>
  !i. i < LENGTH tys ==>
    type_memory_size (EL i ltvs) + 64 < dimword (:256)
Proof
  rpt strip_tac >>
  `type_memory_size (TupleTV tvs) < 2 ** 64` by
    (drule expr_body_pre_copy_ok >>
     disch_then (qspec_then `TupleTV tvs` mp_tac) >>
     simp[is_word_type_def]) >>
  `type_memory_size (TupleTV ltvs) <= type_memory_size (TupleTV tvs)` by
    (irule (cj 1 arg_fits_evaluated_memory_size) >>
     goal_assum (drule_at Any) >> qexists_tac `TupleT tys` >>
     simp[arg_type_fits_def]) >>
  `LENGTH ltvs = LENGTH tys` by
    (imp_res_tac evaluate_type_TupleT_cases >> gvs[] >>
     metis_tac[LIST_REL_LENGTH, arg_types_fit_LENGTH]) >>
  `!vs j. j < LENGTH vs ==>
     type_memory_size (EL j vs) <= type_memory_size (TupleTV vs)` by
    (Induct >> simp[type_memory_size_def] >>
     Cases_on `j` >> simp[type_memory_size_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[type_memory_size_def]) >>
  first_x_assum (qspec_then `ltvs` mp_tac) >>
  disch_then (qspec_then `i` mp_tac) >>
  gvs[wordsTheory.dimword_def]
QED
