Theory aggregateEvaluatedLayout
Ancestors
  exprSimHyps exprSimHypsDefs vyperTypeSystem vyperValue valueEncoding
  vyperTypeArgFits compileEnv allocLimits list

Theorem arg_fits_evaluated_memory_size:
  (!t u. arg_type_fits t u ==>
    !tenv tv tu. evaluate_type tenv t = SOME tv /\
      evaluate_type tenv u = SOME tu ==>
      type_memory_size tv <= type_memory_size tu) /\
  (!ts us. arg_types_fit ts us ==>
    !tenv tvs tus. OPT_MMAP (evaluate_type tenv) ts = SOME tvs /\
      OPT_MMAP (evaluate_type tenv) us = SOME tus ==>
      type_memory_size_list tvs <= type_memory_size_list tus)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[arg_type_fits_def, evaluate_type_def, AllCaseEqs(),
       type_memory_size_def] >> rpt strip_tac >> gvs[] >>
  simp[type_memory_size_def]
  >- (irule word_size_monotone >> simp[])
  >- (irule word_size_monotone >> simp[])
  >- (irule arithmeticTheory.LESS_MONO_MULT2 >> simp[] >>
      first_x_assum irule >> metis_tac[])
  >- (first_x_assum irule >> metis_tac[])
  >- (gvs[evaluate_types_OPT_MMAP] >> first_x_assum irule >> metis_tac[]) >>
  metis_tac[arithmeticTheory.LESS_EQ_LESS_EQ_MONO]
QED

Theorem arg_type_fits_word_type:
  !t u. arg_type_fits t u ==> (is_word_type t <=> is_word_type u)
Proof
  ho_match_mp_tac (cj 1 arg_type_fits_ind) >>
  simp[arg_type_fits_def, is_word_type_def] >>
  qexists_tac `\ts us. T` >> simp[]
QED

Theorem body_post_type_allocation_bound:
  expr_body_pre ce cx env e es ==>
  !tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `expr_sim_inv ce cx env es /\ well_typed_expr env e` by
    fs[expr_body_pre_def] >>
  conj_tac
  >- (irule expr_sim_inv_memory_size >> metis_tac[]) >>
  drule_all post_value_type_widens >>
  simp[type_widens_to_def] >> strip_tac >>
  drule expr_body_pre_type_evaluates >> simp[optionTheory.IS_SOME_EXISTS] >>
  disch_then (qx_choose_then `dtv` assume_tac) >>
  `~is_word_type (expr_type e)` by metis_tac[arg_type_fits_word_type] >>
  `type_alloc_ok ce (expr_type e)` by
    metis_tac[expr_body_pre_def, alloc_limits_expr_type_alloc_ok] >>
  `type_memory_bytes ce (expr_type e) < 2 ** 64` by
    fs[type_alloc_ok_def] >>
  `type_memory_bytes ce (expr_type e) = type_memory_size dtv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_size tvt <= type_memory_size dtv` by
    (gvs[] >> metis_tac[cj 1 arg_fits_evaluated_memory_size]) >> gvs[]
QED
