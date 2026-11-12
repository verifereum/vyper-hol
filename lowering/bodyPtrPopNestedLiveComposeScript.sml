Theory bodyPtrPopNestedLiveCompose
Ancestors
  bodyPtrPopNestedLiveContinuation
  bodyPtrPopNestedLiveSource bodyPtrPopNestedLiveHandoff bodyPtrPopNestedLiveEntry
  bodyPtrPopNestedLiveSuffixFrame bodyPtrPopNestedLiveSuffix
  bodyPtrPopNestedLivePositivePost bodyPtrPopTargetDefs
  exprSimPopNestedBase exprSimPopNestedLocalSource exprSimPopNestedLocalHandoff
  exprSimPopNestedLocalRun exprSimPopNestedLocalProps exprSimPopNestedLocalMemory
  gasSummaryComposePtr fragGasPathPtr gasOutcome gasExemptCert
  bodyPtrDefs bodySim exprSimHypsDefs stmtLoweringMono exprLoweringProps
  emitHelperProps exprLowering compileEnv exprSimDefs exprSimProps
  vyperEvalExprPreservesScopesDom vyperInterpreter vyperState vyperAST
  venomState finite_map vyperTypeSystem fragExec stmtSimProps loweringPosts valueEncoding

Theorem pop_nested_live_compose:
  pop_target_frag_ptr d ctx PG func cenv cx env bt es /\
  (!x. bt <> NameTarget x) /\ target_root bt = NameTarget id /\
  local_target_live cx id bt /\ expr_body_pre cenv cx env (Pop ann bt) es ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  strip_tac >>
  `?n. type_place_target env bt = SOME (Type (ArrayT ann (Dynamic n)))` by
    fs[expr_body_pre_def, well_typed_expr_def] >>
  pop_assum strip_assume_tac >>
  rewrite_tac[expr_vv_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >> PairCases_on `q` >>
  qmatch_asmsub_rename_tac `compile_get_target_ptr _ _ _ _ = ((hdr,loc,pt),sm)` >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rewrite_tac[nested_pop_compile_eq] >> asm_rewrite_tac[] >>
  simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac
    `compile_dynarray_pop hdr ws esz F cenv.ce_imm_alloca lc sm` >>
  Cases_on `compile_dynarray_pop hdr ws esz F cenv.ce_imm_alloca lc sm` >>
  simp[] >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by
    metis_tac[ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `ci_mono sm r` by metis_tac[ci_mono_compile_dynarray_pop, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm r func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    metis_tac[nested_pop_target_admissible] >>
  qpat_x_assum `pop_target_frag_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[pop_target_frag_ptr_def] >> disch_then drule_all >>
  `eval_expr cx (Pop ann bt) = vyperState$bind (eval_target_place cx bt) (pop_place cx)` by
    simp[FUN_EQ_THM, Once evaluate_def, vyperStateTheory.bind_def] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  rewrite_tac[gas_outcome_ptr_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >> qexists_tac `marks`
  >- (disj1_tac >> suspend "summary") >>
  disj2_tac >> rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  first_assum (irule_at Any o MATCH_MP gas_exempt_cert_error_place)
QED

Resume pop_nested_live_compose[summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  disch_then (qx_choosel_then [`tres`, `tend`, `G`, `tn`, `tr0`] strip_assume_tac) >>
  gvs[] >- suspend "normal" >>
  Cases_on `tres` >> gvs[expr_exit_def] >>
  rename1 `expr_exit (INR exc) tr0` >>
  qexistsl_tac [`INR exc`, `tend`, `G`, `tn`, `tr0`] >> simp[] >> conj_tac
  >- (irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
  metis_tac[expr_exit_INR_type]
QED

Resume pop_nested_live_compose[normal]:
  `compile_expr cenv ty (Pop ann bt) sa =
    (LocatedValue ann (mk_ptr q lc),r)` by
    (rewrite_tac[nested_pop_compile_eq] >> asm_rewrite_tac[] >>
     simp[Abbr `lc`, Abbr `ws`, Abbr `esz`]) >>
  drule_all pop_normal_target_continuation >> strip_tac >>
  qexistsl_tac [`res`, `fin`, `H`, `tf`, `rr`] >>
  simp[post_value_type_def, expr_type_def] >> metis_tac[]
QED
Finalise pop_nested_live_compose
