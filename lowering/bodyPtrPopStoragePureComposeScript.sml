Theory bodyPtrPopStoragePureCompose
Ancestors
  bodyPtrPopStoragePureSummary bodyPtrPopTargetDefs bodyPtrPreds bodySim
  exprSimHypsDefs exprSimPopNestedBase targetPlaceLive vyperPureExpr
  vyperInterpreter vyperState vyperAST gasSummaryComposePtr gasExemptCert
  stmtLoweringMono exprLoweringProps compileEnv loweringStateRelDefs loweringPosts
  bodyPtrDefs vyperTypeSystem fragExec fragGasPathPtr exprSimDefs stmtSimProps exprSimPopStorage
  vyperStoragePlaceProvenance fragGasPath gasSummary fragGasMode
  vyperStorageLayoutSafety vyperLookupStorage vyperStorageBackend appendStorageSourcePtr
  exprSimSource bodyPtrPopStoragePureFrame exprOperandVar context

Theorem pop_storage_pure_compose:
  !tops ctx cenv cx env ann bt ty es d PG func src id ts vd.
    body_inv tops ctx cenv cx /\
    pop_target_frag_ptr d ctx PG func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME vd /\
    EVERY pure_expr (target_indices bt) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env (Pop ann bt)` by
    fs[expr_body_pre_def] >>
  `?n. type_place_target env bt = SOME (Type (ArrayT ann (Dynamic n)))` by
    fs[well_typed_expr_def] >>
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
  qpat_x_assum `pop_target_frag_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [pop_target_frag_ptr_def]) >>
  disch_then drule_all >>
  `eval_expr cx (Pop ann bt) = vyperState$bind (eval_target_place cx bt) (pop_place cx)` by
    simp[FUN_EQ_THM, Once evaluate_def, vyperStateTheory.bind_def] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  rewrite_tac[gas_outcome_ptr_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks`
  >- (disj1_tac >> suspend "summary") >>
  disj2_tac >> rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  first_assum (irule_at Any o MATCH_MP gas_exempt_cert_error_place)
QED

Resume pop_storage_pure_compose[summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  disch_then (qx_choosel_then [`tres`, `tend`, `G1`, `tn1`, `tr0`] strip_assume_tac) >>
  gvs[]
  >- suspend "normal" >>
  Cases_on `tres` >> gvs[expr_exit_def] >>
  qexistsl [`INR y`, `tend`, `G1`, `tn1`, `tr0`] >>
  conj_tac >- (irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
  metis_tac[expr_exit_INR_type]
QED

Resume pop_storage_pure_compose[normal]:
  pure_rewrite_tac[GSYM gas_summary_ptr_at_marked] >>
  `eval_target_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL p, tend with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_ptr_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all nested_pop_eval_target_pure_state >> strip_tac >>
  `gas_explicit marks s0.vs_gas_readings = [] /\
   tend with gas_obs := [] = es with gas_obs := []` by
    fs[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_x_assum `_ with gas_obs := [] = _ with gas_obs := gas_explicit _ _` kall_tac >>
  gvs[] >>
  drule_all nested_pop_eval_target_storage_class >> strip_tac >> gvs[] >>
  drule nested_pop_storage_target_metadata >> strip_tac >> gvs[] >>
  drule_all pop_storage_element_size >>
  disch_then (qspec_then `tr` assume_tac) >>
  fs[GSYM slot_loc_def] >>
  `ws = 1` by
    (Cases_on `tr` >> fs[Abbr `ws`, Abbr `lc`, slot_loc_def, word_scale_def]) >>
  qunabbrev_tac `lc` >> qunabbrev_tac `ws` >> gvs[Abbr `esz`] >>
  suspend "suffix"
QED

Resume pop_storage_pure_compose[suffix]:
  `expr_body_pre cenv cx env (Pop ann bt) (es with gas_obs := [])` by
    metis_tac[expr_body_pre_gas_obs] >>
  `storage_layout_safe cx /\ contract_storage_well_formed cx (es with gas_obs := [])` by
    (qpat_x_assum `expr_body_pre _ _ _ _ (_ with gas_obs := [])` mp_tac >>
     pure_rewrite_tac[expr_body_pre_def, expr_sim_inv_def] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `storage_place_region cx (StoragePlace tr slot (ArrayTV tv' (Dynamic n)))` by
    metis_tac[eval_target_place_region] >>
  `get_storage_backend cx tr (es with gas_obs := []) =
    (INL (get_storage cx (es with gas_obs := []) tr),es with gas_obs := [])` by
    simp[get_storage_backend_eq] >>
  drule_all nested_pop_eval_target_slots >> strip_tac >>
  drule_all nested_pop_eval_target_live_post >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[compiler_ci_mono_not_fresh] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[compiler_ci_mono_not_fresh] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_ptr_exec, gas_marked_path_exec, gas_path_normal, gas_marked_exec_def] >>
  suspend "apply"
QED

Resume pop_storage_pure_compose[apply]:
  `op_prov G1 hdr = NONE /\ op_taint tn1 hdr = {}` by
    fs[target_ptr_ok_def] >>
  drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`) pop_storage_live_summary >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`r`, `q`, `bt`, `PG`] mp_tac) >>
  impl_tac >- (simp[GSYM slot_loc_def] >> metis_tac[]) >>
  pure_rewrite_tac[gas_summary_ptr_at_marked] >>
  disch_then (qx_choosel_then [`pres`, `pend`, `G2`, `tn2`, `pr`]
    (CONJUNCTS_THEN assume_tac)) >>
  qexistsl [`pres`, `pend`, `G2`, `tn2`, `pr`] >>
  conj_tac
  >- (qpat_x_assum `tend with gas_obs := [] = _` mp_tac >>
      qpat_x_assum `gas_marked_exec_ptr _ _ _ (eval_target_place _ _) _ _ _ _ _ _ _` mp_tac >>
      qpat_x_assum `gas_marked_exec_ptr _ _ _ (pop_place _ _) _ _ _ _ _ _ _` mp_tac >>
      rpt (first_x_assum kall_tac) >> rpt strip_tac >>
      metis_tac[gas_marked_exec_ptr_bind_normal, listTheory.APPEND_NIL]) >>
  gvs[] >- suspend "post" >> simp[]
QED

Resume pop_storage_pure_compose[post]:
  `ghost_kept cenv es sa G0 tn0 s0 G2 tn2` by
    (irule target_post_ghost_kept_compose >>
     qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ghost_kept _ _ sa _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ghost_kept _ _ sm _ _ _ _ _` (irule_at Any) >>
     simp[] >> fs[stmt_state_rel_def, state_rel_def]) >>
  Cases_on `tr` >> gvs[slot_loc_def, mk_ptr_def, expr_type_def]

QED
Finalise pop_storage_pure_compose
