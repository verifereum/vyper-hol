Theory bodyPtrPopTargetSimMapping
Ancestors
  bodyPtrPopTargetSimArrayConstructor bodyPtrPopTargetSimMapContinuation
  bodyPtrPopTargetSimArrayCompose bodyPtrPopTargetSimSubscriptCuts
  bodyPtrPopTargetSimPost bodyPtrPopTargetSimAttribute
  fragGasPathPtr fragGasSeqPtr fragExec pair freshWrites
  exprLoweringProps exprSimHypsDefs exprSimHyps vyperTyping vyperTypeSystem
  gasContext gasExemptCert gasSummaryComposePtr targetPlaceSimCasesBase
  exprLowering emitHelperProps stmtLoweringMono compileEnv loweringPosts
  bodyPtrPopTargetDefs targetPlaceSimDefs targetPlaceSim exprSimSource exprSimDefs
  vyperInterpreter vyperState bodySimStmtCases exprSimProps wordOperandsPtr
  exprSimMapKey vyperValue exprOperandVar stmtSimAugAssignPlace
  bodyPtrPopTargetSimIndexFrame bodyPtrPopTargetSimSourceCut bodyPtrPopTargetSimMapTail
  vyperTypeExprSoundness vyperTypeInvariants bodyPtrDefs
  vyperEvalExprPreservesScopesDom exprSimWordArgs

Theorem target_mapping_sim_ptr:
  body_inv tops ctx cenv cx /\
  body_base_target_ptr_ok cx (SubscriptTarget bt e) /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME (HashMapT kt leaf) /\
  target_sim_ptr d ctx PG func cenv cx env bt es ==>
  target_sim_ptr d ctx PG func cenv cx env (SubscriptTarget bt e) es
Proof
  strip_tac >> simp[target_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
  simp[Once well_typed_expr_def] >> strip_tac >> gvs[] >>
  suspend "base"
QED

Resume target_mapping_sim_ptr[base]:
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  rename1 `compile_get_target_ptr _ _ bt sa = (rb,sm)` >>
  `fn_has_code sa sm func /\ cs_extends sm sb` by
    (mp_tac (cj 1 compile_expr_ci_mono) >> strip_tac >>
     drule_all target_subscript_base_code_ptr >> simp[]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    metis_tac[target_subscript_base_admissible_ptr] >>
  qpat_x_assum `target_sim_ptr _ _ _ _ _ _ _ bt _`
    (mp_tac o REWRITE_RULE [target_sim_ptr_def]) >>
  disch_then (qspecl_then [`HashMapT kt leaf`, `sa`, `sm`, `rb`,
                         `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- suspend "base_summary" >>
  suspend "base_exempt"
QED

Resume target_mapping_sim_ptr[base_summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >> gvs[]
  >~ [`exit_result r`]
  >- (qexists_tac `marks` >> disj1_tac >>
      simp[Once evaluate_def] >>
      Cases_on `res` >> gvs[expr_exit_def] >>
      irule gas_summary_ptr_at_bind_exception >> simp[] >> metis_tac[]) >>
  drule_all target_subscript_index_ready_ptr >>
  disch_then (qspecl_then [`expr_type e`, `d`] strip_assume_tac) >>
  suspend "index"
QED

Resume target_mapping_sim_ptr[index]:
  `SND (SND rb) = SOME (MapPT kt leaf)` by
    fs[target_post_def, value_type_place_def] >>
  PairCases_on `rb` >> gvs[] >>
  drule_all target_map_compile_parts_ptr >> strip_tac >> gvs[] >>
  suspend "index_run"
QED

Resume target_mapping_sim_ptr[index_run]:
  `ci_mono sa sm` by metis_tac[ci_mono_compile_get_target_ptr, SND] >>
  `ci_mono sm sn` by metis_tac[compile_expr_ci_mono, ci_mono_lower_value_cfn, SND] >>
  `ci_mono sn sp` by
    (Cases_on `is_bytestring_type kt` >> gvs[]
     >- (qspecl_then [`key`, `F`, `sn`] mp_tac ci_mono_compile_keccak256_key >> simp[]) >>
     simp[ci_mono_def, cs_extends_refl]) >>
  `ci_mono sp sb` by metis_tac[ci_mono_compile_mapping_subscript, SND] >>
  `fn_has_code sm sn func /\ fn_has_code sn sb func /\ fn_has_code sp sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_ptr_def, gas_path_ptr_ok_not_halted] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sm`, `sn`, `key`, `t`, `G`, `tn`] mp_tac) >>
  (impl_tac >-
    (fs[target_post_def, ci_mono_def] >> metis_tac[not_fresh_at_mono])) >>
  strip_tac >> suspend "index_outcome"
QED

Resume target_mapping_sim_ptr[index_outcome]:
  rewrite_tac[GSYM gas_outcome_ptr_def] >> simp[Once evaluate_def] >>
  irule gas_outcome_ptr_bind_normal >>
  qexistsl_tac [`G`, `marks`, `es_end`, `t`, `tn`, `pv`] >>
  conj_tac
  >- (rpt strip_tac >> BETA_TAC >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`es_end`, `t`, `pv`] >> fs[]) >>
  reverse conj_tac >- simp[] >>
  BETA_TAC >> once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
  >- suspend "index_summary" >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks'` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf'`, `finish'`] >>
  drule gas_exempt_cert_error_value >>
  disch_then (qspec_then
    `\v. ignore_bind (extend_place cx pv (ValueSubscript v)) (return ())` mp_tac) >>
  simp[ignore_bind_def, vyperStateTheory.bind_assoc]
QED

Resume target_mapping_sim_ptr[index_summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >> gvs[]
  >~ [`exit_result r`]
  >- (simp[gas_outcome_ptr_def] >> qexists_tac `marks'` >> disj1_tac >>
      Cases_on `res` >> gvs[expr_exit_def] >>
      irule gas_summary_ptr_at_bind_exception >> simp[] >>
      qexistsl_tac [`G'`, `y`, `es_end'`, `r`, `tn'`] >>
      fs[oneline expr_exit_def]) >>
  irule gas_outcome_ptr_bind_normal >>
  qexistsl_tac [`G'`, `marks'`, `es_end'`, `t'`, `tn'`, `v`] >>
  conj_tac
  >- (rpt strip_tac >> BETA_TAC >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`es_end'`, `t'`, `v`] >> fs[]) >>
  reverse conj_tac >- simp[] >> BETA_TAC >>
  suspend "mapping_suffix"
QED

Resume target_mapping_sim_ptr[mapping_suffix]:
  `vt = leaf /\ expr_type e = kt /\ hashmap_key_type kt` by
    fs[subscript_vtype_def, AllCaseEqs()] >> gvs[] >>
  qabbrev_tac `em = es_end with gas_obs := gas_explicit marks' t.vs_gas_readings` >>
  qabbrev_tac `ef = es_end' with gas_obs := []` >>
  `eval_base_place cx bt
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ em.gas_obs) =
    (INL pv,em)` by
    (fs[gas_marked_exec_ptr_def] >>
     qpat_x_assum `!tail. eval_base_place _ _ _ = _`
       (qspec_then `em.gas_obs` mp_tac) >> simp[Abbr `em`]) >>
  `bind (eval_expr cx e) (read_result cx) em = (INL v,ef)` by
    (fs[gas_marked_exec_ptr_def] >>
     qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[Abbr `em`, Abbr `ef`]) >>
  `expr_sim_inv cenv cx env em` by simp[Abbr `em`] >>
  `expr_body_pre cenv cx env e em` by
    (fs[target_pre_def, target_indices_pre_def] >>
     first_x_assum irule >> metis_tac[]) >>
  `?itv. evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\
         value_has_type itv v` by
    (fs[vyperStateTheory.bind_def] >>
     drule_all (SRULE [vyperStateTheory.bind_def] expr_body_pre_eval) >>
     disch_then (CONJUNCTS_THEN2 kall_tac (qspec_then `v` mp_tac)) >>
     simp[value_runtime_typed_def] >> rpt strip_tac >>
     `env.type_defs = get_tenv cx` by
       (qpat_x_assum `expr_sim_inv cenv cx env em` mp_tac >>
        simp[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]) >>
     metis_tac[]) >>
  suspend "mapping_frame"
QED

Resume target_mapping_sim_ptr[mapping_frame]:
  `?tr base_slot. pv = HashMapRef tr base_slot (expr_type e) leaf` by
    (qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[target_post_def] >> strip_tac >>
     Cases_on `pv` >> gvs[place_ptr_rel_def] >>
     Cases_on `p` >> gvs[place_ptr_rel_def]) >> gvs[] >>
  `!l. rb0 <> Label l` by
    (Cases_on `bt`
     >- fs[Once well_typed_expr_def, AllCaseEqs()]
     >- (qpat_assum `compile_get_target_ptr _ _ (TopLevelNameTarget _) _ = _`
           (mp_then Any mp_tac target_toplevel_compiled_not_label_ptr) >>
         simp[target_root_def])
     >- (qpat_assum `compile_get_target_ptr _ _ (SubscriptTarget _ _) sa = ((rb0,_,_),sm)`
           (mp_then Any mp_tac aug_place_target_ptr_not_label) >> simp[]) >>
     qpat_assum `compile_get_target_ptr _ _ (AttributeTarget _ _) _ = _`
       (mp_then Any mp_tac aug_place_target_ptr_not_label) >> simp[]) >>
  `!x. rb0 = Var x ==> not_fresh_at sm x` by fs[target_post_def] >>
  `op_taint tn' rb0 = {}` by
    (Cases_on `rb0` >> gvs[ptrDisciplineTheory.op_taint_def, target_ptr_ok_def] >>
     fs[ghost_kept_def, ptrDisciplineTheory.op_taint_def]) >>
  `MAP FDOM es.scopes = MAP FDOM (es_end with gas_obs := []).scopes` by
    (drule eval_base_place_preserves_scopes_dom >> simp[Abbr `em`]) >>
  `MAP FDOM (es_end with gas_obs := []).scopes = MAP FDOM ef.scopes` by
    (drule (REWRITE_RULE [ETA_AX] forced_eval_expr_preserves_scopes_dom) >> simp[Abbr `em`]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (qpat_assum `ghost_kept cenv es sa _ _ _ _ _`
       (mp_then Any mp_tac wordOperandsPtrTheory.ghost_kept_trans) >>
     disch_then irule >> simp[] >> conj_tac
     >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`es_end with gas_obs := []`, `t`, `sm`] >>
     fs[target_post_wb_frame, ci_mono_def, stmt_state_rel_def, state_rel_def]) >>
  suspend "mapping_source"
QED

Resume target_mapping_sim_ptr[mapping_source]:
  Cases_on `extend_place cx (HashMapRef tr base_slot (expr_type e) leaf)
      (ValueSubscript v) ef` >>
  rename1 `extend_place _ _ _ ef = (rr,ee)` >>
  drule_all target_subscript_source_cut_ptr >> strip_tac >>
  `!m. rr <> INR (Error (TypeError m))` by
    (qpat_x_assum `gas_admissible (eval_base_place _ (SubscriptTarget _ _)) _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings ++ em.gas_obs` mp_tac) >>
     simp[target_res_ok_def] >> rpt strip_tac >> gvs[]) >>
  `~t'.vs_halted` by
    metis_tac[gas_marked_exec_ptr_def, gas_path_ptr_ok_not_halted] >>
  `!x. key = Var x ==> not_fresh_at sn x` by
    metis_tac[compile_lower_value_var] >>
  `post_value_type cenv e = expr_type e` by
    (Cases_on `is_bytestring_type (expr_type e)` >- simp[] >>
     drule_all map_scalar_key_word >> simp[]) >>
  `ptr_val_ok cx (expr_type e) v key G' tn' t'` by fs[] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x)` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
  fs[ci_mono_def] >>
  `MAP FDOM es.scopes = MAP FDOM (es_end with gas_obs := []).scopes /\
   MAP FDOM (es_end with gas_obs := []).scopes = MAP FDOM ef.scopes` by
    (simp[] >> metis_tac[]) >>
  drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`) target_map_normal_continue_ptr >>
  disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  irule target_map_suffix_outcome_ptr >> simp[Abbr `ef`] >> metis_tac[]
QED

Resume target_mapping_sim_ptr[base_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf'`, `finish'`] >>
  simp[Once evaluate_def, ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_result >> fs[ignore_bind_def]
QED

Finalise target_mapping_sim_ptr
