Theory bodyPtrPopTargetSimArrayConstructor
Ancestors
  bodyPtrPopTargetSimArrayCompose bodyPtrPopTargetSimAttribute
  bodyPtrPopTargetSimSubscriptCuts fragGasPathPtr fragGasSeqPtr fragExec pair freshWrites
  bodyPtrPopTargetSimFixedMemory bodyPtrPopTargetSimFixedSlot
  bodyPtrPopTargetSimDynamicMemory bodyPtrPopTargetSimDynamicSlot
  bodyPtrPopTargetSimIndexSource bodyPtrPopTargetSimIndexFrame
  exprLoweringProps exprSimHypsDefs exprSimHyps vyperTyping vyperTypeSystem
  gasExemptCert gasSummaryComposePtr targetPlaceSimCasesBase
  exprLowering emitHelperProps stmtLoweringMono compileEnv loweringPosts
  bodyPtrPopTargetDefs targetPlaceSimDefs targetPlaceSim exprSimSource exprSimDefs
  vyperInterpreter vyperState

Theorem target_array_sim_ptr:
  body_inv tops ctx cenv cx /\
  body_base_target_ptr_ok cx (SubscriptTarget bt e) /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  (!id. target_root bt = NameTarget id ==>
        local_target_live cx id (SubscriptTarget bt e)) /\
  (!src id. target_root bt = TopLevelNameTarget (src,id) ==>
        EVERY pure_expr (target_indices (SubscriptTarget bt e))) /\
  type_place_target env bt = SOME (Type (ArrayT et bd)) /\
  target_sim_ptr d ctx PG func cenv cx env bt es ==>
  target_sim_ptr d ctx PG func cenv cx env (SubscriptTarget bt e) es
Proof
  strip_tac >> simp[target_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
  simp[Once well_typed_expr_def] >> strip_tac >> gvs[] >>
  suspend "base"
QED

Resume target_array_sim_ptr[base]:
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  rename1 `compile_get_target_ptr _ _ bt sa = (rb,sm)` >>
  `fn_has_code sa sm func /\ cs_extends sm sb` by
    (mp_tac (cj 1 compile_expr_ci_mono) >> strip_tac >>
     drule_all target_subscript_base_code_ptr >> simp[]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    metis_tac[target_subscript_base_admissible_ptr] >>
  qpat_x_assum `target_sim_ptr _ _ _ _ _ _ _ bt _`
    (mp_tac o REWRITE_RULE [target_sim_ptr_def]) >>
  disch_then (qspecl_then [`Type (ArrayT et bd)`, `sa`, `sm`, `rb`,
                         `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- suspend "base_summary" >>
  suspend "base_exempt"
QED

Resume target_array_sim_ptr[base_summary]:
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

Resume target_array_sim_ptr[index]:
  `SND (SND rb) = SOME (ValPT (ArrayT et bd))` by
    fs[target_post_def, value_type_place_def] >>
  PairCases_on `rb` >> gvs[] >>
  drule_all target_array_compile_parts_ptr >> strip_tac >> gvs[] >>
  suspend "index_run"
QED

Resume target_array_sim_ptr[index_run]:
  `ci_mono sa sm` by metis_tac[ci_mono_compile_get_target_ptr, SND] >>
  `ci_mono sm sn` by metis_tac[compile_expr_ci_mono, ci_mono_lower_value_cfn, SND] >>
  `ci_mono sn sb` by metis_tac[ci_mono_compile_array_subscript, ci_mono_compile_ptr_load, SND] >>
  `fn_has_code sm sn func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_ptr_def, gas_path_ptr_ok_not_halted] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sm`, `sn`, `idx`, `t`, `G`, `tn`] mp_tac) >>
  suspend "index_premises"
QED

Resume target_array_sim_ptr[index_premises]:
  (impl_tac >-
    (fs[target_post_def, ci_mono_def] >>
     metis_tac[not_fresh_at_mono])) >>
  strip_tac >> suspend "index_outcome"
QED

Resume target_array_sim_ptr[index_outcome]:
  rewrite_tac[GSYM gas_outcome_ptr_def] >>
  simp[Once evaluate_def] >>
  irule gas_outcome_ptr_bind_normal >>
  qexistsl_tac [`G`, `marks`, `es_end`, `t`, `tn`, `pv`] >>
  conj_tac
  >- (rpt strip_tac >> BETA_TAC >>
      irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`es_end`, `t`, `pv`] >> fs[]) >>
  reverse conj_tac >- simp[] >>
  suspend "index_suffix"
QED

Resume target_array_sim_ptr[index_suffix]:
  BETA_TAC >> once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
  >- suspend "index_summary" >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks'` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  drule gas_exempt_cert_error_value >>
  disch_then (qspec_then
    `\v. ignore_bind (extend_place cx pv (ValueSubscript v)) (return ())` mp_tac) >>
  simp[ignore_bind_def, vyperStateTheory.bind_assoc]
QED

Resume target_array_sim_ptr[index_summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >> gvs[]
  >~ [`exit_result r`]
  >- (simp[gas_outcome_ptr_def] >> qexists_tac `marks'` >> disj1_tac >>
      Cases_on `res` >> gvs[expr_exit_def] >>
      irule gas_summary_ptr_at_bind_exception >> simp[] >>
      qexistsl_tac [`G'`, `y`, `es_end'`, `r`, `tn'`] >>
      fs[oneline expr_exit_def]) >>
  suspend "suffix"
QED

Resume target_array_sim_ptr[suffix]:
  irule gas_outcome_ptr_bind_normal >>
  qexistsl_tac [`G'`, `marks'`, `es_end'`, `t'`, `tn'`, `v`] >>
  conj_tac
  >- (rpt strip_tac >> BETA_TAC >>
      irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`es_end'`, `t'`, `v`] >> fs[]) >>
  reverse conj_tac >- simp[] >> BETA_TAC >>
  suspend "array_suffix"
QED

Resume target_array_sim_ptr[array_suffix]:
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
  suspend "source_ready"
QED

Resume target_array_sim_ptr[source_ready]:
  `expr_sim_inv cenv cx env em` by simp[Abbr `em`] >>
  `expr_body_pre cenv cx env e em` by
    (fs[target_pre_def, target_indices_pre_def] >>
     first_x_assum irule >> metis_tac[]) >>
  `expr_sim_inv cenv cx env ef` by
    (qpat_x_assum `bind _ _ em = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     metis_tac[exprSimSourceTheory.expr_body_pre_eval_result]) >>
  suspend "source_typed"
QED

Resume target_array_sim_ptr[source_typed]:
  cheat
QED

Resume target_array_sim_ptr[base_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[Once evaluate_def, ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_result >> fs[ignore_bind_def]
QED

Finalise target_array_sim_ptr
