Theory bodyPtrPopTargetSimAttribute
Ancestors
  bodyPtrPopTargetSimAttributeAdd gasSummaryComposePtr targetPlaceSimCasesBase
  exprLoweringProps exprSimHypsDefs exprSimProps vyperTyping vyperState
  vyperInterpreter compileEnv loweringPosts fragGasSeqPtr gasExemptCert
  gasSummary gasOutcome fragGasPathPtr bodyPtrPopTargetDefs
  bodyPtrPopTargetSimAttributeSource bodyPtrDefs targetPlaceSimDefs
  exprLowering emitHelperProps stmtLoweringMono fragExec pair
  gasContext vyperTypeSystem venomState exprSimDefs targetPlaceSim exprSimHyps
  vyperTypeInvariants list

Theorem target_attribute_sim_ptr:
  target_pre cenv cx env (AttributeTarget bt fld) es /\
  target_sim_ptr d ctx PG func cenv cx env bt es ==>
  target_sim_ptr d ctx PG func cenv cx env (AttributeTarget bt fld) es
Proof
  strip_tac >> simp[target_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ bty fld = SOME fty` >>
  drule compile_get_target_ptr_attr >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_get_target_ptr, SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_emit_op, SND] >>
  `cs_extends sa sm /\ cs_extends sm sb /\ sa.cs_next_var <= sm.cs_next_var`
    by fs[ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `eval_base_place cx (AttributeTarget bt fld) =
     bind (eval_base_place cx bt) (\pv. extend_place cx pv (AttrSubscript fld))`
    by simp[FUN_EQ_THM, Once evaluate_def] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, bind_def] >> rpt strip_tac >>
     Cases_on `res` >> simp[target_res_ok_def] >>
     first_x_assum (qspec_then `gs` mp_tac) >> simp[target_res_ok_def]) >>
  qpat_x_assum `target_sim_ptr _ _ _ _ _ _ _ bt _`
    (mp_tac o REWRITE_RULE [target_sim_ptr_def]) >>
  disch_then (qspecl_then [`Type bty`, `sa`, `sm`, `rb`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- suspend "summary" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_result >> fs[ignore_bind_def]
QED

Resume target_attribute_sim_ptr[summary]:
  qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >> gvs[]
  >~ [`exit_result r`]
  >- (Cases_on `res` >> gvs[expr_exit_def] >>
      irule gas_summary_ptr_at_bind_exception >> simp[] >> metis_tac[]) >>
  rename1 `target_post _ _ _ _ _ _ _ _ _ pv _ _ t` >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_ptr_def, gas_path_ptr_ok_not_halted] >>
  qabbrev_tac `es1 = es_end with gas_obs := []` >>
  `eval_base_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL pv, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[Abbr `es1`]) >>
  `expr_sim_inv cenv cx env es1` by
    (irule eval_base_place_sim_inv >>
     qexistsl_tac [`bt`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                   `INL pv`] >> fs[target_pre_def] >>
     metis_tac[target_pre_sub, target_pre_def]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?sid. bty = StructT sid` by
    (Cases_on `bty` >> gvs[attribute_type_def]) >> gvs[] >>
  Cases_on `extend_place cx pv (AttrSubscript fld) es1` >>
  rename1 `extend_place _ _ _ _ = (res1, es2)` >>
  `!m. res1 <> INR (Error (TypeError m))` by
    (qpat_x_assum `gas_admissible (bind _ _) _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     simp[bind_def] >> rpt strip_tac >> gvs[target_res_ok_def]) >>
  `?w0. eval_operand (FST rb) t = SOME w0 /\
        place_ptr_rel cenv cx t pv w0 (FST (SND rb)) (Type (StructT sid)) /\
        SND (SND rb) = SOME (ValPT (StructT sid)) /\
        place_readable cx es1 pv` by
    (fs[target_post_def, value_type_place_def] >> metis_tac[]) >>
  drule_all target_field_source_ptr >> strip_tac >> gvs[] >>
  suspend "continuation"
QED

Resume target_attribute_sim_ptr[continuation]:
  drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`) target_add_continuation_ptr >>
  disch_then (drule_at (Pat `place_ptr_rel _ _ _ _ (_ + _) _ _`)) >>
  simp[] >> strip_tac >>
  `target_ptr_ok cenv pv' rb G tn t` by metis_tac[] >>
  first_x_assum drule_all >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INL pv'`, `es_end`, `H`, `tm`, `OK q`] >>
  reverse conj_tac >- gvs[Abbr `es1`, exit_result_def] >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal
         |> REWRITE_RULE [APPEND_NIL]) >>
  qexistsl_tac [`G`, `es_end`, `t`, `tn`, `pv`] >>
  conj_tac >- simp[] >>
  simp[gas_marked_exec_ptr_def, gas_explicit_nil] >>
  qpat_x_assum `!gs. extend_place _ _ _ _ = _` mp_tac >>
  simp[Abbr `es1`]
QED

Finalise target_attribute_sim_ptr
