(* Conditional counted Attribute constructor; the base contract is an IH. *)
Theory bodyIntCallFamStmtMutationAugTargetAttrCounted
Ancestors
  bodyIntCallFamStmtMutationAugTargetAttr targetPlaceSimCasesBase
  bodyIntCallJointAggCore gasSummaryCompose gasOutcome gasExemptCert
  supportedStmts supportedTargets supportedExprTraverse
  vyperTypeCallGraph targetPlaceSimDefs vyperTypeSystem
  stmtLoweringMono exprLoweringProps compileEnv pair fragExec
  vyperInterpreter vyperState gasContext targetPlaceSim
  gasSummary exprSimDefs exprSimHypsDefs loweringPosts
  exprLowering vyperTypeEnv vyperTypeInvariants
  vyperEvalExprPreservesScopesDom loweringStateRelDefs

Theorem intcall_target_attribute_counted:
  !bt fld.
  (!ce env es sa sb s vt op bindings.
    (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
         intcall_map_producer fp e) /\ intcall_frame_ok fp /\
    body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    IS_SOME (supported_target_info fp.jc_tops bindings bt) /\
    target_pre ce fp.jc_cx env bt es /\ type_place_target env bt = SOME vt /\
    calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_target bt) /\
    (!target. supported_target_exists (expr_abi_decode_target_root target) bt ==>
       occurs_abi_decode_target target fp.jc_tops) /\
    compile_get_target_ptr compile_expr ce bt sa = (op,sb) /\
    fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    gas_admissible (eval_base_place fp.jc_cx bt) target_res_ok es /\
    intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (eval_base_place fp.jc_cx bt) (es,s)
      (\res ee u. ?pv. res = INL pv /\
        target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s ee pv vt op u /\
        intcall_expr_cont fp ce env es sa s ee sb u)
      (\res ee r. expr_exit res r)) ==>
  !ce env es sa sb s vt op bindings.
    (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
         intcall_map_producer fp e) /\ intcall_frame_ok fp /\
    body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    IS_SOME (supported_target_info fp.jc_tops bindings (AttributeTarget bt fld)) /\
    target_pre ce fp.jc_cx env (AttributeTarget bt fld) es /\
    type_place_target env (AttributeTarget bt fld) = SOME vt /\
    calls_follow_call_graph fp.jc_edges fp.jc_owner
      (int_calls_target (AttributeTarget bt fld)) /\
    (!target. supported_target_exists (expr_abi_decode_target_root target)
       (AttributeTarget bt fld) ==> occurs_abi_decode_target target fp.jc_tops) /\
    compile_get_target_ptr compile_expr ce (AttributeTarget bt fld) sa = (op,sb) /\
    fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    gas_admissible (eval_base_place fp.jc_cx (AttributeTarget bt fld)) target_res_ok es /\
    intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (eval_base_place fp.jc_cx (AttributeTarget bt fld)) (es,s)
      (\res ee u. ?pv. res = INL pv /\
        target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s ee pv vt op u /\
        intcall_expr_cont fp ce env es sa s ee sb u)
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `target_pre ce fp.jc_cx env bt es` by metis_tac[target_pre_sub] >>
  qpat_x_assum `type_place_target _ (AttributeTarget _ _) = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ bty fld = SOME fty` >>
  drule compile_get_target_ptr_attr >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_get_target_ptr, SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_emit_op, SND] >>
  `cs_extends sa sm /\ cs_extends sm sb /\ sa.cs_next_var <= sm.cs_next_var`
    by fs[ci_mono_def] >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func` by
    metis_tac[fn_has_code_split] >>
  `eval_base_place fp.jc_cx (AttributeTarget bt fld) =
     bind (eval_base_place fp.jc_cx bt)
       (\pv. extend_place fp.jc_cx pv (AttrSubscript fld))`
    by simp[FUN_EQ_THM, Once evaluate_def] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  `gas_admissible (eval_base_place fp.jc_cx bt) target_res_ok es` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, bind_def] >> rpt strip_tac >>
     Cases_on `res` >> simp[target_res_ok_def] >>
     first_x_assum (qspec_then `gs` mp_tac) >> simp[target_res_ok_def]) >>
  `IS_SOME (supported_target_info fp.jc_tops bindings bt)` by
    (Cases_on `supported_target_info fp.jc_tops bindings bt` >>
     gvs[supported_target_info_def]) >>
  fs[int_calls_expr_def, supported_expr_exists_def] >>
  qpat_x_assum `!ce' env' es' sa' sb' s'' vt' op' bindings'. _`
    (qspecl_then [`ce`, `env`, `es`, `sa`, `sm`, `s`, `Type bty`, `rb`, `bindings`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "summary" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_result >> fs[ignore_bind_def]
QED

Resume intcall_target_attribute_counted[summary]:
  qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >> gvs[]
  >~ [`exit_result r`]
  >- (Cases_on `res` >> gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  rename1 `target_post _ _ _ _ _ _ _ _ _ pv _ _ t` >>
  qabbrev_tac `es1 = es_end with gas_obs := []` >>
  `eval_base_place fp.jc_cx bt
     (es with gas_obs := gas_explicit marks s.vs_gas_readings) =
     (INL pv, es1)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
     simp[Abbr `es1`]) >>
  `expr_sim_inv ce fp.jc_cx env es1` by
    (irule eval_base_place_sim_inv >>
     qexistsl_tac [`bt`, `es with gas_obs := gas_explicit marks s.vs_gas_readings`,
                   `INL pv`] >> fs[target_pre_def]) >>
  `env.type_defs = get_tenv fp.jc_cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?sid. bty = StructT sid` by
    (Cases_on `bty` >> gvs[attribute_type_def]) >> gvs[] >>
  Cases_on `extend_place fp.jc_cx pv (AttrSubscript fld) es1` >>
  rename1 `extend_place _ _ _ _ = (res1, es2)` >>
  `!m. res1 <> INR (Error (TypeError m))` by
    (qpat_x_assum `gas_admissible (bind _ _) _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s.vs_gas_readings` mp_tac) >>
     simp[bind_def] >> rpt strip_tac >> gvs[target_res_ok_def]) >>
  `?w0. eval_operand (FST rb) t = SOME w0 /\
        place_ptr_rel ce fp.jc_cx t pv w0 (FST (SND rb)) (Type (StructT sid)) /\
        SND (SND rb) = SOME (ValPT (StructT sid)) /\
        place_readable fp.jc_cx es1 pv` by
    (fs[target_post_def, value_type_place_def] >> metis_tac[]) >>
  drule_all attr_place_step >> strip_tac >> gvs[] >>
  suspend "landing"
QED

Resume intcall_target_attribute_counted[landing]:
  `intcall_expr_res fp ce env es1 sm t /\ ~t.vs_halted /\
   t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    fs[bodyIntCallJointContractTheory.intcall_expr_cont_def] >>
  `local_ptrs_reserved ce sa` by
    fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
  drule_at (Pat `emit_op _ _ _ = _`) intcall_target_add_cont >>
  disch_then drule_all >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    (drule eval_base_place_preserves_scopes_dom >> simp[]) >>
  `intcall_expr_cont fp ce env es sa s es1 sb u` by
    (irule bodyIntCallJointAggCoreTheory.intcall_expr_cont_trans >>
     conj_tac >- simp[] >>
     qexistsl_tac [`es1`, `sm`, `t`] >> fs[ci_mono_def]) >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL pv'`, `es_end`, `OK u`] >> simp[Abbr `es1`] >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
         |> REWRITE_RULE [listTheory.APPEND_NIL]) >>
  qexistsl_tac [`es_end`, `t`, `pv`] >>
  simp[gas_marked_exec_def, gas_explicit_nil] >> gen_tac >>
  `(es_end with gas_obs := []) with gas_obs := tail =
     es_end with gas_obs := tail` by
    simp[evaluation_state_component_equality] >> simp[] >>
  qspecl_then [`fp.jc_cx`, `pv`, `fld`, `es_end`, `tail`] mp_tac
    extend_place_attr_gas_obs >>
  qspecl_then [`fp.jc_cx`, `pv`, `fld`, `es_end`, `[]`] mp_tac
    extend_place_attr_gas_obs >> simp[]
QED

Finalise intcall_target_attribute_counted
