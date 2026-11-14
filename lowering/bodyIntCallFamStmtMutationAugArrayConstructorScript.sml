(* Counted array subscript composition from the base-target induction hypothesis. *)
Theory bodyIntCallFamStmtMutationAugArrayConstructor
Ancestors
  bodyIntCallFamStmtMutationAugArraySource bodyIntCallFamStmtMutationAugArraySuffix
  bodyIntCallFamStmtMutationAugIndexOutcome bodyIntCallFamStmtMutationAugTargetAttrCounted
  exprSimSubscriptMap targetSubscriptSplit targetSubscriptContinuation
  bodyIntCallJointContract bodyIntCallJointAggCore
  supportedStmts supportedTargets supportedExprTraverse vyperTypeCallGraph
  targetPlaceSim targetPlaceSimDefs targetPlaceSimCasesBase vyperTypeSystem fragExec
  stmtLoweringMono exprLoweringProps compileEnv gasOutcome gasSummary
  vyperInterpreter vyperState exprSimDefs exprSimHypsDefs loweringPosts

Theorem intcall_target_array_counted:
  !bt e.
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
  !ce env es sa sb s vt op bindings ety bd.
    (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
         intcall_map_producer fp e) /\ intcall_frame_ok fp /\
    body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    IS_SOME (supported_target_info fp.jc_tops bindings (SubscriptTarget bt e)) /\
    target_pre ce fp.jc_cx env (SubscriptTarget bt e) es /\
    type_place_target env (SubscriptTarget bt e) = SOME vt /\
    type_place_target env bt = SOME (Type (ArrayT ety bd)) /\
    calls_follow_call_graph fp.jc_edges fp.jc_owner
      (int_calls_target (SubscriptTarget bt e)) /\
    (!target. supported_target_exists (expr_abi_decode_target_root target)
       (SubscriptTarget bt e) ==> occurs_abi_decode_target target fp.jc_tops) /\
    compile_get_target_ptr compile_expr ce (SubscriptTarget bt e) sa = (op,sb) /\
    fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    gas_admissible (eval_base_place fp.jc_cx (SubscriptTarget bt e)) target_res_ok es /\
    intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (eval_base_place fp.jc_cx (SubscriptTarget bt e)) (es,s)
      (\res ee u. ?pv. res = INL pv /\
        target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s ee pv vt op u /\
        intcall_expr_cont fp ce env es sa s ee sb u)
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule target_subscript_compile_decompose >> strip_tac >>
  drule_all target_subscript_compile_intervals >> strip_tac >>
  `target_pre ce fp.jc_cx env bt es` by metis_tac[target_pre_sub] >>
  `subscript_vtype (Type (ArrayT ety bd)) (expr_type e) = SOME vt` by
    (qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
     simp[Once well_typed_expr_def]) >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sn fp.jc_func /\
   fn_has_code sn sb fp.jc_func` by
    (fs[ci_mono_def] >>
     `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
     drule_all fn_has_code_split >> strip_tac >>
     drule_all fn_has_code_split >> simp[]) >>
  `gas_admissible (eval_base_place fp.jc_cx bt) target_res_ok es` by
    metis_tac[target_subscript_base_admissible] >>
  `IS_SOME (supported_target_info fp.jc_tops bindings bt) /\
   supported_expr fp.jc_tops e` by
    (Cases_on `supported_target_info fp.jc_tops bindings bt` >>
     gvs[supported_target_info_def, AllCaseEqs()] >>
     Cases_on `supported_expr fp.jc_tops e` >> gvs[]) >>
  fs[int_calls_expr_def, supported_expr_exists_def] >>
  qpat_x_assum `!ce' env' es' sa' sb' s'' vt' op' bindings'. _`
    (qspecl_then [`ce`, `env`, `es`, `sa`, `sm`, `s`,
                  `Type (ArrayT ety bd)`, `rb`, `bindings`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  suspend "bind"
QED

Resume intcall_target_array_counted[bind]:
  `eval_base_place fp.jc_cx (SubscriptTarget bt e) =
    bind (eval_base_place fp.jc_cx bt)
      (\pv. bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
        (\key. extend_place fp.jc_cx pv (ValueSubscript key)))` by
    simp[FUN_EQ_THM, Once evaluate_def, bind_assoc] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  irule gas_outcome_bind_result_exec >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  simp[] >>
  conj_tac >- (Cases >> simp[expr_exit_def] >> metis_tac[]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> gvs[] >> suspend "index") >>
  metis_tac[]
QED

Resume intcall_target_array_counted[index]:
  `expr_body_pre ce fp.jc_cx env e (mid with gas_obs := [])` by
    (fs[target_pre_def, target_indices_pre_def] >>
     first_x_assum irule >> fs[intcall_expr_cont_def, intcall_expr_res_def]) >>
  `gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
     expr_res_ok (mid with gas_obs := [])` by
    (irule target_subscript_index_admissible >>
     goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
     fs[FUN_EQ_THM, Once evaluate_def, bind_assoc]) >>
  `intcall_expr_res fp ce env (mid with gas_obs := []) sm t /\
   ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by fs[intcall_expr_cont_def] >>
  `intcall_forced_producer fp e` by simp[] >>
  drule_all intcall_forced_index_outcome >> strip_tac >>
  irule target_subscript_index_bind_outcome >>
  qexists_tac `\key ee u. expr_val_rel fp.jc_cx (post_value_type ce e) key ix u /\
    (!x. ix = Var x ==> not_fresh_at sn x) /\
    intcall_expr_cont fp ce env (mid with gas_obs := []) sm t ee sn u` >>
  simp[] >> rpt gen_tac >> strip_tac >>
  suspend "suffix"
QED

Resume intcall_target_array_counted[suffix]:
  `local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm` by
    fs[intcall_expr_res_def] >>
  `expr_sim_inv ce fp.jc_cx env es` by fs[intcall_expr_res_def] >>
  `(!l. FST rb <> Label l)` by
    (drule_all target_subscript_typed_base_not_label >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sn.cs_next_id` by fs[ci_mono_def] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by fs[intcall_expr_res_def] >>
  drule_at (Pat `gas_marked_exec _ _ (eval_base_place _ _) _ _ _ _ _`)
    intcall_target_array_index_ready >>
  disch_then drule_all >> strip_tac >> gvs[] >>
  suspend "finish"
QED

Resume intcall_target_array_counted[finish]:
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (drule target_subscript_marked_base_domains >> simp[]) >>
  `intcall_expr_cont fp ce env es sa s (ee with gas_obs := []) sn u` by
    (drule_all bodyIntCallJointAggCoreTheory.intcall_expr_cont_trans >> simp[]) >>
  `return_nonlabel ix` by
    (irule exprReasonOperandTheory.lower_compile_expr_not_label >>
     goal_assum (drule_at (Pat `lower_value`)) >>
     qexists_tac `env` >> fs[expr_body_pre_def, expr_sim_inv_def,
       intcall_expr_res_def]) >>
  `!x. FST op = Var x ==> not_fresh_at sb x` by
    (`SND (SND rb) = SOME (ValPT (ArrayT ety bd)) /\
      ?loc. FST (SND rb) = SOME loc` by
       (fs[target_post_def, exprLoweringTheory.value_type_place_def, place_ptr_rel_def] >>
        Cases_on `v` >> gvs[place_ptr_rel_def, AllCaseEqs()] >>
        Cases_on `p` >> gvs[place_ptr_rel_def]) >>
     PairCases_on `rb` >> gvs[target_subscript_suffix_array] >>
     metis_tac[exprOperandVarTheory.compiler_subscript_ops_var]) >>
  irule intcall_target_array_suffix_summary >>
  simp[arithmeticTheory.ADD_COMM] >>
  conj_tac >- gvs[] >>
  qexistsl_tac [`bd`, `e`, `ety`, `itv`, `ix`, `rb`, `sn`] >>
  simp[] >> fs[ci_mono_def] >> decide_tac
QED

Finalise intcall_target_array_counted
