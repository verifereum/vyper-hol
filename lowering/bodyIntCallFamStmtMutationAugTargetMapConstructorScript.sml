(* Counted mapping constructor: source readiness and counted composition. *)
Theory bodyIntCallFamStmtMutationAugTargetMapConstructor
Ancestors
  bodyIntCallFamStmtMutationAugTargetMapBoundary
  bodyIntCallFamStmtMutationAugTargetMapSource
  bodyIntCallFamAggSubscriptForcedOutcome bodyIntCallJointAggCore
  targetSubscriptSplit exprSimIfExp targetPlaceSim targetPlaceSimDefs
  exprSimHypsDefs vyperInterpreter gasSummary vyperState
  bodyIntCallJointContract exprSimSubscriptMap
  supportedStmts supportedTargets supportedExprTraverse vyperTypeCallGraph
  targetPlaceSimCasesBase vyperTypeSystem fragExec
  stmtLoweringMono exprLoweringProps compileEnv gasOutcome loweringPosts
  targetSubscriptContinuation exprSimDefs

Theorem intcall_target_subscript_marked_index_pre:
  target_pre ce cx env (SubscriptTarget bt e) es /\
  gas_marked_exec memory (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) ==>
  expr_body_pre ce cx env e (mid with gas_obs := [])
Proof
  strip_tac >>
  `target_pre ce cx env bt es` by metis_tac[target_pre_sub] >>
  drule target_subscript_marked_base_source >>
  disch_then (qspec_then `[]` assume_tac) >>
  `expr_sim_inv ce cx env (mid with gas_obs := [])` by
    metis_tac[target_subscript_marked_base_inv] >>
  fs[target_pre_def, target_indices_pre_def]
QED

Theorem intcall_forced_post_outcome_from_origin:
  intcall_forced_producer fp e /\
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env e mid /\
  supportedExprs$supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  lower_value compile_expr ce ty e sm = (ix,sn) /\
  fn_has_code sm sn fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
    expr_res_ok mid /\
  intcall_expr_res fp ce env es sa s0 /\
  intcall_expr_cont fp ce env es sa s0 mid sm t /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) (mid,t)
    (\res ee u. ?key. res = INL key /\
      expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e mid sm sn t ee key ix u /\
      intcall_expr_cont fp ce env mid sm t ee sn u /\
      intcall_expr_cont fp ce env es sa s0 ee sn u)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `intcall_expr_res fp ce env mid sm t /\ ~t.vs_halted /\
   t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by fs[intcall_expr_cont_def] >>
  drule_all intcall_forced_post_outcome >> strip_tac >>
  irule gas_outcome_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> qexists_tac `v` >> simp[] >>
  irule bodyIntCallJointAggCoreTheory.intcall_expr_cont_trans >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_target_mapping_index_suffix:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es0 sa s0 /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sm s0 mid
    (HashMapRef tr slot kt vt) (HashMapT kt vt) rb t /\
  expr_body_pre ce fp.jc_cx env e mid /\
  gas_marked_exec F (fp.jc_ctx,fp.jc_func)
    (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
    (mid,t) right (INL key) ee (OK u) /\
  expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e mid sm sn t
    (ee with gas_obs := []) key ix u /\
  intcall_expr_cont fp ce env mid sm t (ee with gas_obs := []) sn u /\
  intcall_expr_cont fp ce env es0 sa s0 (ee with gas_obs := []) sn u /\
  expr_type e = kt /\ hashmap_key_type kt /\
  well_formed_vtype (get_tenv fp.jc_cx) vt /\
  target_subscript_suffix ce e rb ix sn = (op,sb) /\
  fn_has_code sn sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\
  MAP FDOM es0.scopes = MAP FDOM mid.scopes /\
  (!l. FST rb <> Label l) /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) ==>
  gas_summary_at F (fp.jc_ctx,fp.jc_func) []
    (extend_place fp.jc_cx (HashMapRef tr slot kt vt) (ValueSubscript key))
    (ee with gas_obs := [],u)
    (\res es v. ?pv. res = INL pv /\
      target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sb s0 es pv vt op v /\
      intcall_expr_cont fp ce env es0 sa s0 es sb v)
    (\res es r. expr_exit res r)
Proof
  strip_tac >>
  `bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
     (mid with gas_obs := gas_explicit right t.vs_gas_readings) =
     (INL key,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre ce fp.jc_cx env e
     (mid with gas_obs := gas_explicit right t.vs_gas_readings)` by fs[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) ifexp_body_pre_read_typed) >> strip_tac >>
  `MAP FDOM es0.scopes = MAP FDOM (ee with gas_obs := []).scopes` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV) exprBopSimPropsTheory.bop_marked_scopes_dom) >>
     simp[]) >>
  irule intcall_target_mapping_extend_summary >> simp[] >>
  rpt strip_tac >> simp[] >>
  irule intcall_target_mapping_post_suffix >> simp[] >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  gvs[] >> metis_tac[]
QED

Theorem intcall_target_mapping_counted:
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
  !ce env es sa sb s vt op bindings kt vty.
    (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
         intcall_map_producer fp e) /\ intcall_frame_ok fp /\
    body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    IS_SOME (supported_target_info fp.jc_tops bindings (SubscriptTarget bt e)) /\
    target_pre ce fp.jc_cx env (SubscriptTarget bt e) es /\
    type_place_target env (SubscriptTarget bt e) = SOME vt /\
    type_place_target env bt = SOME (HashMapT kt vty) /\
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
  `subscript_vtype (HashMapT kt vty) (expr_type e) = SOME vt` by
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
                  `HashMapT kt vty`, `rb`, `bindings`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
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

Resume intcall_target_mapping_counted[index]:
  `expr_body_pre ce fp.jc_cx env e (mid with gas_obs := [])` by
    (irule intcall_target_subscript_marked_index_pre >>
     goal_assum (drule_at Any) >> simp[]) >>
  `gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
     expr_res_ok (mid with gas_obs := [])` by
    (irule target_subscript_index_admissible >>
     goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
     fs[FUN_EQ_THM, Once evaluate_def, bind_assoc]) >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (drule target_subscript_marked_base_domains >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[ci_mono_def] >>
  `intcall_forced_producer fp e` by simp[] >>
  drule_all intcall_forced_post_outcome_from_origin >> strip_tac >>
  irule target_subscript_index_bind_outcome >>
  qexists_tac `\key ee u.
    expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e (mid with gas_obs := []) sm sn t ee key ix u /\
    intcall_expr_cont fp ce env (mid with gas_obs := []) sm t ee sn u /\
    intcall_expr_cont fp ce env es sa s ee sn u` >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >> suspend "suffix"
QED

Resume intcall_target_mapping_counted[suffix]:
  `expr_type e = kt /\ vt = vty /\ hashmap_key_type kt` by
    gvs[subscript_vtype_def, AllCaseEqs()] >> gvs[] >>
  `well_formed_vtype (get_tenv fp.jc_cx) vt` by
    metis_tac[target_subscript_pre_result_well_formed] >>
  `?tr slot. v = HashMapRef tr slot (expr_type e) vt` by
    (fs[target_post_def, exprLoweringTheory.value_type_place_def] >>
     Cases_on `v` >> gvs[place_ptr_rel_def, AllCaseEqs()] >>
     Cases_on `p` >> gvs[place_ptr_rel_def]) >> gvs[] >>
  `expr_sim_inv ce fp.jc_cx env es` by fs[intcall_expr_res_def] >>
  `(!l. FST rb <> Label l)` by
    (drule_all target_subscript_typed_base_not_label >> simp[]) >>
  `local_ptrs_reserved ce sm` by fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `!x. ix = Var x ==> not_fresh_at sn x` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `SND (SND rb) = SOME (MapPT (expr_type e) vt)` by
    fs[target_post_def, exprLoweringTheory.value_type_place_def] >>
  `!x. FST op = Var x ==> not_fresh_at sb x` by
    (PairCases_on `rb` >> gvs[target_subscript_suffix_mapping] >>
     metis_tac[exprOperandVarTheory.compiler_subscript_ops_var]) >>
  irule intcall_target_mapping_index_suffix >>
  simp[] >> goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`ix`, `rb`, `sm`, `sn`] >>
  fs[ci_mono_def] >> decide_tac
QED

Finalise intcall_target_mapping_counted
