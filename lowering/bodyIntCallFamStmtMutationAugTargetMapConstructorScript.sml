(* Counted mapping constructor: source readiness and counted composition. *)
Theory bodyIntCallFamStmtMutationAugTargetMapConstructor
Ancestors
  bodyIntCallFamStmtMutationAugTargetMapBoundary
  bodyIntCallFamStmtMutationAugTargetMapSource
  bodyIntCallFamAggSubscriptForcedOutcome bodyIntCallJointAggCore
  targetSubscriptSplit exprSimIfExp targetPlaceSim targetPlaceSimDefs
  exprSimHypsDefs vyperInterpreter gasSummary vyperState
  bodyIntCallJointContract exprSimSubscriptMap

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
