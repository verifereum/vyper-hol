(* Source readiness and counted pure-storage target continuations. *)
Theory targetStorageContinuationMemory
Ancestors
  targetStorageArraySummaryMemory targetMappingSummaryMemory
  targetIndexCompositionMemory targetSubscriptSplit
  targetPlaceSimDefs loweringStateRelDefs loweringPosts
  gasOutcome gasSummary exprSimHypsDefs exprSimDefs exprReasonOperand
  targetPlaceSimCasesBase stmtLoweringMono exprLoweringProps
  stmtSimAugAssignPlaceStorage targetPlaceSim exprSimHyps
  bodySimStmtCases exprOpenTerminals exprLowering compileEnv vyperInterpreter
  vyperState vyperStorage vyperValue list
Libs
  pairLib

Theorem target_pure_storage_result_ready_mem[local]:
  contract_storage_well_formed cx es /\
  EVERY (supported_pure_expr tops) (target_indices bt) /\
  eval_base_place cx bt es = (INL (PlaceR (StoragePlace tr slot tv)),ee) ==>
  slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
  storage_read_live cx tr (get_storage cx ee tr) slot tv
Proof
  metis_tac[aug_place_pure_base_storage_range, aug_place_pure_base_storage_live]
QED

Theorem target_storage_index_open_mem[local]:
  body_inv tops ctx cenv cx /\ supported_expr tops e /\
  expr_body_pre cenv cx env e es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  eval_expr cx e es = (INL tv,es1) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  ~block_is_terminated sm ==> ~block_is_terminated sn
Proof
  simp[lower_value_def, comp_bind_def] >> pairarg_tac >>
  strip_tac >> gvs[] >> irule unwrap_value_open >>
  goal_assum (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  irule compile_expr_open >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  metis_tac[]
QED

Theorem target_storage_typed_summary_mem[local]:
  ((?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)) \/
   (?tr slot kt vty. pv = HashMapRef tr slot kt vty)) /\
  subscript_vtype bvt (expr_type e) = SOME vt /\
  well_formed_vtype (get_tenv cx) vt /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\ value_has_type itv key /\
  target_post ctx func cenv cx es0 sa sn s0 es pv bvt rb s /\
  expr_post ctx func cenv cx e ee sm sn t es key ix s /\
  expr_store_bound cx (expr_type e) key ix s /\ expr_sim_inv cenv cx env es /\
  (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
    storage_read_live cx tr (get_storage cx es tr) slot tv /\
    w2n slot + type_slot_size tv <= dimword(:256) /\
    (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
      w2n (lookup_storage slot (get_storage cx es tr)) <= cnt)) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\ ~block_is_terminated sn /\
  local_ptrs_reserved cenv sn /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next ==>
  gas_summary_at T (ctx,func) []
    (extend_place cx pv (ValueSubscript key)) (es,s)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es0 sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac
  >- (`?aty. bvt = Type aty` by
        (fs[target_post_def] >> Cases_on `bvt` >> gvs[place_ptr_rel_def]) >>
      gvs[] >> irule target_storage_array_typed_summary_mem >> simp[] >>
      metis_tac[]) >>
  gvs[] >> irule target_mapping_typed_summary_mem >> simp[] >> metis_tac[]
QED

Theorem target_storage_index_summary_mem[local]:
  (!gs. expr_body_pre cenv cx env e (mid with gas_obs := gs)) /\
  ((?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)) \/
   (?tr slot kt vty. pv = HashMapRef tr slot kt vty)) /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (mid with gas_obs := [],t) right (INL key) ee (OK u) /\
  target_post ctx func cenv cx es sa sn s0 (ee with gas_obs := []) pv bvt rb u /\
  expr_post ctx func cenv cx e (mid with gas_obs := []) sm sn t
    (ee with gas_obs := []) key ix u /\
  expr_store_bound cx (expr_type e) key ix u /\
  subscript_vtype bvt (expr_type e) = SOME vt /\
  well_formed_vtype (get_tenv cx) vt /\
  (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
    storage_read_live cx tr (get_storage cx (ee with gas_obs := []) tr) slot tv /\
    w2n slot + type_slot_size tv <= dimword(:256) /\
    (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
      w2n (lookup_storage slot (get_storage cx (ee with gas_obs := []) tr)) <= cnt)) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\ ~block_is_terminated sn /\
  local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!l. FST rb <> Label l) /\ alloca_history func u /\
  s0.vs_alloca_next <= u.vs_alloca_next ==>
  gas_summary_at T (ctx,func) [] (extend_place cx pv (ValueSubscript key))
    (ee with gas_obs := [],u)
    (\res fin v. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 fin pv' vt op v /\
      v.vs_current_bb = sb.cs_current_bb /\ v.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func v /\ s0.vs_alloca_next <= v.vs_alloca_next)
    (\res fin r. expr_exit res r)
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := gas_explicit right t.vs_gas_readings) =
    (INL key,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
    (mid with gas_obs := gas_explicit right t.vs_gas_readings)` by simp[] >>
  drule_all target_subscript_index_source_diagnostic >> strip_tac >>
  drule_all target_subscript_index_runtime_diagnostic >> strip_tac >>
  `!x. ix = Var x ==> not_fresh_at sn x` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `!x. FST op = Var x ==> not_fresh_at sb x` by
    metis_tac[target_subscript_suffix_var] >>
  `~u.vs_halted` by metis_tac[target_subscript_marked_nonhalted] >>
  `!l. ix <> Label l` by
    (irule lower_compile_expr_not_label >>
     goal_assum (drule_at (Pat `lower_value`)) >>
     qexists `env` >> fs[expr_body_pre_def, expr_sim_inv_def]) >>
  gvs[] >>
  drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    target_storage_typed_summary_mem >>
  disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then irule >> simp[] >>
  qexists `env` >> fs[expr_sim_inv_def] >> metis_tac[]
QED

Theorem target_storage_marked_ready_mem[local]:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  EVERY pure_expr (target_indices (SubscriptTarget bt e)) /\
  gas_marked_exec T (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (mid with gas_obs := [],t) right (INL key) ee (OK u) ==>
  !tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
    storage_read_live cx tr (get_storage cx (ee with gas_obs := []) tr) slot tv /\
    w2n slot + type_slot_size tv <= dimword(:256) /\
    (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
      w2n (lookup_storage slot (get_storage cx (ee with gas_obs := []) tr)) <= cnt)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule target_subscript_marked_base_source >>
  disch_then (qspec_then `gas_explicit right t.vs_gas_readings` assume_tac) >>
  `bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := gas_explicit right t.vs_gas_readings) =
    (INL key,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_at (Pat `eval_base_place _ _ _ = _`) target_subscript_storage_ready >>
  disch_then (drule_at (Pat `bind _ _ _ = _`)) >>
  impl_tac >-
    (fs[target_pre_def, expr_sim_inv_def] >>
     irule vyperStorageLayoutSafetyTheory.contract_storage_well_formed_storage_frame >>
     goal_assum (drule_at Any) >>
     Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  simp[]
QED

Theorem target_storage_marked_index_open_mem[local]:
  body_inv tops ctx cenv cx /\ supported_expr tops e /\
  (!gs. expr_body_pre cenv cx env e (mid with gas_obs := gs)) /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (mid with gas_obs := [],t) right (INL key) ee (OK u) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  ~block_is_terminated sm ==> ~block_is_terminated sn
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := gas_explicit right t.vs_gas_readings) =
    (INL key,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `?tv es1. eval_expr cx e
    (mid with gas_obs := gas_explicit right t.vs_gas_readings) = (INL tv,es1)` by
    (fs[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `expr_body_pre cenv cx env e mid` by
    (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  irule target_storage_index_open_mem >>
  goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >> simp[] >> metis_tac[]
QED

Theorem target_storage_index_bind_mem[local]:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  EVERY pure_expr (target_indices (SubscriptTarget bt e)) /\
  body_inv tops ctx cenv cx /\ supported_expr tops e /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  (!gs. expr_body_pre cenv cx env e (mid with gas_obs := gs)) /\
  ((?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)) \/
   (?tr slot kt vty. pv = HashMapRef tr slot kt vty)) /\
  gas_marked_exec T (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) /\
  subscript_vtype bvt (expr_type e) = SOME vt /\ well_formed_vtype (get_tenv cx) vt /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\ ~block_is_terminated sm /\
  local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  (!l. FST rb <> Label l) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (mid with gas_obs := [],t)
    (\res ee u. ?key. res = INL key /\
      target_post ctx func cenv cx es sa sn s0 ee pv bvt rb u /\
      expr_post ctx func cenv cx e (mid with gas_obs := []) sm sn t ee key ix u /\
      expr_store_bound cx (expr_type e) key ix u /\
      u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\key. extend_place cx pv (ValueSubscript key)))
    (mid with gas_obs := [],t)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> (irule target_subscript_index_bind_outcome >>
  qexists `\key ee u.
    target_post ctx func cenv cx es sa sn s0 ee pv bvt rb u /\
    expr_post ctx func cenv cx e (mid with gas_obs := []) sm sn t ee key ix u /\
    expr_store_bound cx (expr_type e) key ix u /\
    u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next` >>
  pure_rewrite_tac[BETA_THM] >> reverse conj_tac >- gvs[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(\key ee u. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `~block_is_terminated sn` by
    (irule target_storage_marked_index_open_mem >>
     goal_assum (drule_at (Pat `gas_marked_exec _ _ (bind _ _) _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `lower_value`)) >> metis_tac[]) >>
  `!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
    storage_read_live cx tr (get_storage cx (ee with gas_obs := []) tr) slot tv /\
    w2n slot + type_slot_size tv <= dimword(:256) /\
    (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
      w2n (lookup_storage slot (get_storage cx (ee with gas_obs := []) tr)) <= cnt)` by
    (drule_at (Pat `gas_marked_exec _ _ (eval_base_place _ _) _ _ _ _ _`)
       target_storage_marked_ready_mem >>
     disch_then (drule_at (Pat `gas_marked_exec _ _ (bind _ _) _ _ _ _ _`)) >>
     simp[] >> disch_then irule >> metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV) exprBopSimPropsTheory.bop_marked_scopes_dom) >>
     drule target_subscript_marked_base_domains >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  `expr_body_pre cenv cx env e mid` by
    (qpat_x_assum `!gs. expr_body_pre _ _ _ _ _` (qspec_then `[]` mp_tac) >> simp[]) >>
  gvs[] >> irule target_storage_index_summary_mem >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ (bind _ _) _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> metis_tac[])
QED

Theorem target_subscript_storage_continuation_mem_core[local]:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  EVERY pure_expr (target_indices (SubscriptTarget bt e)) /\
  body_inv tops ctx cenv cx /\ supported_expr tops e /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  ((?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)) \/
   (?tr slot kt vty. pv = HashMapRef tr slot kt vty)) /\
  type_place_target env bt = SOME bvt /\ subscript_vtype bvt (expr_type e) = SOME vt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  ci_mono sa sm /\ ci_mono sm sn /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ~block_is_terminated sm /\
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  gas_marked_exec T (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) /\
  target_post ctx func cenv cx es sa sm s0 (mid with gas_obs := []) pv bvt rb t /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  expr_sim_mem ctx func cenv cx (expr_type e) e (mid with gas_obs := []) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\key. extend_place cx pv (ValueSubscript key))) (mid with gas_obs := [],t)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> (
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `!gs. expr_body_pre cenv cx env e (mid with gas_obs := gs)` by
    (drule_all target_subscript_marked_base_inv >>
     fs[target_pre_def, target_indices_pre_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
    (mid with gas_obs := [])` by
    (irule target_subscript_index_admissible >> goal_assum (drule_at Any) >> simp[]) >>
  `!gs v ee. bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := gs) = (INL v,ee) ==> place_readable cx ee pv` by
    (rpt gen_tac >> strip_tac >>
     `place_readable cx (mid with gas_obs := gs) pv` by fs[target_post_def] >>
     drule target_subscript_marked_base_source >>
     disch_then (qspec_then `gs` assume_tac) >>
     drule_all target_subscript_pure_index_live >> strip_tac >>
     metis_tac[target_subscript_readable_gas_obs]) >>
  `expr_sim_inv cenv cx env es` by fs[target_pre_def] >>
  `!l. FST rb <> Label l` by metis_tac[target_subscript_typed_base_not_label] >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (drule target_subscript_marked_base_domains >> simp[]) >>
  `~t.vs_halted` by metis_tac[target_subscript_marked_base_nonhalted] >>
  `well_formed_vtype (get_tenv cx) vt` by
    metis_tac[target_subscript_pre_result_well_formed, target_subscript_vtype_well_formed] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id /\ sa.cs_next_var <= sn.cs_next_var /\
   sa.cs_next_id <= sn.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  drule target_index_outcome_mem >>
  disch_then (qspecl_then [`sn`, `ix`, `e`] mp_tac) >> simp[] >>
  impl_tac >- metis_tac[] >> strip_tac >>
  irule target_storage_index_bind_mem >> metis_tac[])
QED
