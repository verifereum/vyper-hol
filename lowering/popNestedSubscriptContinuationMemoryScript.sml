(* Counted subscript continuation with explicit endpoint readiness. *)
Theory popNestedSubscriptContinuationMemory
Ancestors
  popNestedTargetIndexMemory popNestedTargetSuffixMemory stmtReasonVvMemory
  targetSubscriptSplit targetPlaceSim targetPlaceSimMem exprLoweringProps exprSimMemDefs exprSimDefs
  loweringPosts targetPlaceSimDefs gasOutcome gasSummary exprSimHypsDefs
  targetPlaceSimCasesBase exprReasonOperand exprBopSimProps exprLowering
  exprOperandVar exprSimSource freshWrites compileEnv
  fragExec finite_map vyperAST vyperInterpreter vyperState venomState

Theorem pop_nested_subscript_continuation_mem:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e (mid with gas_obs := []) /\
  (!gs key ee.
    bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) = (INL key,ee) ==>
    place_readable cx ee pv /\
    (!id path. pv = PlaceR (MemoryPlace id path) ==>
      ?entry av. lookup_scopes id ee.scopes = SOME entry /\
        evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) /\
    (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
      storage_read_live cx tr (get_storage cx ee tr) slot tv /\
      w2n slot + type_slot_size tv <= dimword(:256) /\
      (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
        w2n (lookup_storage slot (get_storage cx ee tr)) <= cnt))) /\
  type_place_target env bt = SOME bvt /\
  subscript_vtype bvt (expr_type e) = SOME vt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  gas_marked_exec T (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) /\
  target_post ctx func cenv cx es sa sm s0 (mid with gas_obs := []) pv bvt rb t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\key. extend_place cx pv (ValueSubscript key)))
    (mid with gas_obs := [],t)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (mid with gas_obs := [],t)
    (\res ee u. ?key. res = INL key /\
      target_post ctx func cenv cx es sa sn s0 ee pv bvt rb u /\
      expr_post ctx func cenv cx e (mid with gas_obs := []) sm sn t ee key ix u /\
      expr_store_bound cx (expr_type e) key ix u /\
      u.vs_current_bb = sn.cs_current_bb /\
      u.vs_inst_idx = LENGTH sn.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)` by suspend "index" >>
  irule gas_outcome_bind_value >>
  qexistsl [`\res ee u. ?key. res = INL key /\
      target_post ctx func cenv cx es sa sn s0 ee pv bvt rb u /\
      expr_post ctx func cenv cx e (mid with gas_obs := []) sm sn t ee key ix u /\
      expr_store_bound cx (expr_type e) key ix u /\
      u.vs_current_bb = sn.cs_current_bb /\
      u.vs_inst_idx = LENGTH sn.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next`,
    `\res ee r. expr_exit res r`] >>
  reverse conj_tac >- suspend "exit" >>
  suspend "suffix"
QED

Resume pop_nested_subscript_continuation_mem[index]:
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `expr_sim_inv cenv cx env es` by fs[target_pre_def] >>
  `!l. FST rb <> Label l` by
    (drule_all target_subscript_typed_base_not_label >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (drule target_subscript_marked_base_domains >> simp[]) >>
  `~t.vs_halted` by metis_tac[target_subscript_marked_base_nonhalted] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
    (mid with gas_obs := [])` by
    (irule target_subscript_index_admissible >> goal_assum (drule_at Any) >> simp[]) >>
  irule pop_nested_target_index_outcome_mem >>
  goal_assum (drule_at Any) >>
  gvs[ci_mono_def] >> metis_tac[]
QED

Resume pop_nested_subscript_continuation_mem[exit]:
  rpt gen_tac >> simp[] >> Cases_on `res`
  >- (Cases_on `r` >> simp[oneline expr_exit_def, exit_result_def]) >>
  rpt strip_tac >> qexists `y` >>
  qpat_x_assum `expr_exit _ _` mp_tac >>
  simp[oneline expr_exit_def]
QED

Resume pop_nested_subscript_continuation_mem[suffix]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(\res ee u. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gvs[] >>
  `bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := gas_explicit marks t.vs_gas_readings) =
    (INL key, mid' with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  drule target_subscript_marked_base_source >>
  disch_then (qspec_then `gas_explicit marks t.vs_gas_readings` assume_tac) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := gas_explicit marks t.vs_gas_readings)` by
    (drule_at (Pat `eval_base_place _ _ _ = _`) eval_base_place_sim_inv >> simp[]) >>
  `expr_body_pre cenv cx env e (mid with gas_obs := gas_explicit marks t.vs_gas_readings)` by
    fs[target_pre_def, target_indices_pre_def] >>
  drule_all target_subscript_index_source_diagnostic >> strip_tac >>
  drule_all target_subscript_index_runtime_diagnostic >> strip_tac >>
  qpat_x_assum `!gs key ee. _` (drule_then strip_assume_tac) >>
  `local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `MAP FDOM es.scopes = MAP FDOM (mid' with gas_obs := []).scopes` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV) exprBopSimPropsTheory.bop_marked_scopes_dom) >>
     drule target_subscript_marked_base_domains >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `!x. ix = Var x ==> not_fresh_at sn x` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `!x. FST op = Var x ==> not_fresh_at sb x` by
    (drule target_subscript_suffix_var >> simp[]) >>
  `~t'.vs_halted` by (drule target_subscript_marked_nonhalted >> simp[]) >>
  `well_formed_vtype (get_tenv cx) vt` by
    metis_tac[target_subscript_pre_result_well_formed, target_subscript_vtype_well_formed] >>
  `!l. FST rb <> Label l` by
    (drule_all target_subscript_typed_base_not_label >> simp[]) >>
  `!l. ix <> Label l` by
    (irule lower_compile_expr_not_label >> goal_assum (drule_at (Pat `lower_value`)) >>
     qexists `env` >> fs[expr_body_pre_def, expr_sim_inv_def]) >>
  suspend "summary"
QED

Resume pop_nested_subscript_continuation_mem[summary]:
  drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    pop_nested_subscript_typed_summary_mem >>
  disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- fs[]) >>
  simp[gas_summary_at_def] >> strip_tac >>
  simp[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Finalise pop_nested_subscript_continuation_mem
