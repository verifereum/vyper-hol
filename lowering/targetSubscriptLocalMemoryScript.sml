(* Counted continuations for local array target places. *)
Theory targetSubscriptLocalMemory
Ancestors
  targetArraySuffixMemory targetIndexCompositionMemory targetSubscriptContinuation
  targetSubscriptSplit targetMemoryContracts exprSimMemDefs
  exprReasonOperand exprSimHypsDefs exprSimHyps targetPlaceLive
  targetPlaceSimCasesBase stmtLoweringMono targetPlaceSim targetPlaceSimDefs
  targetSubscriptMemory
  loweringPosts gasOutcome gasSummary gasContext fragGasMode fragExec
  exprSimDefs exprLowering exprLoweringProps compileEnv vyperInterpreter vyperState
  loweringStateRelDefs venomState list finite_map vyperTypeSystem vyperValue

Theorem target_local_array_summary_mem[local]:
  target_post ctx func cenv cx es0 sa sn s0 es
    (PlaceR (MemoryPlace id path))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
    SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\
  value_has_type itv (IntV i) /\ eval_operand ix s = SOME (i2w i) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next ==>
  gas_summary_at T (ctx,func) []
    (extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i))) (es,s)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es0 sa sb s0 ee pv' (Type ety) op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all target_subscript_memory_compile >> strip_tac >> gvs[] >>
  Cases_on `extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) es` >>
  rename1 `extend_place _ _ _ _ = (result,es')` >> Cases_on `result`
  >- (drule_all target_memory_array_suffix_mem >> strip_tac >>
      irule target_subscript_extend_summary_normal >>
      goal_assum (drule_at Any) >> simp[] >>
      fs[target_post_def, locals_kept_def, popped_kept_def] >>
      metis_tac[]) >>
  drule_all target_memory_array_error_suffix_mem >> strip_tac >> gvs[] >>
  irule target_subscript_extend_summary_error >>
  qexistsl [`Error (RuntimeError "evaluate_subscripts array_index")`, `es`,
    `Abort Revert_abort u`] >> simp[expr_exit_def, exit_result_def]
QED

Theorem target_local_typed_summary_mem[local]:
  subscript_vtype bvt (expr_type e) = SOME vt /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\ value_has_type itv key /\
  target_post ctx func cenv cx es0 sa sn s0 es (PlaceR (MemoryPlace id path)) bvt rb s /\
  expr_post ctx func cenv cx e ee sm sn t es key ix s /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next ==>
  gas_summary_at T (ctx,func) []
    (extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript key)) (es,s)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es0 sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `?w. place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w (FST (SND rb)) bvt` by
    (fs[target_post_def] >> metis_tac[]) >>
  gvs[place_ptr_rel_def] >>
  rename1 `subscript_vtype (Type aty) _ = _` >> Cases_on `aty` >>
  gvs[subscript_vtype_def, AllCaseEqs()] >>
  rename1 `evaluate_type _ (ArrayT ety bd) = _` >> Cases_on `bd` >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  drule_all target_subscript_int_index_view >> strip_tac >> gvs[]
  >- (drule (SRULE [] (Q.INST [`dyn` |-> `F`] target_local_array_summary_mem)) >>
      simp[evaluate_type_def] >> disch_then drule_all >> simp[]) >>
  drule (SRULE [] (Q.INST [`dyn` |-> `T`] target_local_array_summary_mem)) >>
  simp[evaluate_type_def] >> disch_then drule_all >> simp[]
QED

Theorem target_local_index_summary_mem[local]:
  (!gs. expr_body_pre cenv cx env e (mid with gas_obs := gs)) /\
  (!gs key ee. bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := gs) = (INL key,ee) ==>
    ?entry v. lookup_scopes id ee.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v) /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (mid with gas_obs := [],t) right (INL key) ee (OK u) /\
  target_post ctx func cenv cx es sa sn s0 (ee with gas_obs := [])
    (PlaceR (MemoryPlace id path)) bvt rb u /\
  expr_post ctx func cenv cx e (mid with gas_obs := []) sm sn t
    (ee with gas_obs := []) key ix u /\
  subscript_vtype bvt (expr_type e) = SOME vt /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\
  u.vs_current_bb = sn.cs_current_bb /\
  u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!l. FST rb <> Label l) /\ alloca_history func u /\
  s0.vs_alloca_next <= u.vs_alloca_next ==>
  gas_summary_at T (ctx,func) []
    (extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript key))
    (ee with gas_obs := [],u)
    (\res fin v. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 fin pv' vt op v /\
      v.vs_current_bb = sb.cs_current_bb /\
      v.vs_inst_idx = LENGTH sb.cs_current_insts /\
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
  qpat_x_assum `!gs key ee. _` drule >> strip_tac >>
  drule_all target_subscript_memory_array_ready >> strip_tac >> gvs[] >>
  `!x. ix = Var x ==> not_fresh_at sn x` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `!x. FST op = Var x ==> not_fresh_at sb x` by
    metis_tac[target_subscript_suffix_var] >>
  `~u.vs_halted` by metis_tac[target_subscript_marked_nonhalted] >>
  `!l. ix <> Label l` by
    (irule lower_compile_expr_not_label >>
     goal_assum (drule_at (Pat `lower_value`)) >>
     qexists `env` >> fs[expr_body_pre_def, expr_sim_inv_def]) >>
  irule target_local_typed_summary_mem >>
  simp[] >> metis_tac[]
QED

Theorem target_subscript_local_live_continuation_mem:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME bvt /\
  subscript_vtype bvt (expr_type e) = SOME vt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  ci_mono sa sm /\ ci_mono sm sn /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  gas_marked_exec T (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL (PlaceR (MemoryPlace id path))) mid (OK t) /\
  target_post ctx func cenv cx es sa sm s0 (mid with gas_obs := [])
    (PlaceR (MemoryPlace id path)) bvt rb t /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  expr_sim_mem ctx func cenv cx (expr_type e) e (mid with gas_obs := []) /\
  (!gs key ee. bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := gs) = (INL key,ee) ==>
    ?entry v. lookup_scopes id ee.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\key. extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript key)))
    (mid with gas_obs := [],t)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `!gs. expr_body_pre cenv cx env e (mid with gas_obs := gs)` by
    (drule_all target_subscript_marked_base_inv >>
     fs[target_pre_def, target_indices_pre_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
    (mid with gas_obs := [])` by
    (irule target_subscript_index_admissible >> goal_assum (drule_at Any) >> simp[]) >>
  `!gs v ee. bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := gs) = (INL v,ee) ==>
    place_readable cx ee (PlaceR (MemoryPlace id path))` by
    (rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
     irule place_readable_memory_live >> metis_tac[]) >>
  `expr_sim_inv cenv cx env es` by fs[target_pre_def] >>
  `!l. FST rb <> Label l` by metis_tac[target_subscript_typed_base_not_label] >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (drule target_subscript_marked_base_domains >> simp[]) >>
  `~t.vs_halted` by metis_tac[target_subscript_marked_base_nonhalted] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by fs[ci_mono_def] >>
  drule target_index_outcome_mem >>
  disch_then (qspecl_then [`sn`, `ix`, `e`] mp_tac) >> simp[] >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  irule target_subscript_index_bind_outcome >>
  qexists `\key ee u.
    target_post ctx func cenv cx es sa sn s0 ee (PlaceR (MemoryPlace id path)) bvt rb u /\
    expr_post ctx func cenv cx e (mid with gas_obs := []) sm sn t ee key ix u /\
    u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next` >>
  pure_rewrite_tac[BETA_THM] >> reverse conj_tac >- (simp[] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(\key ee u. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  `sa.cs_next_var <= sn.cs_next_var /\ s0.vs_alloca_next <= u.vs_alloca_next` by
    decide_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  irule target_local_index_summary_mem >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_exec`)) >> simp[] >>
  qexistsl [`bvt`, `env`] >>
  goal_assum (drule_at Any) >> gvs[] >> metis_tac[]
QED

Theorem target_subscript_local_nopop_continuation_mem:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  target_root bt = NameTarget id /\
  ~supported_target_exists (\x. ?ty t. x = Pop ty t) (SubscriptTarget bt e) /\
  type_place_target env bt = SOME bvt /\
  subscript_vtype bvt (expr_type e) = SOME vt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  ci_mono sa sm /\ ci_mono sm sn /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  gas_marked_exec T (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL (PlaceR (MemoryPlace id path))) mid (OK t) /\
  target_post ctx func cenv cx es sa sm s0 (mid with gas_obs := [])
    (PlaceR (MemoryPlace id path)) bvt rb t /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  expr_sim_mem ctx func cenv cx (expr_type e) e (mid with gas_obs := []) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\key. extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript key)))
    (mid with gas_obs := [],t)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `!gs key ee. bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := gs) = (INL key,ee) ==>
    ?entry v. lookup_scopes id ee.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v` by
    (rpt gen_tac >> strip_tac >> drule target_subscript_marked_base_source >>
     disch_then (qspec_then `gs` assume_tac) >>
     drule_all target_subscript_local_index_live >> simp[] >> metis_tac[]) >>
  drule_all target_subscript_local_live_continuation_mem >> simp[]
QED
