(* Return-selected physical-layout bounds at expression endpoints. *)
Theory internalReturnValueEndpointMem
Ancestors
  bodyMemoryDefs externalNormalizePremises exprSimProps loweringPosts exprSimMemDefs
  exprSimMemUnwrap bodyRhsRoomMemory stmtReasonVvMemory
  exprLowering emitHelper fragGasPathMem exprSimUnwrap exprSimUnwrapProps
  exprLoweringProps exprOperandVar emitHelperProps loweringSlice
  vyperEvalExprPreservesScopesDom fragGasPath fragExec exprSimDefs
  exprSimSubscriptMap
  vyperState context compileEnv gasOutcome gasSummary fragGasMode exprSimMemorySource list

Theorem internal_return_nonbytes_value_endpoint_mem:
  expr_sim_mem ctx func ce cx ct e es /\
  lower_value compile_expr ce ct e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\
      expr_post ctx func ce cx e es sa sb s0 ee v op t /\
      expr_store_bound cx (expr_type e) v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      (!sty stv. post_value_type ce e = sty /\
        evaluate_type (get_tenv cx) sty = SOME stv /\
        value_has_type stv v /\ ~is_bytestring_type sty ==>
        expr_store_bound cx sty v op t /\
        (~is_word_type sty ==>
         ?sw. eval_operand op t = SOME sw /\
           (type_memory_size stv = 0 \/
            w2n sw + type_memory_size stv <= t.vs_alloca_next) /\
           w2n sw + type_memory_size stv < dimword (:256))))
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then drule_all >> strip_tac >>
  irule gas_outcome_post_mono >> goal_assum (drule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qexists_tac `v` >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type (post_value_type ce e)`
  >- simp[expr_store_bound_word] >>
  `stmt_state_rel ctx func ce cx ee t /\
   expr_val_at ce cx (post_value_type ce e) sa sb ee v op t` by fs[expr_post_def] >>
  drule_all normalize_source_window >> strip_tac >>
  reverse conj_tac >- (simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `val_wf stv v` by fs[expr_val_at_def] >>
  simp[expr_store_bound_def] >> rpt strip_tac >> gvs[] >>
  drule val_store_size_le >> strip_tac >> decide_tac
QED

(* A selected layout survives an identity unwrap; materialisation allocates
   the annotation's capacity, which must cover the selected layout. *)
Theorem internal_return_unwrap_selected_capacity[local]:
  post_value_type ce e = expr_type e /\
  unwrap_value ce vv sm = (op,sb) /\
  local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~is_word_type (expr_type e) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    type_memory_bytes ce (expr_type e) = type_memory_size tv /\
    type_memory_size tv < 2 ** 64) /\
  (vv_location vv <> SOME LocMemory ==> !ltv tv.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    type_memory_size ltv <= type_memory_size tv) /\
  vv_post ctx func ce cx e es sa sm s0 ee (Value v) vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_path_mem ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    expr_store_bound cx (expr_type e) v op u /\
    (!sw ltv. eval_operand op u = SOME sw /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv ==>
      type_memory_size ltv = 0 \/
      w2n sw + type_memory_size ltv <= u.vs_alloca_next) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >> qexists_tac `s` >>
      simp[cj 1 gas_path_mem_rules] >>
      conj_tac >- metis_tac[expr_post_of_vv_post_stack] >>
      gvs[vv_store_bound_def, expr_store_bound_def, read_result_def, return_def] >>
      metis_tac[]) >>
  rename1 `LocatedValue vt p` >>
  Cases_on `p.ptr_location = LocCalldata` >- gvs[vv_post_calldata] >>
  Cases_on `p.ptr_location = LocMemory`
  >- (`~is_word_type vt` by
        gvs[vv_post_def, vv_holds_def, valueCopyBytesTheory.is_bytestring_word_type] >>
      gvs[unwrap_value_def, comp_return_def] >> qexists_tac `s` >>
      simp[cj 1 gas_path_mem_rules] >>
      conj_tac >- metis_tac[expr_post_of_vv_post_memory] >>
      gvs[vv_store_bound_def, expr_store_bound_def, read_result_def, return_def] >>
      metis_tac[]) >>
  `vt = expr_type e` by
    (Cases_on `p.ptr_location` >> gvs[vv_post_def, vv_holds_def]) >>
  qpat_x_assum `vt = expr_type e` SUBST_ALL_TAC >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_copy_capacity_path_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- (Cases_on `p.ptr_location` >> gvs[vv_operand_def]) >>
  strip_tac >> qexists_tac `u` >> simp[] >>
  rpt strip_tac >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by
    fs[optionTheory.IS_SOME_EXISTS] >>
  `type_memory_size ltv <= type_memory_size tv` by
    (qpat_x_assum `_ ==> !ltv tv. _` irule >> simp[vv_location_def]) >>
  qpat_x_assum `~is_word_type _ ==> vv_store_bound _ _ _ _ _ _ _` mp_tac >>
  simp[vv_store_bound_def, vv_location_def, vv_operand_def,
       contextTheory.mk_ptr_def] >>
  strip_tac >> first_x_assum (qspecl_then [`tv`, `sw`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem internal_return_selected_marked_read_mem[local]:
  post_value_type ce e = expr_type e /\
  unwrap_value ce vv sm = (op,sb) /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~is_word_type (expr_type e) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    type_memory_bytes ce (expr_type e) = type_memory_size tv /\
    type_memory_size tv < 2 ** 64) /\
  (vv_location vv <> SOME LocMemory ==> !ltv tv.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    type_memory_size ltv <= type_memory_size tv) /\
  vv_post ctx func ce cx e es sa sm s0 ee rv vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee rv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec T (ctx,func) (read_result cx rv) (ee,s)
          [] (INL v) ee (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    expr_store_bound cx (expr_type e) v op u /\
    (!sw ltv. eval_operand op u = SOME sw /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv ==>
      type_memory_size ltv = 0 \/
      w2n sw + type_memory_size ltv <= u.vs_alloca_next) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> Cases_on `read_result cx rv ee` >> rename1 `_ = (res, ee')` >>
  `ee' = ee` by metis_tac[read_result_state] >> gvs[] >>
  reverse (Cases_on `res`) >- metis_tac[vv_post_failed_read] >>
  rename1 `read_result cx rv ee = (INL v, ee)` >>
  `vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) vv s` by
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
     rw[vv_store_bound_def] >> gvs[read_result_def, return_def] >>
     first_x_assum irule >> metis_tac[]) >>
  drule vv_post_read_result >> strip_tac >> gvs[] >> pop_assum kall_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) internal_return_unwrap_selected_capacity >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[] >>
  simp[gas_marked_exec_def, gas_marked_path_def] >>
  gvs[read_result_gas_obs, APPEND]
QED

Theorem internal_return_selected_value_outcome_mem:
  post_value_type ce e = expr_type e /\ ~is_word_type (expr_type e) /\
  expr_vv_sim_mem ctx func ce cx ct e es /\
  compile_expr ce ct e sa = (vv,sm) /\ unwrap_value ce vv sm = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    type_memory_bytes ce (expr_type e) = type_memory_size tv /\
    type_memory_size tv < 2 ** 64) /\
  (vv_location vv <> SOME LocMemory ==> !ltv tv.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    type_memory_size ltv <= type_memory_size tv) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\
      expr_post ctx func ce cx e es sa sb s0 ee v op t /\
      expr_store_bound cx (expr_type e) v op t /\
      (!sw ltv. eval_operand op t = SOME sw /\
        evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv ==>
        type_memory_size ltv = 0 \/
        w2n sw + type_memory_size ltv <= t.vs_alloca_next) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (drule (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then drule_all >> strip_tac >>
  irule gas_outcome_bind_result_exec >> goal_assum (drule_at Any) >>
  simp[] >>
  conj_tac >- (rpt strip_tac >> Cases_on `res`
    >- (Cases_on `r` >> gvs[expr_exit_def]) >>
    Cases_on `y` >> Cases_on `r` >> gvs[expr_exit_def] >>
    Cases_on `e'` >> gvs[expr_exit_def]) >>
  reverse conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) internal_return_selected_marked_read_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >> goal_assum (drule_at Any) >>
  gvs[]
QED
