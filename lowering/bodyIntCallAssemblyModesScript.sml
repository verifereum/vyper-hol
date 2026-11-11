Theory bodyIntCallAssemblyModes
Ancestors
  bodyIntCallAssemblyFrame bodyIntCallCompletedModes bodyIntCallCompletedFrame
  compileEnv exprLoweringProps loweringPosts venomExecSemantics venomState
  fragGasFocus fragGasPath finite_map list bodyIntCallEmitBoundary
  localPtrsProps emitHelper emitHelperProps intCallFrame words loweringStateRelDefs

Theorem void_return_endpoint:
  expr_has_effect e /\
  post_value_type ce e = expr_type e /\
  emit_void INVOKE ops si = ((),sb) /\ fn_has_code si sb func /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  ir.iret_values = [] /\ ir.iret_adopt_fmp = NONE /\
  expr_type e = NoneT /\ value_has_type NoneTV v /\
  stmt_state_rel ctx func ce cx es t /\
  state_rel other ce cx (ee with scopes := []) cs /\
  immutable_alloca_sep func ce cx (ee with scopes := es.scopes) t /\
  wb_frame ce es0 es sa s0 t /\
  (!id b sz. local_region ce es0.scopes s0 id b sz ==>
    local_region ce es.scopes t id b sz) /\
  (!id b sz aid off asz.
    local_region ce es.scopes t id b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < hi ==> regions_disjoint b sz off asz) /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < hi ==> regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) ==>
  ?k out. gas_path ctx func t (n + k) (OK out) /\
    vv_post ctx func ce cx e es0 sa sb s0 (ee with scopes := es.scopes) (Value v)
      (StackValue NoneT (Lit 0w)) out /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `bind_outputs [] ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) =
    SOME (merge_callee_state t cs)` by
    simp[bind_outputs_def, adopt_return_fmp_def] >>
  drule_all (SRULE [] (Q.INST [`outs` |-> `[]`] return_successor_frame)) >>
  strip_tac >>
  qexists_tac `0` >> simp[] >> irule void_completed_endpoint >> simp[] >>
  conj_tac >- (qexistsl_tac [`ops`,`si`] >> simp[]) >>
  qexistsl_tac [`callee`,`cs`,`entered`,`ir`] >> simp[]
QED

Theorem memory_return_endpoint:
  expr_has_effect e /\
  post_value_type ce e = expr_type e /\
  emit_void INVOKE ops si = ((),sb) /\ fn_has_code si sb func /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  ir.iret_values = [] /\ ir.iret_adopt_fmp = NONE /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ type_memory_size tv <= buf.buf_size /\
  eval_operand buf.buf_operand t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,buf.buf_size) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  val_in_memory tv v (w2n w) cs.vs_memory /\
  stmt_state_rel ctx func ce cx es t /\
  state_rel other ce cx (ee with scopes := []) cs /\
  immutable_alloca_sep func ce cx (ee with scopes := es.scopes) t /\
  wb_frame ce es0 es sa s0 t /\
  (!id b sz. local_region ce es0.scopes s0 id b sz ==>
    local_region ce es.scopes t id b sz) /\
  (!id b sz aid off asz.
    local_region ce es.scopes t id b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) ==>
  ?k out. gas_path ctx func t (n + k) (OK out) /\
    vv_post ctx func ce cx e es0 sa sb s0 (ee with scopes := es.scopes) (Value v)
      (LocatedValue (expr_type e) (base_ptr buf)) out /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `bind_outputs [] ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) =
    SOME (merge_callee_state t cs)` by
    simp[bind_outputs_def, adopt_return_fmp_def] >>
  drule_all (SRULE [] (Q.INST [`outs` |-> `[]`] return_successor_frame)) >>
  strip_tac >>
  qexists_tac `0` >> simp[] >> irule memory_completed_endpoint >> simp[] >>
  conj_tac >- (qexistsl_tac [`ops`,`si`] >> simp[]) >>
  qexistsl_tac [`aid`,`callee`,`cs`,`entered`,`ir`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!id b sz aid off asz. _` drule_all >>
  simp[regions_disjoint_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem multi_invoke_output_frame:
  emit_multi_op INVOKE ops nret si = (MAP Var outs,sj) /\
  local_ptrs_reserved ce si /\ sa.cs_next_var <= si.cs_next_var ==>
  EVERY (not_local_ptr ce scopes) outs /\
  EVERY (not_scope_ptr ce scopes) outs /\
  (!x. not_fresh_at sa x ==> ~MEM x outs)
Proof
  strip_tac >> drule emit_multi_op_result >> strip_tac >>
  qpat_x_assum `MAP Var outs = _`
    (mp_tac o AP_TERM ``MAP (\op. case op of Var x => x | _ => "")``) >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >> strip_tac >> gvs[] >>
  `EVERY (not_local_ptr ce scopes)
    (GENLIST (\i. "%" ++ toString (si.cs_next_var + i)) nret)` by
    (simp[EVERY_MEM, MEM_GENLIST] >> rpt strip_tac >> gvs[] >>
     irule local_ptrs_reserved_fresh >> goal_assum (drule_at Any) >> simp[]) >>
  fs[arithmeticTheory.ADD_COMM] >>
  conj_tac >- (fs[EVERY_MEM] >> metis_tac[not_local_ptr_scope]) >>
  simp[MEM_GENLIST] >> rpt strip_tac >> gvs[not_fresh_at_def] >>
  first_x_assum (qspec_then `si.cs_next_var + i` mp_tac) >> simp[]
QED

Theorem stack_return_endpoint:
  expr_has_effect e /\
  post_value_type ce e = expr_type e /\
  emit_multi_op INVOKE ops nret si = (results,sj) /\
  store_multi_results buf.buf_operand results 0 sj = ((),sb) /\
  fn_has_code si sj func /\ fn_has_code sj sb func /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  ir.iret_adopt_fmp = NONE /\ LENGTH ir.iret_values = nret /\ 0 < nret /\
  compile_alloc_buffer (32 * nret) st1 = (buf,st2) /\
  st2.cs_next_var <= si.cs_next_var /\
  local_ptrs_reserved ce si /\ sa.cs_next_var <= si.cs_next_var /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name))
    (expr_type e) /\
  value_has_type tv v /\ intret_vals_match tv v ir.iret_values /\
  eval_operand buf.buf_operand t = SOME (n2w off) /\
  FLOOKUP t.vs_allocas aid = SOME (off,buf.buf_size) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (?ai. MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_id = aid) /\
  stmt_state_rel ctx func ce cx es t /\
  state_rel other ce cx (ee with scopes := []) cs /\
  immutable_alloca_sep func ce cx (ee with scopes := es.scopes) t /\
  wb_frame ce es0 es sa s0 t /\
  (!id b sz. local_region ce es0.scopes s0 id b sz ==>
    local_region ce es.scopes t id b sz) /\
  (!id b sz aid off asz.
    local_region ce es.scopes t id b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) ==>
  ?k out. gas_path ctx func t (n + k) (OK out) /\
    vv_post ctx func ce cx e es0 sa sb s0 (ee with scopes := es.scopes) (Value v)
      (LocatedValue (expr_type e) (base_ptr buf)) out /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all emit_multi_invoke_instruction >> strip_tac >>
  `LENGTH outs = LENGTH ir.iret_values` by simp[] >>
  drule_all multi_outputs_return_state >>
  disch_then (qspecl_then [`t`,`cs`] strip_assume_tac) >>
  gvs[] >>
  drule_all multi_invoke_output_frame >>
  disch_then (qspec_then `es.scopes` strip_assume_tac) >>
  drule_all return_successor_frame >> strip_tac >>
  drule invoke_return_frame >> strip_tac >>
  drule_all compiled_return_buffer_geometry >> strip_tac >>
  `~MEM p outs` by
    (drule emit_multi_op_output_bounds >> simp[MEM_MAP] >> metis_tac[]) >>
  `eval_operand buf.buf_operand (u with vs_inst_idx := SUC t.vs_inst_idx) =
     SOME (n2w off)` by
    (simp[eval_operand_def] >>
     qpat_x_assum `!x. ~MEM x outs ==> _` drule >>
     gvs[eval_operand_def]) >>
  `immutable_alloca_sep func ce cx (ee with scopes := es.scopes)
     (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule immutable_alloca_sep_fields >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `si.cs_next_var <= sj.cs_next_var /\
   sj.cs_current_bb = si.cs_current_bb /\
   LENGTH sj.cs_current_insts = SUC (LENGTH si.cs_current_insts)` by
    (drule emit_multi_op_result >> strip_tac >> gvs[]) >>
  `u.vs_current_bb = t.vs_current_bb` by
    (qpat_x_assum `bind_outputs outs _ _ = SOME u` mp_tac >>
     simp[bind_outputs_def] >> strip_tac >>
     qspecl_then [`ZIP (outs,ir.iret_values)`,
       `adopt_return_fmp ir (merge_callee_state t cs)`]
       strip_assume_tac foldl_update_var_frame >>
     gvs[adopt_return_fmp_def, merge_callee_state_def]) >>
  `local_ptrs_reserved ce sj` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sj sb))` >>
  irule (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] stack_completed_endpoint) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_multi_op _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `bind_outputs _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `gas_path _ _ _ _ _`)) >> simp[] >>
  qexistsl_tac [`ai.inst_id`,`off`] >> simp[] >>
  conj_tac >- (qexists_tac `ai` >> simp[]) >>
  fs[eval_operand_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!id b sz aid off asz. _` drule >>
      simp[] >> disch_then (qspec_then `ai.inst_id` mp_tac) >>
      simp[regions_disjoint_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  gvs[eval_operand_def]
QED
