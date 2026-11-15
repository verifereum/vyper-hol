Theory bodyIntCallNrStack
Ancestors
  bodyIntCallWidenedEndpoint bodyIntCallAssemblyModes bodyIntCallAssemblyFrame
  bodyIntCallCompletedModes bodyIntCallCompilerBoundary exprLoweringProps bodyIntCallEmitBoundary
  compileEnv emitHelper emitHelperProps intCallFrame venomExecSemantics venomState
  fragGasPath fragGasFocus loweringPosts loweringStateRelDefs vyperTyping
  valueTypingMemoryProps valueEncodingProofs exprSimProps list finite_map

Theorem nr_stack_physical_endpoint:
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
  evaluate_type (get_tenv cx) cty = SOME tv /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name)) cty /\
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
  ?out. gas_path ctx func t
      (n + LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sj sb))) (OK out) /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx (ee with scopes := es.scopes) out /\
    wb_frame ce es0 (ee with scopes := es.scopes) sa s0 out /\
    eval_operand buf.buf_operand out = SOME (n2w off) /\
    val_in_memory tv v off out.vs_memory /\
    FLOOKUP out.vs_allocas aid = SOME (off,buf.buf_size) /\
    val_footprint tv v <= buf.buf_size /\
    (!id lb lsz. local_region ce es.scopes out id lb lsz ==>
      off + buf.buf_size <= lb \/ lb + lsz <= off)
Proof
  strip_tac >> drule_all emit_multi_invoke_instruction >> strip_tac >>
  `LENGTH outs = LENGTH ir.iret_values` by simp[] >>
  drule_all multi_outputs_return_state >>
  disch_then (qspecl_then [`t`,`cs`] strip_assume_tac) >> gvs[] >>
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
  suspend "store"
QED

Resume nr_stack_physical_endpoint[store]:
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
  irule (Q.INST [`es'` |-> `ee with scopes := es.scopes`]
    (SPEC_ALL stack_completed_owned) |> SIMP_RULE (srw_ss()) [] |> GEN_ALL) >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (qexists_tac `ai` >> simp[]) >>
  conj_tac >- (qexists_tac `cty` >> simp[]) >>
  goal_assum (drule_at (Pat `gas_path _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_multi_op _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `bind_outputs _ _ _ = _`)) >>
  simp[eval_operand_def] >>
  qpat_x_assum `!k. stmt_state_rel _ _ _ _ _ _ /\ _`
    (qspec_then `SUC (LENGTH si.cs_current_insts)` strip_assume_tac) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!id b sz aid off asz. _` drule >>
      simp[regions_disjoint_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  gvs[eval_operand_def]
QED

Finalise nr_stack_physical_endpoint
