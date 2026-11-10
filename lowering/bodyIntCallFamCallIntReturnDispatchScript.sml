(* Compiler preparation for the concrete return witness. *)
Theory bodyIntCallFamCallIntReturnDispatch
Ancestors
  bodyIntCallFamCallIntReturnRun bodyIntCallFamCallIntReturnFrame
  bodyIntCallSeamDefs bodyIntCallCompilerBoundary
  bodyIntCallCompletedModes bodyIntCallAssemblyModes bodyIntCallAssemblyFrame
  bodyIntCallEmitBoundary valueTypingMemoryProps valueEncodingProofs exprSimProps
  emitHelperProps emitHelper exprLoweringProps compileEnv venomState
  venomExecSemantics loweringPosts exprSimDefs intCallFrame list finite_map

Theorem intcall_stack_return_prepare:
  compile_multi_vvs compile_expr ce es sa = (vals,s1) /\
  ci_mono s1 s2 /\
  compile_stage_intcall_args ce vals flags tys s2 = (args,si) /\
  emit_multi_op INVOKE ops nret si = (results,sj) /\
  store_multi_results buf results 0 sj = ((),sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  LENGTH ir.iret_values = nret ==>
  ?bb outs u.
    results = MAP Var outs /\ LENGTH outs = nret /\ ALL_DISTINCT outs /\
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME (mk_inst si.cs_next_id INVOKE ops outs) /\
    bind_outputs outs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
    MAP (\op. eval_operand op (u with vs_inst_idx := SUC t.vs_inst_idx)) results =
      MAP SOME ir.iret_values /\
    EVERY (not_local_ptr ce prev) outs /\ EVERY (not_scope_ptr ce prev) outs /\
    (!x. not_fresh_at sa x ==> ~MEM x outs) /\
    fn_has_code sj sb func /\ local_ptrs_reserved ce sj /\
    sa.cs_next_var <= sj.cs_next_var /\ s2.cs_next_var <= si.cs_next_var /\
    si.cs_next_var <= sj.cs_next_var /\
    (u with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb = sj.cs_current_bb /\
    (u with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = LENGTH sj.cs_current_insts /\
    (!x. MEM (Var x) results ==> not_fresh_at sj x)
Proof
  strip_tac >> drule_all intcall_stack_compiler_boundary >> strip_tac >>
  drule_all emit_multi_invoke_instruction >> strip_tac >>
  gvs[] >>
  drule_all multi_invoke_output_frame >>
  disch_then (qspec_then `prev` strip_assume_tac) >>
  `LENGTH outs = LENGTH ir.iret_values` by simp[] >>
  drule_all multi_outputs_return_state >>
  disch_then (qspecl_then [`t`,`cs`] strip_assume_tac) >>
  drule emit_multi_op_result >> strip_tac >>
  drule emit_multi_op_output_bounds >> strip_tac >>
  drule invoke_return_frame >> strip_tac >>
  `local_ptrs_reserved ce sj` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `u.vs_current_bb = t.vs_current_bb` by
    (qpat_x_assum `bind_outputs _ _ _ = SOME u` mp_tac >>
     simp[bind_outputs_def] >> strip_tac >>
     qspecl_then [`ZIP (outs,ir.iret_values)`,
       `adopt_return_fmp ir (merge_callee_state t cs)`]
       strip_assume_tac foldl_update_var_frame >>
     Cases_on `ir.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def, merge_callee_state_def]) >>
  `!x. not_fresh_at sa x ==> ~MEM x outs` by
    (rpt strip_tac >>
     `not_fresh_at si x` by
       (irule loweringShapeDefsTheory.not_fresh_at_mono >>
        goal_assum (drule_at Any) >> simp[]) >>
     gvs[MEM_MAP]) >>
  qexistsl [`outs`,`u`] >>
  simp[eval_operand_def, lookup_var_def] >>
  gvs[]
QED

(* Geometry at the restored successor, independent of the way it was reached. *)
Theorem intcall_return_buffer_prepare:
  compile_alloc_buffer (32 * nret) st1 = (buf,st2) /\
  st2.cs_next_var <= si.cs_next_var /\
  emit_multi_op INVOKE ops nret si = (results,sj) /\
  stmt_state_rel ctx func ce cx es s /\
  eval_operand buf.buf_operand s = SOME (n2w off) /\
  FLOOKUP s.vs_allocas aid = SOME (off,buf.buf_size) /\
  MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_id = aid /\
  immutable_alloca_sep func ce cx es s /\
  (!id lb lsz. local_region ce es.scopes s id lb lsz ==>
    regions_disjoint lb lsz off buf.buf_size) /\
  evaluate_type (get_tenv cx) cty = SOME tv /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name)) cty /\
  value_has_type tv v /\ intret_vals_match tv v ws /\ ws <> [] /\ LENGTH ws = nret /\
  allocas_above lo s /\ (!a k. P a k ==> a + k <= lo) ==>
  (?p. buf.buf_operand = Var p /\ not_fresh_at sj p) /\
  (!x. MEM (Var x) results ==> not_fresh_at sj x) /\
  buf.buf_size = 32 * LENGTH results /\
  type_memory_size tv = 32 * LENGTH results /\
  w2n (n2w off : bytes32) = off /\ off + 32 * LENGTH results < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n (n2w off : bytes32),32 * LENGTH results) /\
  val_footprint tv v <= 32 * LENGTH results /\
  (!id lb lsz. local_region ce es.scopes s id lb lsz ==>
    off + 32 * LENGTH results <= lb \/ lb + lsz <= off) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (32 * LENGTH results) io (type_memory_size itv)) /\
  (!a k. P a k ==> a + k <= off \/ off + 32 * LENGTH results <= a)
Proof
  strip_tac >> drule emit_multi_op_output_bounds >> strip_tac >>
  drule_all compiled_return_buffer_geometry >> strip_tac >>
  drule emit_multi_op_result >> strip_tac >>
  `si.cs_next_var <= sj.cs_next_var` by simp[] >>
  `?p. buf.buf_operand = Var p /\ not_fresh_at sj p` by
    (qexists `p` >> simp[] >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all stack_return_memory_size >> strip_tac >>
  drule value_has_type_memory_wf >> strip_tac >>
  drule val_footprint_le >> strip_tac >>
  `FLOOKUP s.vs_allocas ai.inst_id = SOME (off,buf.buf_size)` by simp[] >>
  drule owned_alloca_immutable_separation >>
  disch_then (qspecl_then [`buf.buf_size`,`off`,`ai`] mp_tac) >>
  simp[] >> strip_tac >>
  fs[allocas_above_def, regions_disjoint_def] >>
  rpt conj_tac >> rpt strip_tac >> gvs[]
  >~ [`local_region _ _ _ _ _ _`] >- metis_tac[]
  >~ [`ce.ce_is_ctor`] >- metis_tac[] >>
  `lo <= off` by metis_tac[] >>
  `a + k <= lo` by metis_tac[] >> decide_tac
QED

Theorem intcall_bound_return_buffer:
  compile_alloc_buffer bsz st1 = (buf,st2) /\
  st2.cs_next_var <= si.cs_next_var /\
  emit_multi_op INVOKE ops nret si = (MAP Var outs,sj) /\
  stmt_state_rel ctx func ce cx es t /\
  eval_operand buf.buf_operand t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME (off,buf.buf_size) /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  immutable_alloca_sep func ce cx ee t /\
  (!id b sz. local_region ce ee.scopes (u with vs_inst_idx := idx) id b sz ==>
    local_region ce ee.scopes t id b sz) ==>
  eval_operand buf.buf_operand (u with vs_inst_idx := idx) = SOME w /\
  FLOOKUP (u with vs_inst_idx := idx).vs_allocas aid = SOME (off,buf.buf_size) /\
  immutable_alloca_sep func ce cx ee (u with vs_inst_idx := idx)
Proof
  strip_tac >> drule_all compiled_return_buffer_geometry >> strip_tac >>
  drule emit_multi_op_output_bounds >> strip_tac >>
  `~MEM p outs` by (gvs[MEM_MAP] >> metis_tac[]) >>
  drule invoke_return_frame >> strip_tac >>
  conj_tac
  >- (simp[eval_operand_def, lookup_var_def] >>
      qpat_x_assum `!x. ~MEM x outs ==> _` drule >>
      gvs[eval_operand_def, lookup_var_def]) >>
  simp[] >> irule immutable_alloca_sep_fields >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* Both zero-count modes land at the same explicit merge successor. *)
Theorem intcall_zero_return_prepare:
  compile_multi_vvs compile_expr ce es sa = (vals,s1) /\ ci_mono s1 s2 /\
  compile_stage_intcall_args ce vals flags tys s2 = (args,si) /\
  emit_void INVOKE ops si = ((),sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered nsteps (IntRet ir cs) /\ ir.iret_values = [] /\
  intcall_callee_exit other ce cx rtv rcn rb sa.cs_next_id sb.cs_next_id t
    res ee (IntRet ir cs) /\
  stmt_state_rel ctx func ce cx (es1 with scopes := prev) t /\
  immutable_alloca_sep func ce cx (ee with scopes := prev) t /\
  wb_frame ce es0 sa s0 t /\
  (!id b sz. local_region ce es0.scopes s0 id b sz ==>
    local_region ce prev t id b sz) /\
  (!id b sz aid off asz. local_region ce prev t id b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) /\
  allocas_above lo t /\ (!a k. P a k ==> a + k <= lo) ==>
  let s = merge_callee_state t cs with vs_inst_idx := SUC t.vs_inst_idx in
    gas_path ctx func t nsteps (OK s) /\
    s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx (ee with scopes := prev) s /\
    wb_frame ce es0 sa s0 s /\
    (!id b sz. local_region ce prev s id b sz <=> local_region ce prev t id b sz) /\
    allocas_above lo s /\ s.vs_allocas = t.vs_allocas /\
    t.vs_alloca_next <= s.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x t) /\
    (!a k. P a k ==> mem_bytes_at a k s.vs_memory = mem_bytes_at a k t.vs_memory)
Proof
  strip_tac >> drule_all intcall_void_compiler_boundary >> strip_tac >>
  `ir.iret_adopt_fmp = NONE` by
    fs[intcall_callee_exit_def, expr_exit_def] >>
  `bind_outputs [] ir.iret_values (adopt_return_fmp ir (merge_callee_state t cs)) =
    SOME (merge_callee_state t cs)` by simp[bind_outputs_def, adopt_return_fmp_def] >>
  drule_all (intcall_return_restored_frame |> Q.INST [`outs` |-> `[]`] |> SRULE []) >>
  disch_then (qspec_then `SUC t.vs_inst_idx` strip_assume_tac) >>
  drule_all (intcall_return_bound_resources |> Q.INST [`outs` |-> `[]`] |> SRULE []) >>
  disch_then (qspecl_then [`sa`,`SUC t.vs_inst_idx`] strip_assume_tac) >>
  drule_all void_outputs_counted_path >> strip_tac >>
  simp[] >>
  `sb.cs_current_bb = si.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH si.cs_current_insts)` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, emit_inst_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  gvs[merge_callee_state_def]
QED
