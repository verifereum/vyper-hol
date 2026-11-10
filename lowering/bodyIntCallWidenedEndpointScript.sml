Theory bodyIntCallWidenedEndpoint
Ancestors
  bodyIntCallWidenedStore bodyIntCallCompletedModes
  bodyIntCallAssemblyFrame bodyIntCallAssemblyModes bodyIntCallCompilerBoundary
  intCallFrame arithmetic venomMemDefs loweringHalt compileEnv exprLoweringProps venomState venomExecSemantics
  fragGasPath fragGasFocus emitHelperProps emitHelper list valueTypingMemoryProps vyperValue
  bodyIntCallEmitBoundary valueEncodingProofs bodyIntCallCompletedPath exprSimProps loweringPosts

Theorem owned_endpoint_index_region[local]:
  local_region ce scopes (z with vs_inst_idx := k) id lb lsz =
  local_region ce scopes z id lb lsz
Proof
  simp[local_region_def, lookup_var_def]
QED

Theorem stack_completed_owned:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  bind_outputs inst.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  s = (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  emit_multi_op INVOKE ops nret si = (results,sj) /\
  store_multi_results buf.buf_operand results 0 sj = ((),sb) /\
  fn_has_code sj sb func /\
  s.vs_current_bb = sj.cs_current_bb /\
  s.vs_inst_idx = LENGTH sj.cs_current_insts /\
  compile_alloc_buffer (32 * nret) st1 = (buf,st2) /\
  st2.cs_next_var <= sj.cs_next_var /\
  local_ptrs_reserved ce sj /\ sa.cs_next_var <= sj.cs_next_var /\
  evaluate_type (get_tenv cx) cty = SOME tv /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name)) cty /\
  value_has_type tv v /\ intret_vals_match tv v ir.iret_values /\
  LENGTH ir.iret_values = nret /\ 0 < nret /\
  MAP (\op. eval_operand op s) results = MAP SOME ir.iret_values /\
  stmt_state_rel ctx func ce cx es' s /\ wb_frame ce es0 es' sa s0 s /\
  eval_operand buf.buf_operand s = SOME (n2w off) /\
  FLOOKUP s.vs_allocas aid = SOME (off,buf.buf_size) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (?ai. MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_id = aid) /\
  immutable_alloca_sep func ce cx es' s /\
  (!id lb lsz. local_region ce es'.scopes s id lb lsz ==>
    off + buf.buf_size <= lb \/ lb + lsz <= off) /\
  (!id lb lsz. local_region ce es0.scopes s0 id lb lsz ==>
    local_region ce es'.scopes s id lb lsz) ==>
  ?out. gas_path ctx func t
      (n + LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sj sb)))
      (OK out) /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx es' out /\ wb_frame ce es0 es' sa s0 out /\
    eval_operand buf.buf_operand out = SOME (n2w off) /\
    val_in_memory tv v off out.vs_memory /\
    FLOOKUP out.vs_allocas aid = SOME (off,buf.buf_size) /\
    val_footprint tv v <= buf.buf_size /\
    (!id lb lsz. local_region ce es'.scopes out id lb lsz ==>
      off + buf.buf_size <= lb \/ lb + lsz <= off)
Proof
  strip_tac >> drule emit_multi_op_output_bounds >> strip_tac >>
  drule_all compiled_return_buffer_geometry >> strip_tac >>
  `ir.iret_values <> []` by (strip_tac >> gvs[]) >>
  `val_footprint tv v <= 32 * LENGTH results` by
    (drule_all stack_return_memory_size >> strip_tac >>
     drule value_has_type_memory_wf >> strip_tac >>
     drule val_footprint_le >> simp[]) >>
  `FLOOKUP s.vs_allocas ai.inst_id = SOME (off,buf.buf_size)` by metis_tac[] >>
  drule owned_alloca_immutable_separation >> strip_tac >>
  `?z. run_inst_seq (emitted_insts sj sb) s = OK z /\
    (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    stmt_state_rel ctx func ce cx es' z /\ wb_frame ce es0 es' sa s0 z /\
    eval_operand buf.buf_operand z = SOME (n2w off) /\
    val_in_memory tv v (w2n (n2w off : bytes32)) z.vs_memory /\
    FLOOKUP z.vs_allocas aid = SOME (w2n (n2w off : bytes32),32 * LENGTH results) /\
    (!id lb lsz. local_region ce es'.scopes z id lb lsz ==>
      w2n (n2w off : bytes32) + 32 * LENGTH results <= lb \/
      lb + lsz <= w2n (n2w off : bytes32))` by
    (irule stack_buffer_run_owned >> simp[] >>
     rpt conj_tac >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.regions_disjoint_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `gas_path ctx func t n (OK s)` by
    (drule_all invoke_intret_counted_path >> simp[]) >>
  `~s.vs_halted` by (drule gas_path_normal >> simp[]) >>
  drule_all store_run_counted_endpoint >> strip_tac >>
  qexists_tac `z with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >> conj_tac
  >- (irule gas_path_then >> goal_assum (drule_at Any) >> simp[]) >>
  simp[exprSimRawCallCalldataTheory.raw_call_wb_frame_inst_idx, owned_endpoint_index_region,
       stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem physical_source_return_dispatch:
  !nret.
  compile_multi_vvs compile_expr ce es sa = (vals,s1) /\
  compile_stage_intcall_args ce vals flags tys s2 = (args,si) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  (nret = 0 /\ cty = NoneT ==>
    s2 = s1 /\ (?u. emit_void INVOKE (Label lbl::args) si = (u,sb)) /\
    vv = StackValue cty (Lit 0w)) /\
  (0 < nret \/ cty <> NoneT ==>
    ?buf aid off.
      compile_alloc_buffer (if 0 < nret then 32 * nret else rbs) s1 = (buf,s2) /\
      vv = LocatedValue cty (base_ptr buf) /\
      eval_operand buf.buf_operand t = SOME (n2w off) /\
      FLOOKUP t.vs_allocas aid = SOME (off,buf.buf_size) /\
      (?ai. MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_id = aid) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
      (0 < nret ==>
        ?results sj u. emit_multi_op INVOKE (Label lbl::args) nret si = (results,sj) /\
          store_multi_results buf.buf_operand results 0 sj = (u,sb)) /\
      (nret = 0 ==>
        (?u. emit_void INVOKE (Label lbl::buf.buf_operand::args) si = (u,sb)) /\
        (w:256 word) = n2w off /\ type_memory_size tv <= buf.buf_size)) /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  ir.iret_adopt_fmp = NONE /\ LENGTH ir.iret_values = nret /\
  (nret = 0 /\ cty <> NoneT ==> val_in_memory tv v (w2n w) cs.vs_memory) /\
  evaluate_type (get_tenv cx) cty = SOME tv /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (0 < nret ==> 0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name)) cty) /\
  value_has_type tv v /\ intret_vals_match tv v ir.iret_values /\
  stmt_state_rel ctx func ce cx (es1 with scopes := prev) t /\
  state_rel other ce cx (ee with <|scopes := []; gas_obs := []|>) cs /\
  immutable_alloca_sep func ce cx (ee with scopes := prev) t /\
  wb_frame ce es0 (es1 with scopes := prev) sa s0 t /\
  (!id b sz. local_region ce es0.scopes s0 id b sz ==>
    local_region ce prev t id b sz) /\
  (!id b sz aid off asz.
    local_region ce prev t id b sz /\ FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) ==>
  ?k out. gas_path ctx func t (n + k) (OK out) /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx (ee with <|scopes := prev; gas_obs := []|>) out /\
    wb_frame ce es0 (ee with <|scopes := prev; gas_obs := []|>) sa s0 out /\
    ((cty = NoneT /\ nret = 0 /\ vv = StackValue NoneT (Lit 0w) /\ v = NoneV) \/
     (?buf aid off. vv = LocatedValue cty (base_ptr buf) /\
       eval_operand buf.buf_operand out = SOME (n2w off) /\
       val_in_memory tv v off out.vs_memory /\
       FLOOKUP out.vs_allocas aid = SOME (off,buf.buf_size) /\
       sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
       val_footprint tv v <= buf.buf_size /\
       (!id lb lsz. local_region ce prev out id lb lsz ==>
         off + buf.buf_size <= lb \/ lb + lsz <= off)))
Proof
  gen_tac >> strip_tac >> Cases_on `nret = 0`
  >- (`ir.iret_values = []` by (Cases_on `ir.iret_values` >> fs[]) >>
      Cases_on `cty = NoneT`
      >- suspend "void" >>
      suspend "memory") >>
  suspend "stack"
QED

Resume physical_source_return_dispatch[void]:
  qpat_x_assum `_ ==> s2 = s1 /\ _` mp_tac >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
  `ci_mono s1 s1` by simp[ci_mono_refl] >>
  drule_all intcall_void_compiler_boundary >> strip_tac >>
  `bind_outputs [] ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) =
    SOME (merge_callee_state t cs)` by
    simp[bind_outputs_def, adopt_return_fmp_def] >>
  `immutable_alloca_sep func ce cx
      (ee with <|scopes := prev; gas_obs := []|>) t` by
    (irule immutable_alloca_sep_fields >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  drule_all (Q.INST [`es` |-> `es1 with scopes := prev`,
      `ee` |-> `ee with gas_obs := []`, `outs` |-> `[]`]
      (SPEC_ALL return_successor_frame) |> SIMP_RULE (srw_ss()) [] |> GEN_ALL) >>
  strip_tac >> drule_all void_outputs_counted_path >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  qexistsl_tac [`0`,`merge_callee_state t cs with vs_inst_idx := SUC t.vs_inst_idx`] >>
  gvs[] >>
  qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
  simp[emit_void_def, emit_inst_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  disch_then (SUBST1_TAC o SYM) >> simp[]
QED

Resume physical_source_return_dispatch[memory]:
  qpat_x_assum `0 < nret \/ _ ==> _` mp_tac >>
  simp[] >> strip_tac >> gvs[] >>
  `ci_mono s1 s2` by
    (qspecl_then [`rbs`,`s1`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  drule_all intcall_void_compiler_boundary >> strip_tac >>
  `bind_outputs [] ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) =
    SOME (merge_callee_state t cs)` by
    simp[bind_outputs_def, adopt_return_fmp_def] >>
  `immutable_alloca_sep func ce cx
      (ee with <|scopes := prev; gas_obs := []|>) t` by
    (irule immutable_alloca_sep_fields >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  drule_all (Q.INST [`es` |-> `es1 with scopes := prev`,
      `ee` |-> `ee with gas_obs := []`, `outs` |-> `[]`]
      (SPEC_ALL return_successor_frame) |> SIMP_RULE (srw_ss()) [] |> GEN_ALL) >>
  strip_tac >> drule_all void_outputs_counted_path >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  qexistsl_tac [`0`,`merge_callee_state t cs with vs_inst_idx := SUC t.vs_inst_idx`] >>
  gvs[] >> conj_tac
  >- (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
      simp[emit_void_def, emit_inst_def, fresh_id_def, emit_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `off < dimword (:256)` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac [stmt_state_rel_def] >> strip_tac >>
     drule alloca_room_next_lt >>
     fs[alloca_inv_def, alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. _`
       (qspecl_then [`ai.inst_id`,`off`,`buf.buf_size`] mp_tac) >>
     simp[] >> decide_tac) >>
  qexistsl_tac [`buf`,`ai.inst_id`,`off`] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  fs[] >>
  simp[merge_callee_state_def, eval_operand_def, lookup_var_def] >>
  conj_tac >- metis_tac[eval_operand_def, lookup_var_def] >>
  conj_tac >- metis_tac[value_has_type_memory_wf, val_footprint_le, LESS_EQ_TRANS] >>
  rpt strip_tac >>
  qpat_x_assum `!k. stmt_state_rel _ _ _ _ _ _ /\ _` (qspec_then `SUC (LENGTH si.cs_current_insts)` strip_assume_tac) >>
  fs[regions_disjoint_def] >> metis_tac[ADD_COMM]
QED

Resume physical_source_return_dispatch[stack]:
  `0 < nret` by decide_tac >>
  qpat_x_assum `0 < nret \/ _ ==> _` mp_tac >> simp[] >> strip_tac >>
  gvs[] >>
  `ci_mono s1 s2` by
    (qspecl_then [`32 * LENGTH ir.iret_values`,`s1`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  drule_all intcall_stack_compiler_boundary >> strip_tac >>
  drule_all emit_multi_invoke_instruction >> strip_tac >>
  `LENGTH outs = LENGTH ir.iret_values` by simp[] >>
  drule_all multi_outputs_return_state >>
  disch_then (qspecl_then [`t`,`cs`] strip_assume_tac) >> gvs[] >>
  drule_all multi_invoke_output_frame >>
  disch_then (qspec_then `prev` strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> ~MEM x outs` by
    (drule emit_multi_op_output_bounds >> strip_tac >>
     rpt strip_tac >>
     `not_fresh_at si x` by
       (irule loweringShapeDefsTheory.not_fresh_at_mono >> goal_assum (drule_at Any) >> simp[]) >>
     qpat_x_assum `!x. not_fresh_at si x ==> _` drule >> simp[MEM_MAP]) >>
  `immutable_alloca_sep func ce cx
      (ee with <|scopes := prev; gas_obs := []|>) t` by
    (irule immutable_alloca_sep_fields >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  drule_all (Q.INST [`es` |-> `es1 with scopes := prev`,
      `ee` |-> `ee with gas_obs := []`]
      (SPEC_ALL return_successor_frame) |> SIMP_RULE (srw_ss()) [] |> GEN_ALL) >>
  strip_tac >>
  drule invoke_return_frame >> strip_tac >>
  drule_all compiled_return_buffer_geometry >> strip_tac >>
  `~MEM p outs` by
    (drule emit_multi_op_output_bounds >> simp[MEM_MAP] >> metis_tac[]) >>
  `eval_operand buf.buf_operand (u with vs_inst_idx := SUC t.vs_inst_idx) =
     SOME (n2w off)` by
    (simp[eval_operand_def] >>
     qpat_x_assum `!x. ~MEM x outs ==> _` drule >> gvs[eval_operand_def]) >>
  `immutable_alloca_sep func ce cx (ee with <|scopes := prev; gas_obs := []|>)
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
  `?out. gas_path ctx func t
      (n + LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sj sb))) (OK out) /\
      out.vs_current_bb = sb.cs_current_bb /\
      out.vs_inst_idx = LENGTH sb.cs_current_insts /\
      stmt_state_rel ctx func ce cx (ee with <|scopes := prev; gas_obs := []|>) out /\
      wb_frame ce es0 (ee with <|scopes := prev; gas_obs := []|>) sa s0 out /\
      eval_operand buf.buf_operand out = SOME (n2w off) /\
      val_in_memory tv v off out.vs_memory /\
      FLOOKUP out.vs_allocas ai.inst_id = SOME (off,buf.buf_size) /\
      val_footprint tv v <= buf.buf_size /\
      (!id lb lsz. local_region ce prev out id lb lsz ==>
        off + buf.buf_size <= lb \/ lb + lsz <= off)` by
    (irule (Q.INST [`es'` |-> `ee with <|scopes := prev; gas_obs := []|>`]
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
         qpat_x_assum `!id b sz aid off asz. _`
           (qspecl_then [`id`,`lb`,`lsz`,`ai.inst_id`,`off`,`buf.buf_size`] mp_tac) >>
         simp[regions_disjoint_def] >> metis_tac[ADD_COMM]) >>
     gvs[eval_operand_def]) >>
  qexists_tac `out` >> simp[] >>
  qexistsl_tac [`buf`,`ai.inst_id`,`off`] >> simp[] >> gvs[]
QED

Finalise physical_source_return_dispatch
