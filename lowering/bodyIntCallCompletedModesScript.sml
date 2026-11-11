Theory bodyIntCallCompletedModes
Ancestors
  bodyIntCallCompletedFrame bodyIntCallCompletedPath bodyIntCallRestoreResults
  bodyIntCallStorePath bodyIntCallStoreRun bodyIntCallEmitBoundary
  emitHelper emitHelperProps fragExec fragGasPath fragGasFocus
  compileEnv loweringPosts exprLoweringProps venomExecSemantics venomState
  venomInst list rich_list loweringHalt venomMemDefs context
  bodyIntCallReturnLayout exprSimProps valueEncoding valueEncodingProofs
  valueTypingMemoryProps vyperTyping loweringStateRelDefs

Theorem emit_void_invoke_instruction:
  emit_void INVOKE ops si = ((),sb) /\ fn_has_code si sb func /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts ==>
  ?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx =
      SOME (mk_inst si.cs_next_id INVOKE ops [])
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = si.cs_current_bb` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> simp[]
QED

Theorem void_outputs_counted_path:
  emit_void INVOKE ops si = ((),sb) /\ fn_has_code si sb func /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  ir.iret_values = [] /\ ir.iret_adopt_fmp = NONE ==>
  gas_path ctx func t n
    (OK (merge_callee_state t cs with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  strip_tac >> drule_all emit_void_invoke_instruction >> strip_tac >>
  irule invoke_intret_counted_path >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >>
  simp[mk_inst_def, bind_outputs_def, adopt_return_fmp_def]
QED

Theorem void_completed_endpoint:
  expr_has_effect e /\
  post_value_type ce e = expr_type e /\
  emit_void INVOKE ops si = ((),sb) /\ fn_has_code si sb func /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  ir.iret_values = [] /\ ir.iret_adopt_fmp = NONE /\
  expr_type e = NoneT /\ value_has_type NoneTV v /\
  stmt_state_rel ctx func ce cx es'
    (merge_callee_state t cs with vs_inst_idx := SUC t.vs_inst_idx) /\
  wb_frame ce es0 es' sa s0
    (merge_callee_state t cs with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?out. gas_path ctx func t n (OK out) /\
    vv_post ctx func ce cx e es0 sa sb s0 es' (Value v)
      (StackValue NoneT (Lit 0w)) out /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all void_outputs_counted_path >> strip_tac >>
  qexists_tac `merge_callee_state t cs with vs_inst_idx := SUC t.vs_inst_idx` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule void_invoke_return_post >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at Any) >> simp[merge_callee_state_def] >>
  qexistsl_tac [`ops`,`si`] >> simp[]
QED

Theorem memory_completed_endpoint:
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
  (!id lb lsz. local_region ce es'.scopes t id lb lsz ==>
    w2n w + buf.buf_size <= lb \/ lb + lsz <= w2n w) /\
  stmt_state_rel ctx func ce cx es'
    (merge_callee_state t cs with vs_inst_idx := SUC t.vs_inst_idx) /\
  wb_frame ce es0 es' sa s0
    (merge_callee_state t cs with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?out. gas_path ctx func t n (OK out) /\
    vv_post ctx func ce cx e es0 sa sb s0 es' (Value v)
      (LocatedValue (expr_type e) (base_ptr buf)) out /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all void_outputs_counted_path >> strip_tac >>
  qexists_tac `merge_callee_state t cs with vs_inst_idx := SUC t.vs_inst_idx` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule memory_invoke_return_post >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`ops`,`si`] >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem emit_multi_invoke_instruction:
  emit_multi_op INVOKE ops nret si = (results,sj) /\
  fn_has_code si sj func /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts ==>
  ?bb outs. results = MAP Var outs /\ LENGTH outs = nret /\
    ALL_DISTINCT outs /\
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx =
      SOME (mk_inst si.cs_next_id INVOKE ops outs)
Proof
  strip_tac >> drule emit_multi_op_result >> strip_tac >>
  `ALL_DISTINCT outs` by
    (simp[ALL_DISTINCT_GENLIST] >> rpt strip_tac >>
     gvs[ASCIInumbersTheory.toString_inj]) >>
  `?bb. lookup_block si.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH si.cs_current_insts) =
      SOME (mk_inst si.cs_next_id INVOKE ops outs)` by
    (drule fn_has_code_same_block >> simp[]) >>
  qexistsl_tac [`bb`,`outs`] >> simp[]
QED

Theorem multi_outputs_return_state:
  ALL_DISTINCT outs /\ LENGTH outs = LENGTH ir.iret_values ==>
  ?u. bind_outputs outs ir.iret_values
        (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
    MAP (\op. eval_operand op u) (MAP Var outs) = MAP SOME ir.iret_values
Proof
  strip_tac >>
  `?u. bind_outputs outs ir.iret_values
     (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u` by
    simp[bind_outputs_def] >>
  drule_all intCallStepTheory.bind_outputs_lookup >> strip_tac >>
  qexists_tac `u` >> simp[] >>
  simp[LIST_EQ_REWRITE, EL_MAP, eval_operand_def] >> metis_tac[]
QED

(* Composition keeps the actual store endpoint.  It does not infer a path
   from an existential fragment postcondition. *)
Theorem invoke_store_completed_endpoint:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  bind_outputs inst.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  store_multi_results buf results 0 si = ((),sb) /\
  fn_has_code si sb func /\
  s = (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts /\
  run_inst_seq (emitted_insts si sb) s = OK v /\
  (v with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  vv_post ctx func ce cx e es0 sa sb s0 es' raw vv v ==>
  ?out. gas_path ctx func t
      (n + LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts si sb)))
      (OK out) /\
    vv_post ctx func ce cx e es0 sa sb s0 es' raw vv out /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `gas_path ctx func t n (OK s)` by
    (drule_all invoke_intret_counted_path >> simp[]) >>
  `~s.vs_halted` by (drule gas_path_normal >> simp[]) >>
  drule_all store_run_counted_post >> strip_tac >>
  qexists_tac `out` >> simp[] >>
  irule gas_path_then >> goal_assum (drule_at Any) >> simp[]
QED

Theorem compiled_return_buffer_geometry:
  compile_alloc_buffer bsz st1 = (buf,st2) /\
  st2.cs_next_var <= si.cs_next_var /\
  stmt_state_rel ctx func ce cx es t /\
  FLOOKUP t.vs_allocas aid = SOME (off,buf.buf_size) ==>
  buf.buf_size = bsz /\
  off + bsz < dimword (:256) /\ w2n (n2w off : bytes32) = off /\
  ?p. buf.buf_operand = Var p /\ not_fresh_at si p
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  `off + buf.buf_size <= t.vs_alloca_next` by
    (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `t.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> qexistsl_tac [`ctx`,`func`] >>
     fs[stmt_state_rel_def]) >>
  simp[] >> gvs[not_fresh_at_def] >> rpt strip_tac >>
  qpat_x_assum `!n. _` (qspec_then `n` mp_tac) >> simp[] >> decide_tac
QED

Theorem owned_alloca_immutable_separation:
  immutable_alloca_sep func ce cx es t /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (off,sz) ==>
  (ce.ce_is_ctor ==> !name tv v io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off sz io (type_memory_size tv))
Proof
  rw[immutable_alloca_sep_def] >>
  qpat_x_assum `ce.ce_is_ctor ==> _` (mp_tac o UNDISCH) >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `!inst b sz. _` drule_all >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]
QED

Theorem uniform_type_memory_size_list:
  !tvs. EVERY (\tv. type_memory_size tv = sz) tvs ==>
    type_memory_size_list tvs = sz * LENGTH tvs
Proof
  Induct >> simp[type_memory_size_def, arithmeticTheory.MULT_SUC]
QED

Theorem stack_return_memory_size:
  sfields_tenv_consistent sf tenv /\
  evaluate_type tenv ty = SOME tv /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields sf name)) ty /\
  value_has_type tv v /\ intret_vals_match tv v ws /\ ws <> [] ==>
  type_memory_size tv = 32 * LENGTH ws
Proof
  strip_tac >> drule_all stack_return_value_layout >> strip_tac
  >- (drule_all word_tv_memory_size >> strip_tac >>
      drule_all intCallResultTheory.intret_vals_match_word_eq >> simp[])
  >- (gvs[] >>
      `EVERY (\etv. type_memory_size etv = 32) tvs` by
        (fs[EVERY_MEM] >> metis_tac[word_tv_memory_size]) >>
      drule uniform_type_memory_size_list >> strip_tac >>
      Cases_on `v` >> gvs[value_has_type_def] >>
      Cases_on `a` >> gvs[value_has_type_def, intret_vals_match_def,
        type_memory_size_def, LIST_REL_EL_EQN] >>
      drule values_have_types_length >> simp[]) >>
  gvs[] >>
  `EVERY (\etv. type_memory_size etv = 32) (MAP SND ftvs)` by
    (fs[EVERY_MEM] >> metis_tac[word_tv_memory_size]) >>
  drule uniform_type_memory_size_list >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, intret_vals_match_def,
    type_memory_size_def, type_memory_size_fields_sum,
    type_memory_size_list_sum, GSYM MAP_MAP_o, LIST_REL_EL_EQN] >>
  drule struct_has_type_values_have_types >>
  disch_then (mp_tac o MATCH_MP values_have_types_length) >> simp[]
QED

(* The stack mode starts from the restored caller predicates and the concrete
   bound-output state.  Buffer geometry and immutable separation are derived
   from its owned ALLOCA, not from a bound on constructor memory. *)
Theorem stack_completed_endpoint:
  expr_has_effect e /\
  post_value_type ce e = expr_type e /\
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
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name))
    (expr_type e) /\
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
    vv_post ctx func ce cx e es0 sa sb s0 es' (Value v)
      (LocatedValue (expr_type e) (base_ptr buf)) out /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
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
    vv_post ctx func ce cx e es0 sa sb s0 es' (Value v)
      (LocatedValue (expr_type e) (base_ptr buf)) z /\
    (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s` by
    (irule stack_buffer_run_post >> simp[] >>
     qexistsl_tac [`aid`,`results`,`ir.iret_values`] >>
     simp[] >> rpt strip_tac >> gvs[] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule invoke_store_completed_endpoint >>
  goal_assum (drule_at Any) >> conj_tac >- metis_tac[] >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED
