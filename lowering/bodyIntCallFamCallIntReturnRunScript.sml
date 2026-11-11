(* Enrich the public owned-store witness before counting that same run. *)
Theory bodyIntCallFamCallIntReturnRun
Ancestors
  bodyIntCallFamCallIntReturnFrame bodyIntCallWidenedStore
  intCallResult compileEnv exprLoweringProps venomState
  finite_map list rich_list loweringPosts exprSimDefs intCallFrame

Theorem intcall_stack_buffer_run_resources:
  store_multi_results buf.buf_operand results 0 si = ((),sb) /\
  local_ptrs_reserved ce si /\
  buf.buf_operand = Var p /\ not_fresh_at si p /\
  (!x. MEM (Var x) results ==> not_fresh_at si x) /\
  evaluate_type (get_tenv cx) cty = SOME tv /\ value_has_type tv v /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name)) cty /\
  intret_vals_match tv v ws /\ ws <> [] /\
  stmt_state_rel ctx func ce cx es' s /\ wb_frame ce es0 sa s0 s /\
  sa.cs_next_var <= si.cs_next_var /\
  eval_operand buf.buf_operand s = SOME w /\
  MAP (\op. eval_operand op s) results = MAP SOME ws /\
  w2n w + 32 * LENGTH results < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n w,32 * LENGTH results) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  val_footprint tv v <= 32 * LENGTH results /\
  (!n lb lsz. local_region ce es'.scopes s n lb lsz ==>
    w2n w + 32 * LENGTH results <= lb \/ lb + lsz <= w2n w) /\
  (!n lb lsz. local_region ce es0.scopes s0 n lb lsz ==>
    local_region ce es'.scopes s n lb lsz) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint (w2n w) (32 * LENGTH results) off
      (type_memory_size itv)) /\
  allocas_above lo s /\
  (!a k. P a k ==> a + k <= w2n w \/ w2n w + 32 * LENGTH results <= a) ==>
  ?u. run_inst_seq (emitted_insts si sb) s = OK u /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    stmt_state_rel ctx func ce cx es' u /\ wb_frame ce es0 sa s0 u /\
    eval_operand buf.buf_operand u = SOME w /\
    val_in_memory tv v (w2n w) u.vs_memory /\
    FLOOKUP u.vs_allocas aid = SOME (w2n w,32 * LENGTH results) /\
    (!n lb lsz. local_region ce es'.scopes u n lb lsz ==>
      w2n w + 32 * LENGTH results <= lb \/ lb + lsz <= w2n w) /\
    allocas_above lo u /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at si x ==> lookup_var x u = lookup_var x s) /\
    (!a k. P a k ==> mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >>
  drule_all stack_buffer_run_owned >> strip_tac >>
  rename1 `run_inst_seq _ s = OK u` >>
  `allocas_above lo u /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\
   (!x. not_fresh_at si x ==> lookup_var x u = lookup_var x s) /\
   (!a k. P a k ==> mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory)` by
    (irule intcall_store_results_resources >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`w2n w`,`buf.buf_operand`,`0`,`results`,`ws`] >>
     gvs[]) >>
  qexists `u` >> gvs[] >> metis_tac[]
QED

Theorem intcall_store_run_counted_resources:
  store_multi_results buf ops 0 si = ((),sb) /\
  fn_has_code si sb func /\ ~s.vs_halted /\
  s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts /\
  run_inst_seq (emitted_insts si sb) s = OK u /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  stmt_state_rel ctx func ce cx es' u /\ wb_frame ce es0 sa s0 u /\
  eval_operand buf u = SOME w /\ val_in_memory tv v (w2n w) u.vs_memory /\
  FLOOKUP u.vs_allocas aid = SOME (w2n w,32 * LENGTH ops) /\
  (!n lb lsz. local_region ce es'.scopes u n lb lsz ==>
    w2n w + 32 * LENGTH ops <= lb \/ lb + lsz <= w2n w) /\
  allocas_above lo u /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  (!x. not_fresh_at si x ==> lookup_var x u = lookup_var x s) /\
  (!a k. P a k ==> mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  gas_path ctx func s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts si sb)))
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  u.vs_current_bb = sb.cs_current_bb /\
  stmt_state_rel ctx func ce cx es' (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  wb_frame ce es0 sa s0 (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  eval_operand buf (u with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME w /\
  val_in_memory tv v (w2n w) (u with vs_inst_idx := LENGTH sb.cs_current_insts).vs_memory /\
  FLOOKUP (u with vs_inst_idx := LENGTH sb.cs_current_insts).vs_allocas aid =
    SOME (w2n w,32 * LENGTH ops) /\
  (!n lb lsz. local_region ce es'.scopes (u with vs_inst_idx := LENGTH sb.cs_current_insts) n lb lsz ==>
    w2n w + 32 * LENGTH ops <= lb \/ lb + lsz <= w2n w) /\
  allocas_above lo (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  (u with vs_inst_idx := LENGTH sb.cs_current_insts).vs_allocas = s.vs_allocas /\
  (u with vs_inst_idx := LENGTH sb.cs_current_insts).vs_alloca_next = s.vs_alloca_next /\
  (!x. not_fresh_at si x ==>
    lookup_var x (u with vs_inst_idx := LENGTH sb.cs_current_insts) = lookup_var x s) /\
  (!a k. P a k ==> mem_bytes_at a k (u with vs_inst_idx := LENGTH sb.cs_current_insts).vs_memory =
    mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >> drule_all store_run_counted_endpoint >> strip_tac >>
  fs[stmt_state_rel_inst_idx, wb_frame_def, local_region_def,
     allocas_above_def, eval_operand_def, lookup_var_def] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
