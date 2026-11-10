(* Memory-safe array header and the following element-loop entry. *)
Theory bodyMemArrayHeader
Ancestors
  exprSimAggregateLoops bodyDeclWordMemory gasOutcome fragGasMode
  exprLoweringProps emitHelperProps localPtrsProps stmtSimProps
  venomState venomMemDefs exprLowering compileEnv loweringSlice stmtSimDefs
  gasSummary fragGasPathMem loweringPosts

Theorem array_header_emit_entry:
  emit_void MSTORE [Var x; Lit (n2w len)] sa = ((),sm) ==>
  sm.cs_current_bb = sa.cs_current_bb /\
  LENGTH sm.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
  sm.cs_next_id = SUC sa.cs_next_id /\ sm.cs_next_var = sa.cs_next_var /\
  (local_ptrs_reserved ce sm <=> local_ptrs_reserved ce sa) /\
  (not_fresh_at sm z <=> not_fresh_at sa z)
Proof
  strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb /\
   LENGTH sm.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   sm.cs_next_id = SUC sa.cs_next_id /\ sm.cs_next_var = sa.cs_next_var` by
    gvs[emitHelperTheory.emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  simp[local_ptrs_reserved_def, not_fresh_at_def]
QED

Theorem array_header_path_mem[local]:
  emit_void MSTORE [Var x; Lit (n2w len)] sa = ((),sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  32 <= asz /\ b + asz < dimword (:256) /\
  sh = (mstore b (n2w len) s0 with vs_inst_idx := SUC s0.vs_inst_idx) ==>
  gas_marked_path T ctx func s0 0 (OK sh) /\ alloca_history func sh
Proof
  strip_tac >> drule array_header_emit_entry >> strip_tac >>
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  `b + 32 <= s0.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >>
     first_x_assum drule >> decide_tac) >>
  `b < dimword (:256)` by decide_tac >>
  drule annassign_word_mstore_path_mem >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`n2w len`, `n2w b`, `s0`, `ctx`] mp_tac) >>
  simp[eval_operand_def, gas_marked_path_def]
QED

Theorem array_header_mem_entry:
  emit_void MSTORE [Var x; Lit (n2w len)] sa = ((),sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa x /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  inst.inst_id < sa.cs_next_id /\ not_local_ptr ce es.scopes x /\
  lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  32 <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name tv v io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint io (type_memory_size tv) b 32) /\
  sh = (mstore b (n2w len) s0 with vs_inst_idx := SUC s0.vs_inst_idx) ==>
  gas_marked_path T ctx func s0 0 (OK sh) /\ alloca_history func sh /\
  stmt_state_rel ctx func ce cx es sh /\ locals_kept ce es s0 sh /\
  ~sh.vs_halted /\ sh.vs_current_bb = sm.cs_current_bb /\
  sh.vs_inst_idx = LENGTH sm.cs_current_insts /\
  lookup_var x sh = SOME (n2w b) /\
  FLOOKUP sh.vs_allocas inst.inst_id = SOME (b,asz) /\
  sh.vs_allocas = s0.vs_allocas /\ sh.vs_alloca_next = s0.vs_alloca_next /\
  local_ptrs_reserved ce sm /\ not_fresh_at sm x /\
  inst.inst_id < sm.cs_next_id /\
  mem_word_at b sh.vs_memory = n2w len /\
  (!p n. p+n <= b \/ b+32 <= p ==>
    mem_bytes_at p n sh.vs_memory = mem_bytes_at p n s0.vs_memory)
Proof
  strip_tac >>
  drule_all array_header_path_mem >> strip_tac >>
  drule array_header_emit_entry >>
  disch_then (qspecl_then [`x`, `ce`] strip_assume_tac) >>
  drule_all array_header_store_boundary >>
  disch_then (qspec_then `n2w len` strip_assume_tac) >>
  `stmt_state_rel ctx func ce cx es sh` by simp[stmt_state_rel_inst_idx] >>
  gvs[locals_kept_def, mstore_def, lookup_var_def] >>
  metis_tac[]
QED
