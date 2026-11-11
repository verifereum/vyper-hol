(* Allocation landings independent of previous fresh-register bindings. *)
Theory bodyIntCallWindowLanding
Ancestors
  bodyIntCallAllocatedForcing bodyIntCallWindowCopy
  bodyIntCallMaterializeLanding bodyIntCallProtectedAlloc exprSimAlloc exprSimPrecompiles
  placeMemoryPrimitiveForward context emitHelperProps exprLoweringProps
  compileEnv venomState venomInst fragGasMode instIdxIndep finite_map
  list rich_list words intCallFrame emitHelper entrySinkExtraction
  abiBuiltinAllocation venomExecSemantics
Libs
  pairLib

Theorem materialization_alloc_run_fields:
  compile_alloc_buffer sz sa = (buf,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK t /\ sz < dimword (:256) ==>
  t.vs_data_section = s.vs_data_section /\
  t.vs_immutables = s.vs_immutables /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  t.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id sz s).vs_allocas
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_def,
      step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def, eval_operand_def] >>
  gvs[AllCaseEqs(), update_var_def, FLOOKUP_UPDATE,
      abi_builtin_allocate_state_def]
QED

Theorem materialization_alloc_landing:
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) /\ allocas_above lo s /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    allocas_above lo u /\ u.vs_memory = s.vs_memory /\
    u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ s.vs_alloca_next <= u.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id sz s).vs_allocas /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!name b len. local_region ce es.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule_all materialization_alloc_run_fields >> strip_tac >>
  `t.vs_labels = s.vs_labels` by (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `allocas_above lo t` by (drule_all alloc_buffer_allocas_above >> simp[]) >>
  `lo <= w2n w` by (fs[allocas_above_def] >> metis_tac[]) >>
  `sm.cs_current_bb = sa.cs_current_bb /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sm) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sm)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >>
     gvs[fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def, emitted_insts_def,
         DROP_APPEND, mk_inst_def, is_terminator_def]) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `gas_marked_path F ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sm.cs_current_insts`, `w`] >>
  fs[stmt_state_rel_inst_idx, eval_op_inst_idx, allocas_above_def,
       local_region_def, lookup_var_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `q` >>
      gvs[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem materialization_alloc_window_landing:
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) /\ allocas_above lo s /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    allocas_above lo u /\ u.vs_memory = s.vs_memory /\
    u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ s.vs_alloca_next <= u.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!name b len. local_region ce es.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (!p k. Win p k ==> regions_disjoint p k (w2n w) sz) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >> drule_all materialization_alloc_landing >> strip_tac >>
  `!p k. Win p k ==> regions_disjoint p k (w2n w) sz` by
    (rpt strip_tac >>
     drule_at (Pos (el 2)) earlier_allocated_window_disjoint >>
     disch_then irule >>
     conj_tac
     >- (qexistsl_tac [`Win`, `s`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  qexistsl_tac [`u`, `w`] >> simp[] >> metis_tac[]
QED
