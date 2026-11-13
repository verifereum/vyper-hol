(* The tuple compiler emits MCOPY even for an empty aggregate cell. *)
Theory extcallEmptyStoreMemory
Ancestors
  extcallStoreCellMemory exprSimBufferStore memoryReadProps
  fragExecMem fragGasPathMem exprLoweringProps emitHelperProps
  loweringPosts compileEnv venomExecSemantics venomState venomInst list stmtReasonMemory instMemFrontier
  exprSimMemUnwrap venomMemProps

Theorem extcall_empty_copy_mem:
  emit_void MCOPY [dst; src; Lit 0w] sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    stmt_state_rel ctx func ce cx es z /\ alloca_history func z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    z.vs_vars = s.vs_vars /\ z.vs_allocas = s.vs_allocas /\
    z.vs_alloca_next = s.vs_alloca_next /\
    contract_storage z = contract_storage s /\
    contract_transient z = contract_transient s /\
    z.vs_data_section = s.vs_data_section /\ z.vs_labels = s.vs_labels /\
    (!off len. mem_bytes_at off len z.vs_memory =
      mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s =
     OK (mcopy (w2n d) (w2n a) 0 s)` by
    (asm_rewrite_tac [] >> irule run_inst_seq_sing_ok >>
     simp[step_mcopy_eq,eval_operand_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    simp[run_inst_seq_mem_ok_last,below_frontier_MCOPY,eval_operand_def] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
       ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def,is_terminator_def] >>
  drule_all straight_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `!off len. mem_bytes_at off len (mcopy (w2n d) (w2n a) 0 s).vs_memory =
     mem_bytes_at off len s.vs_memory` by
    simp[GSYM read_memory_eq_mem_bytes_at,read_memory_mcopy_zero] >>
  `(mcopy (w2n d) (w2n a) 0 s with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s` by
    simp[mcopy_def,write_memory_with_expansion_def] >>
  `!x. lookup_var x (mcopy (w2n d) (w2n a) 0 s) = lookup_var x s` by
    simp[mcopy_def,write_memory_with_expansion_def,lookup_var_def] >>
  `LENGTH s.vs_memory <= LENGTH (mcopy (w2n d) (w2n a) 0 s).vs_memory` by
    (simp[mcopy_def,LENGTH_write_memory_with_expansion,arithmeticTheory.MAX_DEF] >>
     decide_tac) >>
  `stmt_state_rel ctx func ce cx es (mcopy (w2n d) (w2n a) 0 s)` by
    (irule buffer_store_state_frame >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ s`)) >>
     qexistsl_tac [`0`,`0`,`sa`] >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  qexists_tac `mcopy (w2n d) (w2n a) 0 s with
     vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx] >>
  simp[mcopy_def,write_memory_with_expansion_def,
       contract_storage_def,contract_transient_def] >> metis_tac[]
QED
