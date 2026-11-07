(* Counted raw-call finish paths after the external call. *)
Theory rawCallFinishPathMemory
Ancestors
  bodyMemRawCallFinish rawCallRevertPathMemory rawCallCountedRun
  exprSimRawCall exprSimRawCallCalldata fragGasPathMem fragGasSeqMem
  fragExec emitHelper loweringHalt builtinSimple context compileEnv exprLoweringProps venomExecSemantics
  venomState venomInst finite_map rich_list list
Libs
  monadsyntax

Theorem raw_call_failure_prefix_run[local]:
  emit_op RETURNDATASIZE [] sa = (rds,sb) /\
  compile_alloc_buffer 0 sb = (buf,sc) ==>
  ?u addr. run_inst_seq (emitted_insts sa sc) s = OK u /\
    eval_operand buf.buf_operand u = SOME addr /\
    eval_operand rds u = SOME (n2w (LENGTH s.vs_returndata)) /\
    u.vs_returndata = s.vs_returndata
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_read0_def] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
       eval_operand_def, exec_alloca_def, update_var_def] >>
  Cases_on `FLOOKUP s.vs_allocas (sa.cs_next_id + 1)`
  >- (simp[run_inst_seq_def, eval_operand_def, lookup_var_def,
           FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj]) >>
  rename1 `FLOOKUP _ _ = SOME p` >> PairCases_on `p` >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj]
QED

Theorem raw_call_failure_prefix_code[local]:
  emit_op RETURNDATASIZE [] sa = (rds,sb) /\
  compile_alloc_buffer 0 sb = (buf,sc) ==>
  sc.cs_current_bb = sa.cs_current_bb /\
  sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sc)
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem raw_call_failure_prefix_counted_mem[local]:
  emit_op RETURNDATASIZE [] sa = (rds,sb) /\
  compile_alloc_buffer 0 sb = (buf,sc) /\ fn_has_code sa sc func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u addr. gas_path_mem ctx func s 0 (OK u) /\
    u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    eval_operand buf.buf_operand u = SOME addr /\
    eval_operand rds u = SOME (n2w (LENGTH s.vs_returndata)) /\
    u.vs_returndata = s.vs_returndata
Proof
  strip_tac >> drule_all raw_call_failure_prefix_code >> strip_tac >>
  drule_all raw_call_failure_prefix_run >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sa sc) s` by
    (irule raw_call_failure_prefix_mem_ok >> metis_tac[]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sc)) = 0` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sc) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sc)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb` by
    (drule_all exec_block_run_inst_seq >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sc)`,
    `addr`] >>
  simp[eval_operand_def, lookup_var_def] >> metis_tac[LENGTH_APPEND]
QED
