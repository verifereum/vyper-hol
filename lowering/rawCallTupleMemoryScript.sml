(* Memory checks for the inline tuple result of nonreverting raw_call. *)
Theory rawCallTupleMemory
Ancestors
  rawCallFinishPathMemory exprSimRawCall fragExecMem instMemFrontier
  exprSafeOperand freshWrites emitHelper context compileEnv exprLoweringProps fragExec memSafeRun venomExecSemantics venomState
  venomInst words finite_map rich_list list

Theorem raw_call_tuple_copy_seq_mem_ok[local]:
  emit_op ADD [pop;Lit 32w] sa = (dst,sb) /\
  emit_void MCOPY [dst;src;Lit (n2w sz)] sb = ((),sc) /\
  safe_operand sa src /\ eval_operand pop s = SOME w /\
  eval_operand src s = SOME a /\ sz < dimword (:256) /\
  w2n (w + 32w) + sz <= s.vs_alloca_next /\
  w2n a + sz <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sc) s
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_mem_ok_cons, below_frontier_no_ranges,
       inst_dload_in_section_other, mk_inst_def] >>
  simp[Once step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  `src <> Var (STRING #"%" (toString sa.cs_next_var))` by
    (strip_tac >> gvs[safe_operand_def, not_fresh_at_def]) >>
  `eval_operand src (update_var (STRING #"%" (toString sa.cs_next_var)) (w + 32w) s) = SOME a` by
    (Cases_on `src` >> gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  simp[run_inst_seq_mem_ok_last, GSYM mk_inst_def] >>
  simp[below_frontier_MCOPY, inst_dload_in_section_other] >>
  rpt strip_tac >> gvs[eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, w2n_n2w]
QED
