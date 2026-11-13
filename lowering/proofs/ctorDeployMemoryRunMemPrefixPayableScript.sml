Theory ctorDeployMemoryRunMemPrefixPayable
Ancestors
  fragExecMem fragExec exprLoweringProps moduleLoweringProps emitHelper compileEnv moduleLowering
  unitTransformDefs venomInst venomState list rich_list memSafeRun contextCodegenRel codegenRel

Theorem ctor_prefix_payable_mem:
  emit_op CALLVALUE [] st0 = (cv,st1) /\
  emit_op ISZERO [cv] st1 = (nv,st2) /\
  emit_void ASSERT [nv] st2 = ((),st3) /\
  fresh_vars_wrt st0 s /\ s.vs_call_ctx.cc_callvalue <> 0w ==>
  frag_exec_mem ctx st0 st3 (\t. t = s) (\t. F)
    (\r. ?t. r = Abort Revert_abort t)
Proof
  rpt strip_tac >>
  `?t. run_inst_seq (emitted_insts st0 st3) s = Abort Revert_abort t`
    by (drule_all compile_payable_check_ok_or_revert >> simp[]) >>
  irule frag_exec_mem_run_inst_seq >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
      fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emitted_insts_def, DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def] >>
  irule run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, inst_mem_below_frontier_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       inst_dload_in_section_def]
QED
