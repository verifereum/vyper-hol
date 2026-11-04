(* Memory footprints of external entry prefixes. *)
Theory entryPrefixMem
Ancestors
  moduleLowering emitHelper compileEnv exprLoweringProps fragExec fragExecMem instMemFrontier venomInst list rich_list

Theorem compile_entry_checks_mem_ok:
  compile_entry_checks min_cds is_payable st = ((), st') ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  Cases_on `is_payable` >> Cases_on `4 < min_cds` >>
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  irule run_inst_seq_mem_ok_every >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  rpt strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED
