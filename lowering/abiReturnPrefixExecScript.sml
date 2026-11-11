Theory abiReturnPrefixExec
Ancestors
  abiReturnSize fragExec exprLoweringProps exprLowering builtinSimple emitHelper compileEnv
  venomExecSemantics venomState venomInst list rich_list

Theorem abi_return_prefix_straight[local]:
  compile_return_value_decode lo cap a = (hi,b) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts a b)
Proof
  simp[compile_return_value_decode_def, builtinSimpleTheory.compile_select_def,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pure_rewrite_tac[emitted_insts_def] >>
  simp_tac (srw_ss()) [] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem abi_return_prefix_block[local]:
  compile_return_value_decode lo cap a = (hi,b) /\ fn_has_code a b func /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts a b) (DROP s.vs_inst_idx bb.bb_instructions) /\
    s.vs_inst_idx + LENGTH (emitted_insts a b) = LENGTH b.cs_current_insts
Proof
  strip_tac >> drule abi_return_size_code >> strip_tac >>
  fs[fn_has_code_def, same_blocks_def] >>
  qpat_x_assum `_ ++ _ ≼ _` mp_tac >>
  simp[IS_PREFIX_APPEND] >> strip_tac >>
  metis_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem abi_return_prefix_abort:
  compile_return_value_decode lo cap a = (hi,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  run_inst_seq (emitted_insts a b) s = Abort Revert_abort u ==>
  ?fuel z. run_from fuel ctx func s = Abort Revert_abort z
Proof
  strip_tac >> drule_all abi_return_prefix_block >> strip_tac >>
  drule abi_return_prefix_straight >> strip_tac >>
  qspecl_then [`emitted_insts a b`, `s`, `0`, `ctx`, `bb`]
    mp_tac exec_block_run_inst_seq >> simp[] >> strip_tac >>
  qexists_tac `0` >> simp[run_from_def]
QED

Theorem abi_return_prefix_then_abort:
  compile_return_value_decode lo cap a = (hi,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  run_inst_seq (emitted_insts a b) s = OK u /\
  run_from k ctx func (u with vs_inst_idx := LENGTH b.cs_current_insts) =
    Abort Revert_abort z ==>
  ?fuel v. run_from fuel ctx func s = Abort Revert_abort v
Proof
  strip_tac >> drule_all abi_return_prefix_block >> strip_tac >>
  drule abi_return_prefix_straight >> strip_tac >>
  qspecl_then [`emitted_insts a b`, `s`, `k`, `ctx`, `bb`]
    mp_tac exec_block_run_inst_seq >> simp[] >> strip_tac >>
  qexists_tac `k` >>
  qpat_x_assum `run_from k _ _ _ = _` mp_tac >>
  simp[run_from_def] >> gvs[]
QED
