(* Memory-safe base case of recursive, pointer-to-pointer typed copies. *)
Theory placeTypedCopyMem
Ancestors
  placeMemoryTypedBase bodyDeclMemoryCounted bodyDeclMemoryCore
  instMemFrontier fragExecMem fragGasPathMem allocaHistory
  context emitHelperProps venomExecSemantics venomState venomInst
  valueEncodingProps immutableMemoryFrame ASCIInumbers
  compileEnv emitHelper exprLoweringProps finite_map list rich_list memSafeRun
  allocaHistoryFragment fragExec

Theorem typed_word_sequence_mem_ok[local]:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\ (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  w2n sw + 32 <= s.vs_alloca_next /\
  w2n dw + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `!w. eval_operand dst
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) = SOME dw` by
    (Cases_on `dst` >> gvs[eval_operand_def, update_var_def, lookup_var_def] >>
     rpt strip_tac >>
     `s' <> STRING #"%" (toString sa.cs_next_var)` by
       (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
     simp[FLOOKUP_UPDATE]) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
  gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, run_inst_seq_mem_ok_def] >>
  simp[below_frontier_MLOAD, below_frontier_MSTORE,
       mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def] >>
  simp[GSYM update_var_def, below_frontier_MSTORE] >>
  simp[exec_write2_def, eval_operand_def, lookup_var_update_var]
QED

Theorem typed_memory_word_path_mem:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\ (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  w2n sw + 32 <= s.vs_alloca_next /\
  w2n dw + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  let t = (mstore (w2n dw) (mload (w2n sw) s)
    (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n sw) s) s))
    with vs_inst_idx := LENGTH sb.cs_current_insts
  in gas_path_mem ctx func s 0 (OK t) /\
     ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_memory_word_sequence >> strip_tac >>
  drule_all typed_word_sequence_mem_ok >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all body_decl_cursor_path >> simp[]
QED

Theorem typed_memory_word_history:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\ (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  alloca_history func
    ((mstore (w2n dw) (mload (w2n sw) s)
      (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n sw) s) s))
      with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule_all typed_memory_word_sequence >> strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, same_blocks_def] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED
