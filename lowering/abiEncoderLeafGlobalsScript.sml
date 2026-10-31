(* Pure leaf opcode certificate; field preservation only, not execution correctness. *)
Theory abiEncoderLeafGlobals
Ancestors
  abiEncoderLeafCode abiEncoderBytesCode abiEncoderReentryLeaves abiEncoder
  emitHelper emitHelperProps exprLoweringProps compileEnv venomState venomExecSemantics venomInst
  valueEncoding list rich_list pred_set words arithmetic

Theorem abi_encoder_leaf_step_globals:
  inst.inst_opcode IN {MLOAD; MSTORE; MCOPY; ADD; AND} /\
  step_inst_base inst s = OK t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests
Proof
  simp_tac (srw_ss()) [IN_INSERT, NOT_IN_EMPTY] >> strip_tac >>
  gvs[Once step_inst_base_def] >>
  gvs[exec_pure2_def, exec_read1_def, exec_write2_def, AllCaseEqs()] >>
  simp[update_var_def, mstore_def, mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_encoder_leaf_sequence_globals:
  !insts s t.
  EVERY (\i. i.inst_opcode IN {MLOAD; MSTORE; MCOPY; ADD; AND}) insts /\
  run_inst_seq insts s = OK t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests
Proof
  Induct_on `insts` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> rename1 `EVERY _ (inst::rest)` >> simp_tac (srw_ss()) [Once run_inst_seq_def] >>
  Cases_on `step_inst_base inst s` >> simp[] >>
  rename1 `step_inst_base inst s = OK next` >> strip_tac >>
  drule_at (Pos last) abi_encoder_leaf_step_globals >> simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`next`, `t`] mp_tac) >> simp[]
QED

Theorem abi_encoder_word_global_code:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') ==>
  EVERY (\i. i.inst_opcode IN {MLOAD; MSTORE; MCOPY; ADD; AND}) (emitted_insts st st')
Proof
  simp[Once compile_abi_encode_child_def, compile_abi_encode_static_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encoder_copy_global_code:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') ==>
  EVERY (\i. i.inst_opcode IN {MLOAD; MSTORE; MCOPY; ADD; AND}) (emitted_insts st st')
Proof
  simp[Once compile_abi_encode_child_def, compile_abi_encode_static_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encoder_bytes_global_code:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,st') ==>
  EVERY (\i. i.inst_opcode IN {MLOAD; MSTORE; MCOPY; ADD; AND}) (emitted_insts st st')
Proof
  simp[Once compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED
