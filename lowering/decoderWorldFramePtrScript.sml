(* Decoder code never touches the world fields that the source-owned
   decoder contracts promise to preserve. *)
Theory decoderWorldFramePtr
Ancestors
  abiDecoderVarSequence abiDecoderLoopSetup abiDecoderIndexedAddress abiEncoder
  venomExecSemantics venomState venomInst venomMemDefs compileEnv emitHelper
  exprLoweringProps list rich_list arithmetic

Theorem decoder_step_world_frame:
  abi_decoder_reentry_opcode inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
  t.vs_requests = s.vs_requests /\
  t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
  t.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[abi_decoder_reentry_opcode_def] >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def,
    exec_alloca_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  simp[update_var_def, mstore_def, mcopy_def, write_memory_with_expansion_def,
    jump_to_def]
QED

Theorem decoder_run_world_frame:
  !code s t. EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
  run_inst_seq code s = OK t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
  t.vs_requests = s.vs_requests /\
  t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
  t.vs_gas_readings = s.vs_gas_readings
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all decoder_step_world_frame >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem decoder_calldata_array_setup_opcodes:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) hi di asz msz st =
    (ops,st') ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')
Proof
  Cases_on `dec_info_needs_offset di` >> Cases_on `hi = Lit 0w` >>
  simp[abi_decode_array_element_setup_def, abi_decode_indexed_address_def,
    compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  strip_tac >> gvs[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED
