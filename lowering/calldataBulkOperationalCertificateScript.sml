(* Operational framing of the given successful finite bulk decoder run. *)
Theory calldataBulkOperationalCertificate
Ancestors
  calldataBulkLive calldataFiniteTransport calldataBulkLeaf abiDecoderBulk
  abiDecoderReservation abiDecoderContract abiEncoder
  entryReachBodyExactArrayLoop ctorAbiActualAlloc
  safeSequence fragExecMem emitHelper exprLoweringProps compileEnv loweringStateRelDefs
  venomExecSemantics venomState venomInst finite_map pred_set words list rich_list arithmetic

Theorem bulk_step_fields[local]:
  MEM i.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; MSTORE; MUL; ADD; CALLDATACOPY] /\
  step_inst_base i s = OK t ==> entry_loop_fields s t
Proof
  simp_tac bool_ss [MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[opcode_case_def] >>
  simp[exec_read1_def, exec_write2_def, exec_pure2_def, exec_pure1_def, AllCaseEqs()] >> strip_tac >>
  gvs[entry_loop_fields_def, update_var_def, mstore_def, write_memory_with_expansion_def]
QED

Theorem bulk_code_shape[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),last) /\
  ~dec_info_needs_clamp ei /\ last.cs_next_var <= limit.cs_next_var ==>
  EVERY (\i. MEM i.inst_opcode
    [CALLDATALOAD; GT; ISZERO; ASSERT; MSTORE; MUL; ADD; CALLDATACOPY] /\
    EVERY (\x. ?k. x = STRING #"%" (toString k) /\ k < limit.cs_next_var)
      i.inst_outputs) (emitted_insts st last)
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED
