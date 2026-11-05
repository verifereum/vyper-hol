(* Concrete bytes child execution, with a physical owner independent of its destination. *)
Theory entryReachBodyOwnedBytesChild
Ancestors
  entryReachBodySequenceObservations entryReachBodyOwnedLoop
  entryReachBodyCanonicalBytes entryReachBodyCanonicalChildAddress
  abiDecoderLoopSetup abiDecoderIndexedAddress abiDecoderContract abiEncoder
  emitHelper emitHelperProps compileEnv venomInst rich_list list arithmetic fragExec exprLoweringProps

Theorem bytes_child_sequence_observations[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (DecBytestring n) az mz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops))
    CALLDATALOAD (Lit 0w) (DecBytestring n) middle = ((),last) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  run_inst_seq (emitted_insts st last) s = OK t ==>
  entry_loop_fields s t /\ fresh_vars_wrt limit_st t
Proof
  strip_tac >> irule entry_sequence_observations >>
  asm_rewrite_tac[] >> qexists_tac `emitted_insts st last` >> asm_rewrite_tac[] >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_array_element_setup_def, compile_abi_decode_to_buf_def,
    compile_abi_decode_dyn_elem_ptr_def, abi_decode_indexed_address_def,
    dec_info_needs_offset_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >> metis_tac[LESS_ADD]
QED
