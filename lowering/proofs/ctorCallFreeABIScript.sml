(* Public ABI builtin opcode boundaries. *)
Theory ctorCallFreeABI
Ancestors
  list pair compileEnv venomInst loweringShapeDefs emitHelper context
  abiEncoder builtinAbi exprLowering
  ctorCallFreeRules ctorCallFreeValues
  ctorCallFreeABIEncode ctorCallFreeABIDecode

Theorem call_free_lower_abi_encode:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (lower_abi_encode ensure mid src info maxlen st)))
Proof
  Cases_on `mid` >> qid_spec_tac `st` >> simp[lower_abi_encode_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_alloc_buffer, call_free_abi_encode, every_state_insts_return])])
QED

Theorem call_free_lower_abi_decode:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (lower_abi_decode data_op info min_sz max_sz out_sz st)))
Proof
  qid_spec_tac `st` >> simp[lower_abi_decode_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_alloc_buffer, call_free_abi_decode_memory, every_state_insts_return])])
QED

Theorem call_free_store_abi_tuple:
  !vs cenv buf off st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_store_abi_tuple cenv buf off vs st)))
Proof
  Induct >- simp[compile_store_abi_tuple_def, every_state_insts_return] >>
  rpt gen_tac >> PairCases_on `h` >> qid_spec_tac `st` >>
  simp[compile_store_abi_tuple_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_copy_memory, every_state_insts_return])])
QED
