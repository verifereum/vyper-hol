(* Public ABI builtin opcode boundaries. *)
Theory ctorCallFreeABI
Ancestors
  list pair compileEnv venomInst loweringShapeDefs emitHelper context
  abiEncoder builtinAbi exprLowering
  ctorCallFreeRules ctorCallFreeValues
  ctorCallFreeABIEncode ctorCallFreeABIDecode

Theorem opcode_every_lower_abi_encode:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (lower_abi_encode ensure mid src info maxlen st)))
  )
Proof
  strip_tac >>
  Cases_on `mid` >> qid_spec_tac `st` >> simp[lower_abi_encode_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      (UNDISCH opcode_every_alloc_buffer), (UNDISCH opcode_every_abi_encode), every_state_insts_return])])
QED

Theorem call_free_lower_abi_encode:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (lower_abi_encode ensure mid src info maxlen st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_lower_abi_encode) >> simp[]
QED

Theorem opcode_every_lower_abi_decode:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (lower_abi_decode data_op info min_sz max_sz out_sz st)))
  )
Proof
  strip_tac >>
  qid_spec_tac `st` >> simp[lower_abi_decode_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      (UNDISCH opcode_every_alloc_buffer), (UNDISCH opcode_every_abi_decode_memory), every_state_insts_return])])
QED

Theorem call_free_lower_abi_decode:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (lower_abi_decode data_op info min_sz max_sz out_sz st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_lower_abi_decode) >> simp[]
QED

Theorem opcode_every_store_abi_tuple:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !vs cenv buf off st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_abi_tuple cenv buf off vs st)))
  )
Proof
  strip_tac >>
  Induct >- simp[compile_store_abi_tuple_def, every_state_insts_return] >>
  rpt gen_tac >> PairCases_on `h` >> qid_spec_tac `st` >>
  simp[compile_store_abi_tuple_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      (UNDISCH opcode_every_copy_memory), every_state_insts_return])])
QED

Theorem call_free_store_abi_tuple:
  !vs cenv buf off st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_store_abi_tuple cenv buf off vs st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_store_abi_tuple) >> simp[]
QED
