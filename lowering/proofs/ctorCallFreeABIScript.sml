(* Public ABI builtin opcode boundaries. *)
Theory ctorCallFreeABI
Ancestors
  list pair compileEnv venomInst loweringShapeDefs emitHelper context
  abiEncoder builtinAbi exprLowering
  ctorCallFreeRules ctorCallFreeValues
  ctorCallFreeABIEncode ctorCallFreeABIDecode

val abi_preserve_tac =
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, every_state_insts_return,
    every_state_insts_fresh_id, every_state_insts_fresh_var, every_state_insts_fresh_label,
        every_state_insts_new_block, outcomes_free_alloc_buffer,
    outcomes_free_copy_memory]),
    gen_tac, strip_tac, irule every_state_insts_bind,
    irule every_state_insts_ignore_bind, conj_tac, IF_CASES_TAC]);

Theorem outcomes_free_lower_abi_encode:
  (!opc. MEM opc [ALLOCA; MLOAD; MSTORE; MCOPY; JMP; LT; ISZERO; JNZ;
    ADD; MUL; AND; NOT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (lower_abi_encode ensure mid src info sz s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `mid` >> simp[lower_abi_encode_def] >>
  rpt (FIRST [CHANGED_TAC (simp[SRULE [DISJ_IMP_THM, FORALL_AND_THM]
    (cj 2 outcomes_free_abi_encode)]), CHANGED_TAC abi_preserve_tac])
QED

Theorem opcode_every_lower_abi_encode:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (lower_abi_encode ensure mid src info maxlen st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_lower_abi_encode >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_lower_abi_decode:
  (!opc. MEM opc [ADD; MUL; LT; GT; EQ; AND; NOT; ISZERO; SHR; SHL;
     SIGNEXTEND; ASSERT; MLOAD; MSTORE; MCOPY; ALLOCA; JMP; JNZ] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (lower_abi_decode src info lo hi sz s)))
Proof
  strip_tac >> simp[lower_abi_decode_def] >>
  `P MLOAD` by fs[] >>
  rpt (FIRST [CHANGED_TAC (simp[cj 1 (UNDISCH outcomes_free_abi_decode)]),
    CHANGED_TAC abi_preserve_tac])
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
  rpt strip_tac >> irule outcomes_free_lower_abi_decode >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_store_abi_tuple:
  !args buf off s. P ADD /\ P MSTORE /\ P MCOPY /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_abi_tuple ce buf off args s)))
Proof
  Induct_on `args` >> rpt strip_tac >>
  simp[compile_store_abi_tuple_def, every_state_insts_return] >>
  rename1 `compile_store_abi_tuple _ _ _ (arg::_)` >> PairCases_on `arg` >>
  simp[compile_store_abi_tuple_def] >>
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, outcomes_free_copy_memory]),
    gen_tac, strip_tac, irule every_state_insts_bind, irule every_state_insts_ignore_bind,
    conj_tac, IF_CASES_TAC, first_assum irule])
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
  rpt strip_tac >> irule outcomes_free_store_abi_tuple >> simp[]
QED
