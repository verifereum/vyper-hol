Theory deployOutcomesFreeAbiGenerators
Ancestors
  ctorCallFreeRules
  deployOutcomesFreeGenerators ctorCallFreeABIEncode ctorCallFreeABIDecode
  ctorCallFreeMemory
  context emitHelper builtinAbi builtinBytes
  builtinSimple exprLowering abiEncoder list pair
  ctorCallFreeValues

val abi_preserve_tac =
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, every_state_insts_return,
    every_state_insts_fresh_id, every_state_insts_fresh_var, every_state_insts_fresh_label,
        every_state_insts_new_block, outcomes_free_alloc_buffer,
    outcomes_free_copy_memory]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
    irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac, IF_CASES_TAC]);

Theorem outcomes_free_zero_words:
  !n s. P ADD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_zero_words base_op n s)))
Proof
  Induct_on `n` >> rpt strip_tac >> simp[compile_zero_words_def] >>
  abi_preserve_tac >> first_x_assum irule >> simp[]
QED

Theorem outcomes_free_builtin_empty_complex:
  P ALLOCA /\ P ADD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_builtin_empty_complex sz bs s)))
Proof
  strip_tac >> simp[compile_builtin_empty_complex_def] >>
  abi_preserve_tac >> simp[outcomes_free_zero_words]
QED

Theorem outcomes_free_bytestring_widen_copy:
  P ALLOCA /\ P MCOPY /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_bytestring_widen_copy sz v old s)))
Proof
  strip_tac >> simp[compile_bytestring_widen_copy_def] >> abi_preserve_tac
QED

Theorem outcomes_free_extract32_load:
  (!opc. MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT; MLOAD] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_extract32_load len data_op off s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_extract32_load_def] >>
  rpt (FIRST [CHANGED_TAC (simp[SRULE [DISJ_IMP_THM, FORALL_AND_THM]
    outcomes_free_compile_assert_slice_bounds]), CHANGED_TAC abi_preserve_tac])
QED

Theorem outcomes_free_lower_abi_encode:
  (!opc. MEM opc [ALLOCA; MLOAD; MSTORE; MCOPY; JMP; LT; ISZERO; JNZ;
    ADD; MUL; AND; NOT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (lower_abi_encode (ensure:bool) mid src info sz s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `mid` >> simp[lower_abi_encode_def] >>
  rpt (FIRST [CHANGED_TAC (simp[SRULE [DISJ_IMP_THM, FORALL_AND_THM]
    (cj 2 outcomes_free_abi_encode)]), CHANGED_TAC abi_preserve_tac])
QED

Theorem outcomes_free_lower_abi_decode:
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (lower_abi_decode src info lo hi sz s)))
Proof
  strip_tac >> simp[lower_abi_decode_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cj 1 (SRULE [DISJ_IMP_THM, FORALL_AND_THM]
    (Q.INST [`P` |-> `\op. op <> CALL /\ op <> STATICCALL /\ op <> DELEGATECALL /\
      op <> CREATE /\ op <> CREATE2 /\ op <> INVOKE`] outcomes_free_abi_decode))]),
    CHANGED_TAC abi_preserve_tac])
QED
