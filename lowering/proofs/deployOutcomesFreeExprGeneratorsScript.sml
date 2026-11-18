Theory deployOutcomesFreeExprGenerators
Ancestors
  ctorCallFreeRules
  deployOutcomesFreeGenerators exprLowering list
  ctorCallFreeValues

Theorem outcomes_free_mapping_subscript:
  P ALLOCA /\ P MSTORE /\ P ADD /\ P SHA3 /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_mapping_subscript b k s)))
Proof
  strip_tac >> simp[compile_mapping_subscript_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
        outcomes_free_alloc_buffer]),
    irule ctorCallFreeRulesTheory.every_state_insts_bind, irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac])
QED

Theorem outcomes_free_keccak256_key:
  P ALLOCA /\ P MSTORE /\ P ADD /\ P MLOAD /\ P SHA3 /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_keccak256_key k flag s)))
Proof
  strip_tac >> Cases_on `flag` >> simp[compile_keccak256_key_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
        outcomes_free_alloc_buffer]),
    irule ctorCallFreeRulesTheory.every_state_insts_bind, irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac])
QED

Theorem outcomes_free_tuple_subscript:
  P ADD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_tuple_subscript b n s)))
Proof
  simp[compile_tuple_subscript_def, opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst]
QED

Theorem outcomes_free_array_subscript:
  (!b st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (loader b st)))) /\
  P SLT /\ P LT /\ P ISZERO /\ P OR /\ P ASSERT /\ P ADD /\ P MUL /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_array_subscript b i d n ws sz sg loader s)))
Proof
  strip_tac >> Cases_on `d` >> Cases_on `sg` >>
  simp[compile_array_subscript_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
        every_state_insts_return]),
    irule ctorCallFreeRulesTheory.every_state_insts_bind, irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac])
QED

