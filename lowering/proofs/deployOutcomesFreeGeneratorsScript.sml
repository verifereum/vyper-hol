Theory deployOutcomesFreeGenerators
Ancestors
  ctorCallFreeRules
  exprLowering context emitHelper compileEnv
  exprBopLowering builtinSimple list pair venomInst
  ctorCallFreeValues

(* Pointer companion of exprBopLowering's as_stack_val_pair. *)
Theorem as_ptr_val_pair:
  !ty loc p. as_ptr_val ty loc p = (LocatedValue ty (mk_ptr (FST p) loc), SND p)
Proof
  Cases_on `p` >> simp[as_ptr_val_def]
QED

Theorem outcomes_free_lower_value_opcodes:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY] ==> P opc) /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
       EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn cenv ty e s)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (lower_value cfn cenv ty e s)))
Proof
  strip_tac >> simp[lower_value_def] >> irule ctorCallFreeRulesTheory.every_state_insts_bind >>
  simp[outcomes_free_unwrap_value]
QED

Theorem outcomes_free_encode_log_topic:
  P ADD /\ P MLOAD /\ P SHA3 /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_encode_log_topic src bytestring s)))
Proof
  strip_tac >> Cases_on `bytestring` >>
  simp[compile_encode_log_topic_def, every_state_insts_return] >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst] >> rpt strip_tac >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]
QED

