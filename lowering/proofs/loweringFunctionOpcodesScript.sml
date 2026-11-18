Theory loweringFunctionOpcodes
Ancestors
  moduleLowering compileEnv context emitHelper loweringShapeDefs venomInst
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeABIDecode list pair

Theorem outcomes_free_nonreentrant:
  (!opc. MEM opc [TLOAD; SLOAD; TSTORE; SSTORE; EQ; ISZERO; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_nonreentrant_lock key trans view s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_nonreentrant_unlock key trans view s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_nonreentrant_lock_def, compile_nonreentrant_unlock_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_fixed_region:
  P ASSIGN ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_fixed_region_with_id sz st)))
Proof
  strip_tac >>
  simp[compile_fixed_region_with_id_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_id_def, fresh_var_def, emit_def,
    state_insts_def, all_blocks_def, mk_inst_def]
QED

Theorem outcomes_free_constructor_epilogue:
  P ALLOCA /\ P ADD /\ P MCOPY /\ P CODECOPY /\ P RETURN ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_constructor_epilogue sz cap imm st)))
Proof
  strip_tac >> simp[compile_constructor_epilogue_def] >>
  rpt (FIRST [IF_CASES_TAC,
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, outcomes_free_alloc_buffer,
      every_state_insts_return])])
QED

Theorem opcode_every_fixed_region:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_fixed_region_with_id sz st)))
Proof
  strip_tac >> match_mp_tac outcomes_free_fixed_region >> simp[]
QED

Theorem opcode_every_nonreentrant_lock:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_nonreentrant_lock key trans view st)))
Proof
  rpt strip_tac >> irule (cj 1 outcomes_free_nonreentrant) >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_abi_arg_ptr_guard:
  P LT /\ P ISZERO /\ P ASSERT /\
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_arg_ptr_guard opc src parent st)))
Proof
  strip_tac >> simp[compile_abi_arg_ptr_guard_def] >> IF_CASES_TAC >>
  simp[every_state_insts_return] >>
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void]),
    gen_tac, strip_tac, irule every_state_insts_bind])
QED

Theorem opcode_every_abi_arg_ptr_guard:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_arg_ptr_guard opc src parent st)))
Proof
  rpt strip_tac >> irule outcomes_free_abi_arg_ptr_guard >> simp[]
QED

Theorem outcomes_free_decode_args:
  (!opc. MEM opc [ADD; MUL; LT; GT; EQ; AND; NOT; ISZERO; SHR; SHL;
     SIGNEXTEND; ASSERT; MLOAD; MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES;
     ALLOCA; JMP; JNZ] ==> P opc) ==>
  !args ce off opc hi base. P opc ==> !st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_decode_args ce args off opc hi base st)))
Proof
  strip_tac >> drule outcomes_free_abi_decode >> strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Induct >> simp[compile_decode_args_def, every_state_insts_return] >>
  qx_gen_tac `arg` >> PairCases_on `arg` >> rpt gen_tac >> strip_tac >>
  simp[compile_decode_args_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      outcomes_free_abi_clamp, every_state_insts_return])]) >>
  BasicProvers.TOP_CASE_TAC >>
  gvs[every_state_insts_return, opcode_every_emit_void] >>
  BasicProvers.TOP_CASE_TAC >>
  gvs[every_state_insts_return, opcode_every_emit_void] >>
  qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op,
      outcomes_free_abi_arg_ptr_guard, every_state_insts_return])])
QED

Theorem opcode_every_decode_args:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !args ce off opc hi base. P opc ==> !st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_decode_args ce args off opc hi base st)))
Proof
  strip_tac >> match_mp_tac outcomes_free_decode_args >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_register_constructor_args:
  (!opc. MEM opc [ADD; MUL; LT; GT; EQ; AND; NOT; ISZERO; SHR; SHL;
     SIGNEXTEND; ASSERT; MLOAD; MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES;
     ALLOCA; JMP; JNZ] ==> P opc) /\ P DLOAD ==>
  !args ce off sz st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_register_constructor_args ce args off sz st)))
Proof
  strip_tac >> drule outcomes_free_decode_args >> strip_tac >>
  `P ALLOCA` by fs[] >>
  Induct >- simp[compile_register_constructor_args_def, every_state_insts_return] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  qmatch_goalsub_rename_tac `compile_register_constructor_args _ ((nm,_)::_)` >>
  Cases_on `FLOOKUP ce.ce_vars nm` >>
  simp[compile_register_constructor_args_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (gvs[outcomes_free_alloc_buffer, every_state_insts_return]),
    irule every_state_insts_bind, irule every_state_insts_ignore_bind, conj_tac,
    IF_CASES_TAC,
    (qmatch_goalsub_rename_tac `var_location_memory_size loc` >>
      Cases_on `var_location_memory_size loc`)]) >>
  qpat_x_assum `!ce off sz st. _` irule >> simp[]
QED
