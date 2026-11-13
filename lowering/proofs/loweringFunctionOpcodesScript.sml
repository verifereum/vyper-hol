Theory loweringFunctionOpcodes
Ancestors
  moduleLowering compileEnv context emitHelper loweringShapeDefs venomInst
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeABIDecode list pair

Theorem opcode_every_fixed_region:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_fixed_region_with_id sz st)))
Proof
  strip_tac >>
  simp[compile_fixed_region_with_id_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_id_def, fresh_var_def, emit_def,
    state_insts_def, all_blocks_def, mk_inst_def]
QED

Theorem opcode_every_nonreentrant_lock:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_nonreentrant_lock key trans view st)))
Proof
  strip_tac >>
  qid_spec_tac `st` >> simp[compile_nonreentrant_lock_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      every_state_insts_return])])
QED

Theorem opcode_every_abi_arg_ptr_guard:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_arg_ptr_guard opc src parent st)))
Proof
  strip_tac >> simp[compile_abi_arg_ptr_guard_def] >> IF_CASES_TAC >>
  simp[every_state_insts_return] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void])])
QED

Theorem opcode_every_decode_args:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !args ce off opc hi base. P opc ==> !st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_decode_args ce args off opc hi base st)))
Proof
  strip_tac >>
  Induct >> simp[compile_decode_args_def, every_state_insts_return] >>
  qx_gen_tac `arg` >> PairCases_on `arg` >> rpt gen_tac >> strip_tac >>
  simp[compile_decode_args_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      (UNDISCH opcode_every_abi_clamp), (UNDISCH opcode_every_abi_decode_opcode), every_state_insts_return])]) >>
  BasicProvers.TOP_CASE_TAC >>
  gvs[every_state_insts_return, opcode_every_emit_void] >>
  BasicProvers.TOP_CASE_TAC >>
  gvs[every_state_insts_return, opcode_every_emit_void] >>
  qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, (UNDISCH opcode_every_abi_decode_opcode),
      UNDISCH opcode_every_abi_arg_ptr_guard, every_state_insts_return])])
QED

