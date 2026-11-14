Theory loweringExtCallOpcodes
Ancestors list pair exprLowering compileEnv context venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeOps
  ctorCallFreeABIEncode ctorCallFreeABIDecode

Theorem opcode_every_extcall_store_values:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !vs ce buf off st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_extcall_store_values ce vs buf off st)))
Proof
  strip_tac >> Induct >> simp[compile_extcall_store_values_def,
    every_state_insts_return] >> rpt gen_tac >> PairCases_on `h` >>
  qid_spec_tac `st` >> simp[compile_extcall_store_values_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[UNDISCH opcode_every_unwrap_value,
      UNDISCH opcode_every_store_bytestring, opcode_every_emit_op,
      opcode_every_emit_void, every_state_insts_return])])
QED

Theorem opcode_every_extcodesize_check:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_extcodesize_check addr st)))
Proof
  strip_tac >> simp[compile_extcodesize_check_def] >>
  ho_match_mp_tac every_state_insts_bind >>
  simp[opcode_every_emit_op, opcode_every_emit_void]
QED

Theorem opcode_every_return_value_decode:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_return_value_decode lo hi st)))
Proof
  strip_tac >> simp[compile_return_value_decode_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[UNDISCH opcode_every_select,
      opcode_every_emit_op, opcode_every_emit_void])])
QED

Theorem opcode_every_default_return_path:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_default_return_path ce rt dt
        buf result default_op addr skip lo hi info st)))
Proof
  strip_tac >> simp[compile_default_return_path_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[UNDISCH opcode_every_store_memory,
      UNDISCH opcode_every_extcodesize_check,
      UNDISCH opcode_every_return_value_decode,
      UNDISCH opcode_every_abi_decode_opcode,
      opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
      every_state_insts_fresh_label, every_state_insts_new_block,
      every_state_insts_return])])
QED

Theorem opcode_every_external_call_kwargs:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) /\ P RETURNDATACOPY ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_external_call_kwargs ce addr vs tys
        memsz abisz mid retsz minret retmem static value gas skip
        has_default default_op rt dt enc_info dec_info st)))
Proof
  strip_tac >> simp[compile_external_call_kwargs_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[UNDISCH opcode_every_alloc_buffer,
      UNDISCH opcode_every_extcall_store_values,
      UNDISCH opcode_every_abi_encode,
      UNDISCH opcode_every_extcodesize_check,
      UNDISCH opcode_every_default_return_path,
      UNDISCH opcode_every_return_value_decode,
      UNDISCH opcode_every_abi_decode_opcode,
      opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
      every_state_insts_fresh_label, every_state_insts_new_block,
      every_state_insts_return])])
QED
