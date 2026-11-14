Theory loweringCallArgsOpcodes
Ancestors list pair exprLowering compileEnv context venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks

Theorem opcode_every_stage_intcall_args:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !cfn ce es flags tys.
  (!e ty st. MEM e es ==> EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn ce ty e st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stage_intcall_args cfn ce es flags tys st)))
Proof
  strip_tac >> ho_match_mp_tac compile_stage_intcall_args_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_stage_intcall_args_def] >>
  rpt (FIRST [
    disch_then (CONJUNCTS_THEN assume_tac),
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac,
    CHANGED_TAC (simp[compile_stage_intcall_args_def,
      UNDISCH opcode_every_unwrap_value, UNDISCH opcode_every_alloc_buffer,
      UNDISCH opcode_every_store_bytestring, UNDISCH opcode_every_store_memory,
      opcode_every_emit_void, every_state_insts_return]),
    CASE_TAC >> simp[compile_stage_intcall_args_def] >> qid_spec_tac `st`,
    disch_tac])
QED

Theorem opcode_every_store_multi_results:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !ops buf off st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (store_multi_results buf ops off st)))
Proof
  strip_tac >> Induct >> simp[store_multi_results_def,
    every_state_insts_return] >> rpt gen_tac >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void])])
QED

Theorem opcode_every_ext_call_args:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !es tys cfn ce kws.
  (!e ty st. MEM e es ==> EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn ce ty e st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_ext_call_args cfn ce kws tys es st)))
Proof
  strip_tac >> Induct >> simp[compile_ext_call_args_def,
    every_state_insts_return] >> rpt gen_tac >> strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >> Cases_on `tys` >>
  simp[compile_ext_call_args_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[UNDISCH opcode_every_snapshot_vv,
      every_state_insts_return])])
QED

Theorem opcode_every_ext_call_kwarg:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) /\
  (!ty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn ce ty e st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_ext_call_kwarg cfn ce rt k e st)))
Proof
  strip_tac >> simp[compile_ext_call_kwarg_def] >> IF_CASES_TAC >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_lower_value >> conj_tac,
    gen_tac, CHANGED_TAC (simp[UNDISCH opcode_every_materialize_vv,
      UNDISCH opcode_every_unwrap_value, every_state_insts_return])])
QED

Theorem opcode_every_ext_call_kwargs:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !es ks cfn ce rt.
  (!e ty st. MEM e es ==> EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn ce ty e st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_ext_call_kwargs cfn ce rt ks es st)))
Proof
  strip_tac >> Induct >> simp[compile_ext_call_kwargs_def,
    every_state_insts_return] >> rpt gen_tac >> strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >> Cases_on `ks` >>
  simp[compile_ext_call_kwargs_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_ext_call_kwarg,
      every_state_insts_return]),
    pairarg_tac >> gvs[] >> qid_spec_tac `st`])
QED
