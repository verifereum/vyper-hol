(* Callback-free return and revert opcode boundaries. *)
Theory ctorCallFreeStmtReturns
Ancestors
  list pair stmtLowering context venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeABI ctorCallFreeABIEncode

Theorem call_free_nonreentrant_unlock:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_nonreentrant_unlock key transient view st)))
Proof
  Cases_on `view` >> Cases_on `transient` >>
  simp[compile_nonreentrant_unlock_def, every_state_insts_return, call_free_emit_void]
QED

Theorem call_free_load_tuple_elements:
  !tys ce base off st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_load_tuple_elements ce base tys off st)))
Proof
  Induct >> simp[compile_load_tuple_elements_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, every_state_insts_return])])
QED

Theorem call_free_mcopy_guard:
  (!st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (action st)))) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_mcopy_guard ce action st)))
Proof
  Cases_on `ce.ce_target CapMcopy` >> simp[compile_mcopy_guard_def, call_free_emit_inst]
QED

Theorem call_free_internal_return:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_internal_return ce value pc nrets ty sty elems buf st)))
Proof
  Cases_on `0 < nrets` >> Cases_on `value` >> Cases_on `buf` >>
  Cases_on `elems = []` >> qid_spec_tac `st` >>
  simp[compile_internal_return_def, every_state_insts_bind,
    every_state_insts_ignore_bind, call_free_emit_inst,
    call_free_load_tuple_elements, call_free_store_memory]
QED

Theorem call_free_external_return:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_external_return value prim raw info maxsz nr key transient view st)))
Proof
  Cases_on `value` >> Cases_on `prim` >> Cases_on `raw` >> Cases_on `nr` >>
  qid_spec_tac `st` >> simp[compile_external_return_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_inst, call_free_emit_void,
      call_free_emit_op, every_state_insts_return, call_free_alloc_buffer,
      call_free_nonreentrant_unlock, call_free_abi_encode])])
QED

Theorem call_free_return_unlock:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_return_unlock ce st)))
Proof
  simp[compile_return_unlock_def] >> pairarg_tac >> gvs[] >>
  IF_CASES_TAC >> simp[call_free_nonreentrant_unlock, every_state_insts_return]
QED

Theorem call_free_internal_return_from_env:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_internal_return_from_env ce ty sty value pc st)))
Proof
  Cases_on `ce.ce_return_buf` >>
  TRY (rename1 `ce.ce_return_buf = SOME loc` >> Cases_on `loc`) >>
  simp[compile_internal_return_from_env_def] >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_return_unlock, call_free_emit_op,
      every_state_insts_return, call_free_internal_return])])
QED

Theorem call_free_revert_with_reason:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_revert_with_reason ce msg ty sz st)))
Proof
  qid_spec_tac `st` >> simp[compile_revert_with_reason_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_inst, call_free_emit_void,
      call_free_emit_op, call_free_alloc_buffer, call_free_unwrap_value])])
QED
