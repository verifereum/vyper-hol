(* Callback-free return and revert opcode boundaries. *)
Theory ctorCallFreeStmtReturns
Ancestors
  list pair stmtLowering context venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeABI ctorCallFreeABIEncode

Theorem opcode_every_nonreentrant_unlock:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_nonreentrant_unlock key transient view st)))
  )
Proof
  strip_tac >>
  Cases_on `view` >> Cases_on `transient` >>
  simp[compile_nonreentrant_unlock_def, every_state_insts_return, opcode_every_emit_void]
QED

Theorem call_free_nonreentrant_unlock:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_nonreentrant_unlock key transient view st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_nonreentrant_unlock) >> simp[]
QED

Theorem opcode_every_load_tuple_elements:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !tys ce base off st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_load_tuple_elements ce base tys off st)))
  )
Proof
  strip_tac >>
  Induct >> simp[compile_load_tuple_elements_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, every_state_insts_return])])
QED

Theorem call_free_load_tuple_elements:
  !tys ce base off st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_load_tuple_elements ce base tys off st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_load_tuple_elements) >> simp[]
QED

Theorem opcode_every_mcopy_guard:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (action st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_mcopy_guard ce action st)))
  )
Proof
  strip_tac >>
  Cases_on `ce.ce_target CapMcopy` >> simp[compile_mcopy_guard_def, opcode_every_emit_inst]
QED

Theorem call_free_mcopy_guard:
  (!st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (action st)))) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_mcopy_guard ce action st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_mcopy_guard) >> simp[]
QED

Theorem opcode_every_internal_return:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_internal_return ce value pc nrets ty sty elems buf st)))
  )
Proof
  strip_tac >>
  Cases_on `0 < nrets` >> Cases_on `value` >> Cases_on `buf` >>
  Cases_on `elems = []` >> qid_spec_tac `st` >>
  simp[compile_internal_return_def, every_state_insts_bind,
    every_state_insts_ignore_bind, opcode_every_emit_inst,
    (UNDISCH opcode_every_load_tuple_elements), (UNDISCH opcode_every_store_memory)]
QED

Theorem call_free_internal_return:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_internal_return ce value pc nrets ty sty elems buf st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_internal_return) >> simp[]
QED

Theorem opcode_every_external_return:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_external_return value prim raw info maxsz nr key transient view st)))
  )
Proof
  strip_tac >>
  Cases_on `value` >> Cases_on `prim` >> Cases_on `raw` >> Cases_on `nr` >>
  qid_spec_tac `st` >> simp[compile_external_return_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_inst, opcode_every_emit_void,
      opcode_every_emit_op, every_state_insts_return, (UNDISCH opcode_every_alloc_buffer),
      (UNDISCH opcode_every_nonreentrant_unlock), (UNDISCH opcode_every_abi_encode)])])
QED

Theorem call_free_external_return:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_external_return value prim raw info maxsz nr key transient view st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_external_return) >> simp[]
QED

Theorem opcode_every_return_unlock:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_return_unlock ce st)))
  )
Proof
  strip_tac >>
  simp[compile_return_unlock_def] >> pairarg_tac >> gvs[] >>
  IF_CASES_TAC >> simp[(UNDISCH opcode_every_nonreentrant_unlock), every_state_insts_return]
QED

Theorem call_free_return_unlock:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_return_unlock ce st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_return_unlock) >> simp[]
QED

Theorem opcode_every_internal_return_from_env:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_internal_return_from_env ce ty sty value pc st)))
  )
Proof
  strip_tac >>
  Cases_on `ce.ce_return_buf` >>
  TRY (rename1 `ce.ce_return_buf = SOME loc` >> Cases_on `loc`) >>
  simp[compile_internal_return_from_env_def] >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[(UNDISCH opcode_every_return_unlock), opcode_every_emit_op,
      every_state_insts_return, (UNDISCH opcode_every_internal_return)])])
QED

Theorem call_free_internal_return_from_env:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_internal_return_from_env ce ty sty value pc st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_internal_return_from_env) >> simp[]
QED

Theorem opcode_every_revert_with_reason:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_revert_with_reason ce msg ty sz st)))
  )
Proof
  strip_tac >>
  qid_spec_tac `st` >> simp[compile_revert_with_reason_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_inst, opcode_every_emit_void,
      opcode_every_emit_op, (UNDISCH opcode_every_alloc_buffer), (UNDISCH opcode_every_unwrap_value)])])
QED

Theorem call_free_revert_with_reason:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_revert_with_reason ce msg ty sz st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_revert_with_reason) >> simp[]
QED
