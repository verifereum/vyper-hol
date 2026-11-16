(* Successful assembly steps leave the executing program's bytes fixed. *)
Theory asmOwnCodeInvariant
Ancestors
  asmSem

Theorem asm_consume_call_outcome_code_preserved[local]:
  !rq ro rs stk s s'.
    asm_consume_call_outcome rq ro rs stk s = AsmOK s' ==>
    s'.as_code = s.as_code
Proof
  rpt gen_tac >>
  simp[asm_consume_call_outcome_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >>
  simp[asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_consume_create_outcome_code_preserved[local]:
  !rq stk s s'.
    asm_consume_create_outcome rq stk s = AsmOK s' ==>
    s'.as_code = s.as_code
Proof
  rpt gen_tac >>
  simp[asm_consume_create_outcome_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >>
  simp[asm_next_def] >> strip_tac >> gvs[]
QED

Theorem asm_step_arith_code_preserved[local]:
  !name s s'.
    asm_step_arith name s = SOME (AsmOK s') ==> s'.as_code = s.as_code
Proof
  rw[asm_step_arith_def] >>
  gvs[asm_binop_def, asm_ternop_def, asm_next_def, AllCaseEqs()]
QED

Theorem asm_step_compare_code_preserved[local]:
  !name s s'.
    asm_step_compare name s = SOME (AsmOK s') ==> s'.as_code = s.as_code
Proof
  rw[asm_step_compare_def] >>
  gvs[asm_binop_def, asm_unop_def, asm_next_def, AllCaseEqs()]
QED

Theorem asm_step_bitwise_code_preserved[local]:
  !name s s'.
    asm_step_bitwise name s = SOME (AsmOK s') ==> s'.as_code = s.as_code
Proof
  rw[asm_step_bitwise_def] >>
  gvs[asm_binop_def, asm_unop_def, asm_next_def, AllCaseEqs()]
QED

Theorem asm_step_memory_code_preserved[local]:
  !name s s'.
    asm_step_memory name s = SOME (AsmOK s') ==> s'.as_code = s.as_code
Proof
  rw[asm_step_memory_def] >>
  gvs[asm_pop_def, asm_mload_def, asm_mstore_def, asm_mstore8_def,
      asm_mcopy_def, asm_push_val_def, asm_sload_def, asm_sstore_def,
      asm_tload_def, asm_tstore_def, asm_sha3_def,
      asm_next_def, AllCaseEqs()]
QED

Theorem asm_step_control_code_preserved[local]:
  !otp name s s'.
    asm_step_control otp name s = SOME (AsmOK s') ==>
    s'.as_code = s.as_code
Proof
  rw[asm_step_control_def] >>
  gvs[asm_jump_def, asm_jumpi_def, asm_return_op_def, asm_revert_op_def,
      asm_next_def, AllCaseEqs()]
QED

Theorem asm_step_copy_code_preserved[local]:
  !name s s'.
    asm_step_copy name s = SOME (AsmOK s') ==> s'.as_code = s.as_code
Proof
  rw[asm_step_copy_def] >>
  gvs[asm_copy_to_mem_def, asm_returndatacopy_def, asm_extcodecopy_def,
      asm_next_def, AllCaseEqs()]
QED

Theorem asm_step_context_code_preserved[local]:
  !name s s'.
    asm_step_context name s = SOME (AsmOK s') ==> s'.as_code = s.as_code
Proof
  rw[asm_step_context_def] >>
  gvs[asm_push_val_def, asm_state_unop_def, asm_gas_def,
      asm_next_def, AllCaseEqs()]
QED

Theorem asm_step_extcall_code_preserved[local]:
  !name s s'.
    asm_step_extcall name s = SOME (AsmOK s') ==> s'.as_code = s.as_code
Proof
  rw[asm_step_extcall_def] >>
  gvs[asm_exec_call_def, asm_exec_staticcall_def,
      asm_exec_delegatecall_def, asm_exec_create_def, asm_exec_create2_def,
      asm_selfdestruct_def, AllCaseEqs()] >>
  FIRST [drule asm_consume_call_outcome_code_preserved,
         drule asm_consume_create_outcome_code_preserved] >> simp[]
QED

Theorem asm_step_op_code_preserved:
  !otp name s s'.
    asm_step_op otp name s = AsmOK s' ==> s'.as_code = s.as_code
Proof
  rpt gen_tac >>
  simp[asm_step_op_def, AllCaseEqs()] >> strip_tac >>
  gvs[asm_dup_def, asm_swap_def, asm_log_def, asm_next_def, AllCaseEqs()] >>
  FIRST [drule asm_step_arith_code_preserved,
         drule asm_step_compare_code_preserved,
         drule asm_step_bitwise_code_preserved,
         drule asm_step_memory_code_preserved,
         drule asm_step_control_code_preserved,
         drule asm_step_extcall_code_preserved,
         drule asm_step_copy_code_preserved,
         drule asm_step_context_code_preserved] >> simp[]
QED

Theorem asm_step_code_preserved:
  !lo otp inst s s'.
    asm_step lo otp inst s = AsmOK s' ==> s'.as_code = s.as_code
Proof
  Cases_on `inst` >>
  simp[asm_step_def, asm_next_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[asm_step_op_code_preserved]
QED
