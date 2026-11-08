Theory bodyPtrBytestringBuiltinsOpcodeEffects
Ancestors bodyPtrBytestringBuiltinsOpcodeStmtMemory
          bodyPtrBytestringBuiltinsOpcodeMemory
          bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState
          bodyPtrBytestringBuiltinsOpcodeAbiEncode
          bodyPtrBytestringBuiltinsOpcodeSyntax
          bodyPtrBytestringBuiltinsOpcodeExpressions
          stmtLowering context supportedStmts supportedExprs list
Libs BasicProvers

Theorem no_extcode_nonreentrant_lock:
  !k trans view s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_nonreentrant_lock k trans view s))
Proof
  rpt strip_tac >> simp[compile_nonreentrant_lock_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_nonreentrant_unlock:
  !k trans view s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_nonreentrant_unlock k trans view s))
Proof
  rpt strip_tac >> simp[compile_nonreentrant_unlock_def] >>
  rpt (IF_CASES_TAC >> simp[no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_mcopy_guard:
  (!s. compiler_no_extcode s ==> compiler_no_extcode (SND (action s))) ==>
  !ce s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_mcopy_guard ce action s))
Proof
  rpt strip_tac >> simp[compile_mcopy_guard_def] >>
  IF_CASES_TAC >> simp[no_extcode_emit_inst]
QED

Theorem no_extcode_internal_return:
  !ce rv rpc count rt st elems buf s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_internal_return ce rv rpc count rt st elems buf s))
Proof
  rpt gen_tac >> Cases_on `rv` >> Cases_on `buf` >> strip_tac >>
  simp[compile_internal_return_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_inst, no_extcode_store_memory, no_extcode_load_tuple_elements]) >>
  simp[no_extcode_emit_inst]
QED

Theorem no_extcode_internal_return_from_env:
  !ce ty st v rpc s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_internal_return_from_env ce ty st v rpc s))
Proof
  rpt strip_tac >> simp[compile_internal_return_from_env_def] >>
  namedCases_on `ce.ce_return_buf` ["", "rbuf"] >> simp[] >>
  TRY (Cases_on `rbuf` >> simp[]) >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_fresh_ops, no_extcode_internal_return, no_extcode_emit_op])
QED

Theorem no_extcode_external_return:
  !rv prim raw enc sz nr k trans view s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_external_return rv prim raw enc sz nr k trans view s))
Proof
  rpt gen_tac >> Cases_on `rv` >> strip_tac >> simp[compile_external_return_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_nonreentrant_unlock, no_extcode_emit_inst, no_extcode_emit_op,
      no_extcode_emit_void, no_extcode_fresh_ops, no_extcode_alloc_buffer,
      cj 2 no_extcode_abi_encode])
QED

Theorem no_extcode_revert_with_reason:
  !ce vv ty sz s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_revert_with_reason ce vv ty sz s))
Proof
  rpt strip_tac >> simp[compile_revert_with_reason_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_alloc_buffer, no_extcode_unwrap_value, no_extcode_emit_op,
      no_extcode_emit_void, no_extcode_emit_inst])
QED

Theorem no_extcode_encode_log_topic:
  !op bs s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_encode_log_topic op bs s))
Proof
  rpt strip_tac >> simp[compile_encode_log_topic_def] >>
  IF_CASES_TAC >> simp[no_extcode_fresh_ops] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >> simp[no_extcode_emit_op])
QED

Theorem no_extcode_log_topic_ops:
  !ops s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_log_topic_ops ops s))
Proof
  Induct >> simp[compile_log_topic_ops_def, no_extcode_fresh_ops] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_encode_log_topic, no_extcode_fresh_ops])
QED

Theorem no_extcode_log_store_data:
  !ce ops buf off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_log_store_data ce ops buf off s))
Proof
  gen_tac >> Induct >> simp[compile_log_store_data_def, no_extcode_fresh_ops] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_store_bytestring])
QED

Theorem no_extcode_log_eval_all:
  !es tops ce s. supported_pure_exprs tops es /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_log_eval_all ce es s))
Proof
  Induct >> simp[compile_log_eval_all_def, supported_pure_exprs_every,
    no_extcode_fresh_ops] >> rpt strip_tac >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_fresh_ops])
  >- metis_tac[supported_pure_exprs_every] >>
  rpt strip_tac >> irule no_extcode_lower_value >> rpt strip_tac >>
  metis_tac[no_extcode_compile_expr_supported]
QED

Theorem no_extcode_reason_message:
  !tops ce e s. supported_string_reason tops e /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_reason_message ce e s))
Proof
  rpt gen_tac >> Cases_on `e` >>
  simp[supported_string_reason_def] >> rpt strip_tac >>
  TRY (rename1 `Literal ann lit` >> Cases_on `lit` >>
    gvs[supported_string_reason_def] >>
    Cases_on `ann` >> simp[compile_reason_message_def, no_extcode_compile_literal] >>
    TRY (rename1 `BaseT bt` >> Cases_on `bt` >>
      simp[compile_reason_message_def, no_extcode_compile_literal]) >>
    rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
      irule no_extcode_bind, irule no_extcode_ignore_bind] >>
      simp[no_extcode_bytelike_literal, no_extcode_fresh_ops]) >> NO_TAC) >>
  simp[compile_reason_message_def] >>
  metis_tac[no_extcode_compile_expr_supported]
QED
