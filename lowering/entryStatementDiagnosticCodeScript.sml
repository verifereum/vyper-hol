Theory entryStatementDiagnosticCode
Ancestors
  entryCodePredicate entryContextCodePredicate entryTypedCopyCode
  entryAggregateCode entryValueCode entryLocationValueCode entryExpressionCode
  stmtLowering context compileEnv supportedStmts

Theorem entry_code_encode_log_topic[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_encode_log_topic value bs)
Proof
  Cases_on `bs` >> simp[compile_encode_log_topic_def, entry_code_return] >>
  rpt (irule entry_code_bind >> simp[entry_code_emit_op] >> rpt gen_tac)
QED

Theorem entry_code_log_topic_ops:
  !ops. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_log_topic_ops ops)
Proof
  Induct >> simp[compile_log_topic_ops_def, entry_code_return] >> rpt gen_tac >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_encode_log_topic] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return]
QED

Theorem entry_code_log_eval_all:
  !es. (!e ce et. MEM e es ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_expr ce et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_log_eval_all cenv es)
Proof
  Induct >> simp[compile_log_eval_all_def, entry_code_return] >> rpt strip_tac >>
  irule entry_code_bind >> reverse conj_tac
  >- (irule entry_code_lower_value >> metis_tac[]) >>
  rpt gen_tac >> BETA_TAC >>
  irule entry_code_bind >> reverse conj_tac >- (first_x_assum irule >> metis_tac[]) >>
  simp[entry_code_return]
QED

Theorem entry_code_log_store_data:
  !ops offset. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_log_store_data ce ops buf offset)
Proof
  Induct >> simp[compile_log_store_data_def, entry_code_return,
                 comp_ignore_bind_def] >> rpt gen_tac >>
  irule entry_code_bind >> reverse conj_tac >- simp[entry_code_emit_op] >>
  rpt gen_tac >> BETA_TAC >>
  irule entry_code_bind >> reverse conj_tac
  >- (rpt IF_CASES_TAC >> simp[entry_code_emit_void, entry_code_store_bytestring]) >>
  simp[]
QED

Theorem entry_code_revert_with_reason:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_revert_with_reason ce msg ty memsz)
Proof
  simp[compile_revert_with_reason_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_emit_void, entry_code_emit_op,
            entry_code_unwrap_value] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_inst]
QED

Theorem entry_code_literal_expression:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_expr ce ty (Literal source_ty lit))
Proof
  rw[entry_preserves_code_def] >>
  gvs[Once exprLoweringTheory.compile_expr_def] >>
  metis_tac[SRULE [entry_preserves_code_def] entry_code_literal_vv]
QED

Theorem entry_code_reason_message:
  supported_string_reason tops e ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_reason_message ce e)
Proof
  Cases_on `e`
  >~ [`compile_reason_message ce (Literal source_ty lit)`]
  >- (namedCases_on `source_ty` ["bt", "tys", "elem bound", "nsid", "flag", ""] >> Cases_on `lit` >>
      simp[supported_string_reason_def, compile_reason_message_def,
           entry_code_literal_expression] >>
      Cases_on `bt` >>
      simp[compile_reason_message_def, entry_code_literal_expression] >>
      irule entry_code_bind >> simp[entry_code_bytelike_literal, entry_code_return]) >>
  simp[supported_string_reason_def, compile_reason_message_def] >>
  metis_tac[entry_code_supported_pure_expr]
QED
