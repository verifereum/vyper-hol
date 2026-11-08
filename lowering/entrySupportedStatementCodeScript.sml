Theory entrySupportedStatementCode
Ancestors
  entryStatementStoreCode entryStatementDiagnosticCode entryStatementLoopCode
  entryStatementTargetSupport entryReturnCode entryExpressionCode
  entryCodePredicate entryContextCodePredicate entryAggregateCode entryValueCode entryLocationValueCode
  entryArithmeticCode entryTypedCopyCode entryEncoderCode
  stmtLowering exprLowering compileEnv supportedStmts supportedExprs list

Theorem entry_code_annassign[local]:
  (!ce' et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_expr ce' et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmt ce lc rt (AnnAssign id vty e))
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_local_alloca, entry_code_return] >>
    rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[entry_code_return, entry_code_unwrap_value]) >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_return] >> rpt gen_tac >> BETA_TAC) >>
  BasicProvers.TOP_CASE_TAC >> simp[entry_code_emit_void] >>
  rename1 `FLOOKUP _ _ = SOME binding` >> Cases_on `binding` >>
  simp[entry_code_emit_void] >> IF_CASES_TAC >>
  simp[entry_code_emit_void, entry_code_assign_value]
QED

Theorem entry_code_assign_stmt[local]:
  (!ce' et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_expr ce' et e)) /\
  (!ix ce' et. MEM ix (target_indices bt) ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_expr ce' et ix)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmt ce lc rt (Assign (BaseTarget bt) e))
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  IF_CASES_TAC
  >- (irule entry_code_bind >> simp[entry_code_store_at_loc] >>
      irule entry_code_get_target_ptr >> simp[]) >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- (simp[entry_code_return, entry_code_unwrap_value] >>
        irule entry_code_get_target_ptr >> simp[]) >>
    rpt gen_tac >> BETA_TAC) >>
  BasicProvers.TOP_CASE_TAC >> simp[entry_code_emit_void, entry_code_assign_value]
QED

Theorem entry_code_augassign[local]:
  (!ce' et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_expr ce' et e)) /\
  (!ix ce' et. MEM ix (target_indices bt) ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_expr ce' et ix)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmt ce lc rt (AugAssign target_ty bt bop e))
Proof
  strip_tac >>
  `!v (f : opcode -> unit compiler).
    comp_bind (comp_return v) f = f v` by
    simp[FUN_EQ_THM, comp_bind_def, comp_return_def] >>
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- (simp[entry_code_return] >> irule entry_code_get_target_ptr >> simp[]) >>
    rpt gen_tac >> BETA_TAC) >>
  BasicProvers.TOP_CASE_TAC >> simp[entry_code_emit_void] >>
  qmatch_goalsub_rename_tac `case loc of LocMemory => MLOAD | LocStorage => SLOAD | LocTransient => TLOAD | LocCode => MLOAD | LocCalldata => MLOAD` >> Cases_on `loc` >>
  simp[] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_return, entry_code_emit_op, entry_code_binop,
            entry_code_lower_value] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_void]
QED

Theorem entry_code_if_stmt[local]:
  (!ce' et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_expr ce' et e)) /\
  (!ce' lc' rt'. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_stmts ce' lc' rt' yes)) /\
  (!ce' lc' rt'. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_stmts ce' lc' rt' no)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmt ce lc rt (If e yes no))
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_lower_value, entry_code_fresh_label,
            entry_code_emit_inst, entry_code_new_block, entry_code_get,
            entry_code_return, entry_code_jmp_if_not_terminated] >>
    rpt gen_tac >> BETA_TAC) >>
  IF_CASES_TAC >> simp[entry_code_return] >>
  irule entry_code_bind >> simp[entry_code_new_block, entry_code_return]
QED

Theorem entry_code_append_stmt[local]:
  (!ce' et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_expr ce' et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmt ce lc rt (Append target e))
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac
  >- simp[entry_code_lower_value] >>
  rpt gen_tac >> BETA_TAC >>
  irule entry_code_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[entry_code_return] >>
      rpt (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_alloc_buffer, entry_code_store_memory] >>
        rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]) >>
  rpt gen_tac >> BETA_TAC >>
  irule entry_code_bind >> reverse conj_tac >- simp[entry_code_return] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_dynarray_append >>
  Cases_on `infer_array_location ce (target_to_expr target)` >>
  simp[load_opc_for_def, store_opc_for_def]
QED

Theorem entry_code_assert_stmt[local]:
  (!ce' et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_expr ce' et e)) /\
  (!reason. why = AssertReason reason ==> supported_string_reason tops reason) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmt ce lc rt (Assert e why))
Proof
  strip_tac >> Cases_on `why` >>
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- (simp[entry_code_lower_value, entry_code_fresh_label,
            entry_code_emit_inst, entry_code_new_block, entry_code_return,
            entry_code_revert_with_reason] >>
        irule entry_code_reason_message >> metis_tac[]) >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_raise_stmt[local]:
  (!reason. why = RaiseReason reason ==> supported_string_reason tops reason) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmt ce lc rt (Raise why))
Proof
  strip_tac >> Cases_on `why` >>
  simp[Once compile_stmt_def, entry_code_emit_inst, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_inst] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return] >>
  irule entry_code_bind >> reverse conj_tac
  >- (irule entry_code_reason_message >> metis_tac[]) >>
  simp[entry_code_revert_with_reason]
QED


Theorem entry_code_normalize_return[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (if needs then
       do buf <- compile_alloc_buffer buf_size;
          ptr <- comp_return buf.buf_operand;
          compile_store_memory_typed ce ptr ty v src_ty;
          comp_return ptr od
     else comp_return v)
Proof
  IF_CASES_TAC >> simp[comp_ignore_bind_def, entry_code_return] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_return,
            entry_code_store_memory_typed] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return]
QED

Theorem entry_code_return_some_stmt[local]:
  (!ce' et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_expr ce' et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmt ce lc rt (Return (SOME e)))
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac
  >- simp[entry_code_lower_value] >> rpt gen_tac >> BETA_TAC >>
  Cases_on `ce.ce_return_pc`
  >- (simp[] >> irule entry_code_bind >>
      simp[SRULE [comp_ignore_bind_def] entry_code_normalize_return, entry_code_external_return,
           comp_ignore_bind_def]) >>
  rename1 `SOME binding` >> Cases_on `binding` >>
  simp[entry_code_internal_return_from_env] >>
  irule entry_code_bind >>
  simp[entry_code_emit_op, entry_code_internal_return_from_env,
       SRULE [comp_ignore_bind_def] entry_code_normalize_return, entry_code_external_return,
       comp_ignore_bind_def]
QED

Theorem entry_code_log_stmt[local]:
  (!e ce' et. MEM e es ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_expr ce' et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmt ce lc rt (Log ev_id es))
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[entry_code_emit_inst] >>
  PairCases_on `x` >> simp[] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- (simp[entry_code_return, entry_code_log_topic_ops] >>
        irule entry_code_log_eval_all >> simp[]) >>
    rpt gen_tac >> BETA_TAC) >>
  IF_CASES_TAC >> simp[entry_code_emit_inst] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_return,
            entry_code_log_store_data, entry_code_encode_to_buf] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_emit_inst]
QED

Theorem entry_code_return_none_stmt[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmt ce lc rt (Return NONE))
Proof
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  Cases_on `ce.ce_return_pc`
  >- (simp[] >> Cases_on `ce.ce_ctor_exit_label` >>
      simp[entry_code_emit_inst] >>
      CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
      irule entry_code_bind >> simp[entry_code_emit_inst] >>
      IF_CASES_TAC >> simp[entry_code_return, entry_code_nonreentrant_unlock]) >>
  rename1 `SOME binding` >> Cases_on `binding` >>
  simp[entry_code_emit_inst] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_inst] >>
  Cases_on `ce.ce_ctor_exit_label` >> simp[entry_code_emit_inst] >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  irule entry_code_bind >> simp[entry_code_emit_inst] >>
  IF_CASES_TAC >> simp[entry_code_return, entry_code_nonreentrant_unlock]
QED

Theorem entry_code_tuple_assign_stmt[local]:
  (!ce' et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_expr ce' et e)) /\
  (!bt ix ce' et. MEM (BaseTarget bt) targets /\ MEM ix (target_indices bt) ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_expr ce' et ix)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmt ce lc rt (Assign (TupleTarget targets) e))
Proof
  strip_tac >> simp[Once compile_stmt_def] >>
  irule entry_code_bind >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >> reverse conj_tac
  >- simp[entry_code_unwrap_value] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_tuple_unpack >> metis_tac[]
QED

Theorem entry_code_supported_statements[local]:
  (!tops bindings s. supported_stmt tops bindings s ==>
    !ce lc rt. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_stmt ce lc rt s)) /\
  (!tops bindings ss. supported_stmts tops bindings ss ==>
    !ce lc rt. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_stmts ce lc rt ss))
Proof
  ho_match_mp_tac supported_stmt_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`compile_stmt _ _ _ Pass`] >- simp[compile_stmt_def, entry_code_return]
  >~ [`compile_stmt _ _ _ Break`] >- suspend "break"
  >~ [`compile_stmt _ _ _ Continue`] >- suspend "continue"
  >~ [`compile_stmt _ _ _ (Expr _)`] >- suspend "expr"
  >~ [`compile_stmt _ _ _ (Return NONE)`] >- simp[entry_code_return_none_stmt]
  >~ [`compile_stmt _ _ _ (Return (SOME _))`] >- (
    simp[supported_stmt_def] >> metis_tac[entry_code_return_some_stmt, entry_code_supported_expr])
  >~ [`compile_stmt _ _ _ (AnnAssign _ _ _)`] >- (
    simp[supported_stmt_def] >> metis_tac[entry_code_annassign, entry_code_supported_expr])
  >~ [`compile_stmt _ _ _ (Assign _ _)`] >- suspend "assign"
  >~ [`compile_stmt _ _ _ (AugAssign _ _ _ _)`] >- suspend "augassign"
  >~ [`compile_stmt _ _ _ (Append _ _)`] >- (
    simp[supported_stmt_def] >> metis_tac[entry_code_append_stmt, entry_code_supported_pure_expr])
  >~ [`compile_stmt _ _ _ (If _ _ _)`] >- (
    simp[supported_stmt_def] >> metis_tac[entry_code_if_stmt, entry_code_supported_pure_expr])
  >~ [`compile_stmt _ _ _ (Assert _ _)`] >- suspend "assert"
  >~ [`compile_stmt _ _ _ (Raise _)`] >- suspend "raise"
  >~ [`compile_stmt _ _ _ (Log _ _)`] >- suspend "log"
  >~ [`compile_stmt _ _ _ (For _ _ _ _ _)`] >- (
    simp[supported_stmt_def] >> metis_tac[entry_code_supported_for])
  >~ [`compile_stmts _ _ _ []`] >- simp[compile_stmt_def, entry_code_return]
  >> suspend "cons"
QED

Resume entry_code_supported_statements[break]:
  strip_tac >> rpt gen_tac >> Cases_on `lc` >>
  simp[compile_stmt_def, entry_code_emit_inst, comp_ignore_bind_def] >>
  irule entry_code_bind >> simp[entry_code_emit_inst, entry_code_return]
QED
Resume entry_code_supported_statements[continue]:
  strip_tac >> rpt gen_tac >> Cases_on `lc` >>
  simp[compile_stmt_def, entry_code_emit_inst, comp_ignore_bind_def] >>
  irule entry_code_bind >> simp[entry_code_emit_inst, entry_code_return]
QED
Resume entry_code_supported_statements[expr]:
  simp[supported_stmt_def, Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt strip_tac >> irule entry_code_bind >> simp[entry_code_return] >>
  metis_tac[entry_code_supported_expr]
QED
Resume entry_code_supported_statements[assign]:
  strip_tac >> rpt gen_tac >> Cases_on `target`
  >- (irule entry_code_assign_stmt >>
      gvs[supported_stmt_def] >>
      metis_tac[entry_code_supported_expr, supported_assignment_base_index,
                supported_assignment_def]) >>
  irule entry_code_tuple_assign_stmt >> gvs[supported_stmt_def] >>
  metis_tac[entry_code_supported_expr, supported_assignment_tuple_index,
            supported_assignment_def]
QED
Resume entry_code_supported_statements[augassign]:
  simp[supported_stmt_def] >> rpt strip_tac >> irule entry_code_augassign >>
  metis_tac[entry_code_supported_expr, supported_target_index,
            supported_aug_target_index]
QED
Resume entry_code_supported_statements[assert]:
  simp[supported_stmt_def] >> rpt strip_tac >> irule entry_code_assert_stmt >>
  Cases_on `reason` >> gvs[supported_assert_reason_def] >>
  metis_tac[entry_code_supported_pure_expr]
QED
Resume entry_code_supported_statements[raise]:
  simp[supported_stmt_def] >> rpt strip_tac >> irule entry_code_raise_stmt >>
  Cases_on `reason` >> gvs[supported_raise_reason_def] >> metis_tac[]
QED
Resume entry_code_supported_statements[log]:
  simp[supported_stmt_def, supported_log_def] >> rpt strip_tac >>
  irule entry_code_log_stmt >>
  gvs[supported_pure_exprs_every, EVERY_MEM] >>
  metis_tac[entry_code_supported_pure_expr]
QED
Resume entry_code_supported_statements[cons]:
  simp[supported_stmt_def] >> rpt strip_tac >>
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  irule entry_code_bind >> simp[entry_code_get] >> gen_tac >>
  IF_CASES_TAC >> simp[entry_code_return] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_declare_stmt_local] >> rpt gen_tac >> BETA_TAC) >> simp[]
QED
Finalise entry_code_supported_statements

Theorem entry_code_supported_stmt:
  supported_stmt tops bindings s ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_stmt ce lc rt s)
Proof
  metis_tac[entry_code_supported_statements]
QED

Theorem entry_code_supported_stmts:
  supported_stmts tops bindings ss ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_stmts ce lc rt ss)
Proof
  metis_tac[entry_code_supported_statements]
QED
