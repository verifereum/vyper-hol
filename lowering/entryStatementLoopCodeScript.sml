Theory entryStatementLoopCode
Ancestors
  entryStatementStoreCode entryStatementDiagnosticCode
  entryCodePredicate entryContextCodePredicate entryLocationValueCode
  entryTypedCopyCode entryAggregateCode entryExpressionCode entryValueCode supportedStmts
  stmtLowering exprLowering context compileEnv emitHelper

Theorem entry_code_range_bound_checks[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_range_bound_checks start end_op rounds bound signed)
Proof
  Cases_on `signed` >>
  simp[compile_range_bound_checks_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_emit_void]
QED

Theorem entry_code_iter_elem_copy[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_iter_elem_copy ce src dst elem_bytes loc slots ty ety)
Proof
  Cases_on `slots` >> Cases_on `loc` >>
  simp[compile_iter_elem_copy_def, compile_slot_to_memory_def,
       entry_code_word_copy_loop, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >>
  simp[entry_code_return, entry_code_copy_memory,
       entry_code_imm_copy_to_memory, entry_code_store_memory,
       entry_code_emit_void] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_word_copy_loop, entry_code_ptr_load, entry_code_emit_op] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return, entry_code_emit_void]
QED

Theorem entry_code_dynarray_append:
  load_opc <> DALLOCA /\ store_opc <> DALLOCA ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_dynarray_append ce base_op val_op scale elem_bytes dty sty cap prim
       load_opc store_opc)
Proof
  strip_tac >> simp[compile_dynarray_append_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (rpt IF_CASES_TAC >> simp[entry_code_emit_void] >>
      irule entry_code_bind >>
      simp[entry_code_store_memory, entry_code_word_copy_loop,
           entry_code_return]) >>
  rpt gen_tac >> BETA_TAC >>
  irule entry_code_bind >> simp[entry_code_emit_op, entry_code_emit_void]
QED

Theorem entry_code_jmp_if_not_terminated:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (emit_jmp_if_not_terminated lbl)
Proof
  simp[emit_jmp_if_not_terminated_def] >>
  irule entry_code_bind >> simp[entry_code_get] >>
  gen_tac >> IF_CASES_TAC >> simp[entry_code_return, entry_code_emit_inst]
QED

Theorem entry_code_range_loop_callback[local]:
  (!ce' et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_expr ce' et start_e)) /\
  (!ce' et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_expr ce' et end_e)) /\
  (!ce' lc' rt'. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_stmts ce' lc' rt' stmts)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmt ce lc rt (For id fty (Range start_e end_e) bound stmts))
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_lower_value, entry_code_declare_local,
            entry_code_emit_local_alloca, entry_code_fresh_label,
            entry_code_fresh_var, entry_code_emit_inst, entry_code_new_block] >>
    rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (POP_ASSUM_LIST (K all_tac) >>
      namedCases_on `start_e` ["", "", "", "", "ann lit", "", "", "", "", "", "", ""] >>
      simp[entry_code_emit_op, entry_code_return] >>
      Cases_on `lit` >> simp[entry_code_emit_op, entry_code_return] >>
      namedCases_on `end_e` ["", "", "", "", "ann2 lit2", "", "", "", "", "", "", ""] >>
      simp[entry_code_emit_op, entry_code_return] >> Cases_on `lit2` >>
      simp[entry_code_emit_op, entry_code_return]) >>
  rpt gen_tac >> BETA_TAC >>
  irule entry_code_bind >> reverse conj_tac
  >- (POP_ASSUM_LIST (K all_tac) >>
      namedCases_on `start_e` ["", "", "", "", "ann lit", "", "", "", "", "", "", ""] >>
      simp[entry_code_range_bound_checks, entry_code_return] >>
      Cases_on `lit` >> simp[entry_code_range_bound_checks, entry_code_return] >>
      namedCases_on `end_e` ["", "", "", "", "ann2 lit2", "", "", "", "", "", "", ""] >>
      simp[entry_code_range_bound_checks, entry_code_return] >> Cases_on `lit2` >>
      simp[entry_code_range_bound_checks, entry_code_return]) >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_inst, entry_code_new_block] >>
    rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (BasicProvers.TOP_CASE_TAC >> simp[entry_code_emit_void] >>
      Cases_on `x` >> simp[entry_code_emit_void]) >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_jmp_if_not_terminated, entry_code_new_block,
            entry_code_emit_op, entry_code_emit_inst] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_array_loop_callback[local]:
  (!ce' et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_expr ce' et arr_e)) /\
  (!ce' lc' rt'. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_stmts ce' lc' rt' stmts)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmt ce lc rt (For id fty (Array arr_e) bound stmts))
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_return] >> rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[entry_code_ptr_load, entry_code_return]) >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_declare_local, entry_code_emit_local_alloca,
            entry_code_fresh_label, entry_code_fresh_var,
            entry_code_emit_inst, entry_code_new_block] >>
    rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[entry_code_return] >>
      rpt (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
      simp[entry_code_emit_void]) >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_inst, entry_code_new_block,
            entry_code_return] >> rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[entry_code_emit_op, entry_code_return]) >>
  rpt gen_tac >> BETA_TAC >>
  irule entry_code_bind >> reverse conj_tac >- simp[entry_code_emit_op] >>
  rpt gen_tac >> BETA_TAC >>
  irule entry_code_bind >> reverse conj_tac
  >- (BasicProvers.TOP_CASE_TAC >> simp[entry_code_emit_void] >>
      rename1 `FLOOKUP _ _ = SOME binding` >>
      Cases_on `binding` >> simp[entry_code_emit_void, entry_code_iter_elem_copy]) >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_jmp_if_not_terminated, entry_code_new_block,
            entry_code_emit_op, entry_code_emit_inst] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_supported_for:
  supported_iterator tops fty iter bound /\
  (!ce' lc' rt'. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_stmts ce' lc' rt' stmts)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmt ce lc rt (For id fty iter bound stmts))
Proof
  reverse (Cases_on `iter`) >> strip_tac
  >- (irule entry_code_range_loop_callback >> simp[] >>
      namedCases_on `e` ["", "", "", "", "ann lit", "", "", "", "", "", "", ""] >>
      gvs[supported_iterator_def]
      >~ [`entry_preserves_code _ (compile_expr _ _ (Literal _ _))`] >- (
        namedCases_on `e0` ["", "", "", "", "ann2 lit2", "", "", "", "", "", "", ""] >> gvs[]
        >~ [`(!xce et. entry_preserves_code _ (compile_expr xce et (Literal _ _))) /\ (!xce et. entry_preserves_code _ (compile_expr xce et (Literal _ _)))`] >- (
          Cases_on `lit` >> Cases_on `lit2` >> gvs[] >>
          metis_tac[entry_code_supported_pure_expr, entry_code_literal_expression]) >>
        metis_tac[entry_code_supported_pure_expr]) >>
      metis_tac[entry_code_supported_pure_expr]) >>
  drule supported_array_iterator_shape >> strip_tac >> gvs[] >>
  irule entry_code_array_loop_callback >> simp[] >>
  rpt gen_tac >> simp[entry_preserves_code_def, Once compile_expr_def] >>
  rewrite_tac[GSYM entry_preserves_code_def] >> irule entry_code_name_vv
QED
