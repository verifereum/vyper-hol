Theory runtimeSymSrcStatements
Ancestors
  runtimeSymSrcStatementAssignFamily runtimeSymSrcStatementExits
  runtimeSymSrcStatementAssignClosed runtimeSymSrcStatementExitClosed
  runtimeSymSrcStatementReasons runtimeSymSrcGeneratorContracts
  runtimeSymSrcStatementControl runtimeSymSrcStatementRange
  runtimeSymSrcStatementControlComplete runtimeSymSrcContextComplete
  runtimeSymSrcOpenValues runtimeSymSrcBinops runtimeSymSrcModuleBodies
  runtimeSymSrcLiteralEnv runtimeSymSrcDeclarations supportedStmts
  runtimeSymSrcInterfaces stmtLowering compileEnv supportedStmtTraverse vyperAST

Theorem runtime_sym_stmts_nil:
  runtime_sym_stmts_contract tops bs compile_stmts ce lc ty []
Proof
  simp[runtime_sym_stmts_contract_def, compile_stmt_def, comp_return_def]
QED

Theorem runtime_sym_stmts_cons:
  (!ce. runtime_sym_stmt_contract tops bs compile_stmt ce lc ty stmt) /\
  (!ce. runtime_sym_stmts_contract tops bs compile_stmts ce lc ty stmts) ==>
  runtime_sym_stmts_contract tops bs compile_stmts ce lc ty (stmt::stmts)
Proof
  simp[runtime_sym_stmts_contract_def, runtime_sym_stmt_contract_def] >>
  rpt strip_tac >>
  gvs[Once compile_stmt_def, comp_get_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >>
  Cases_on `block_is_terminated s` >>
  gvs[comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all runtime_sym_declare_stmt_local >> strip_tac >>
  fs[supported_stmt_def, supported_stmt_expr_exists_def] >>
  metis_tac[]
QED


Theorem runtime_sym_stmts_from_members:
  !stmts ce.
  (!stmt. MEM stmt stmts ==>
    !ce. runtime_sym_stmt_contract tops bs compile_stmt ce lc ty stmt) ==>
  runtime_sym_stmts_contract tops bs compile_stmts ce lc ty stmts
Proof
  Induct >> simp[runtime_sym_stmts_nil] >> rpt gen_tac >> strip_tac >>
  irule runtime_sym_stmts_cons >> simp[] >> metis_tac[]
QED

(* Residual ledger: expressions belong to C1.1.4; target-pointer, append
   and ABI encoding preservation belong to C1.1.3. All statement families
   and all proper-body recursion are closed below, with semantic parameters
   universally quantified so loop and declaration callbacks may change them. *)
Theorem runtime_sym_stmt:
  (!ce ty e. runtime_sym_expr_contract tops compile_expr ce ty e) /\
  (!ce bs bt e s op loc pt s'. runtime_sym_env ce /\
    supported_assignment tops bs (BaseTarget bt) e /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ce bs bt s op loc pt s'. runtime_sym_env ce /\
    (supported_target tops bs bt \/ supported_aug_target tops bs bt) /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ce base v ws es et st cap prim load store s u s'.
    ~is_label_operand base /\ ~is_label_operand v /\
    load <> CODESIZE /\ load <> CODECOPY /\
    store <> CODESIZE /\ store <> CODECOPY /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_dynarray_append ce base v ws es et st cap prim load store s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  !stmt bs ce lc ty.
    runtime_sym_stmt_contract tops bs compile_stmt ce lc ty stmt
Proof
  strip_tac >>
  mp_tac runtime_sym_lower_value >>
  (impl_tac >- metis_tac[runtime_sym_unwrap_value]) >>
  rewrite_tac[runtime_sym_lower_value_clause_def] >> strip_tac >>
  ho_match_mp_tac stmt_induction >> rpt conj_tac
  >- simp[runtime_sym_stmt_pass]
  >- simp[runtime_sym_stmt_continue]
  >- simp[runtime_sym_stmt_break]
  >- metis_tac[runtime_sym_stmt_expr]
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `i`
      >- (match_mp_tac runtime_sym_stmt_for_array >> conj_tac
          >- metis_tac[] >>
          rpt gen_tac >> irule runtime_sym_stmts_from_members >> metis_tac[]) >>
      match_mp_tac runtime_sym_stmt_for_range >> conj_tac
      >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
          qpat_x_assum `!cfn ce ty e s op s'. _`
            (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
          disch_then match_mp_tac >> metis_tac[]) >>
      rpt gen_tac >> irule runtime_sym_stmts_from_members >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      match_mp_tac runtime_sym_stmt_if >> conj_tac
      >- (rpt gen_tac >> strip_tac >>
          qpat_x_assum `!cfn ce ty e s op s'. _`
            (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
          disch_then match_mp_tac >> metis_tac[]) >> conj_tac >>
      irule runtime_sym_stmts_from_members >> metis_tac[])
  >> qpat_x_assum `!cfn ce ty e s op s'. _` kall_tac
  >- (rpt gen_tac >> Cases_on `a` >>
      simp[runtime_sym_assert_bare_closed,
        runtime_sym_assert_unreachable_closed, runtime_sym_assert_reason_closed] >>
      simp[runtime_sym_stmt_contract_def, supported_stmt_def, supported_assert_reason_def])
  >- (rpt gen_tac >> match_mp_tac runtime_sym_log_closed >> conj_tac
      >- simp[] >> first_assum MATCH_ACCEPT_TAC)
  >- (gen_tac >> Cases_on `r` >>
      simp[runtime_sym_stmt_raise_bare, runtime_sym_stmt_raise_unreachable,
        runtime_sym_raise_reason_closed] >>
      simp[runtime_sym_stmt_contract_def, supported_stmt_def, supported_raise_reason_def])
  >- (gen_tac >> Cases_on `o'` >- simp[runtime_sym_return_none_closed] >>
      rpt gen_tac >> match_mp_tac runtime_sym_return_some_closed >> conj_tac
      >- simp[] >> first_assum MATCH_ACCEPT_TAC)
  >- (rpt gen_tac >> Cases_on `a`
      >- (match_mp_tac runtime_sym_assignment_baseassign_closed >> conj_tac
          >- simp[] >> first_assum MATCH_ACCEPT_TAC) >>
      match_mp_tac runtime_sym_assignment_tupleassign_closed >> conj_tac
      >- simp[] >> metis_tac[])
  >- (rpt gen_tac >> match_mp_tac runtime_sym_assignment_augassign_closed >>
      conj_tac >- first_assum MATCH_ACCEPT_TAC >> simp[])
  >- (rpt gen_tac >> match_mp_tac runtime_sym_assignment_append_closed >>
      conj_tac >- simp[] >> first_assum MATCH_ACCEPT_TAC)
  >> simp[runtime_sym_assignment_annassign_closed]
QED

Theorem runtime_sym_stmts:
  (!ce ty e. runtime_sym_expr_contract tops compile_expr ce ty e) /\
  (!ce bs bt e s op loc pt s'. runtime_sym_env ce /\
    supported_assignment tops bs (BaseTarget bt) e /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ce bs bt s op loc pt s'. runtime_sym_env ce /\
    (supported_target tops bs bt \/ supported_aug_target tops bs bt) /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ce base v ws es et st cap prim load store s u s'.
    ~is_label_operand base /\ ~is_label_operand v /\
    load <> CODESIZE /\ load <> CODECOPY /\
    store <> CODESIZE /\ store <> CODECOPY /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_dynarray_append ce base v ws es et st cap prim load store s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  !stmts bs ce lc ty.
    runtime_sym_stmts_contract tops bs compile_stmts ce lc ty stmts
Proof
  strip_tac >> rpt gen_tac >> irule runtime_sym_stmts_from_members >>
  rpt gen_tac >> strip_tac >> irule runtime_sym_stmt >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
