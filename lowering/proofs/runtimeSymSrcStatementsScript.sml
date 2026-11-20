Theory runtimeSymSrcStatements
Ancestors
  runtimeSymSrcStatementAssignFamily
  runtimeSymSrcStatementAssignClosed runtimeSymSrcStatementExitClosed
  runtimeSymSrcStatementReasons runtimeSymSrcGeneratorContracts
  runtimeSymSrcStatementControl runtimeSymSrcStatementRange
  runtimeSymSrcStatementControlComplete runtimeSymSrcContextComplete
  runtimeSymSrcOpenValues runtimeSymSrcBinops runtimeSymSrcModuleBodies
  runtimeSymSrcLiteralEnv runtimeSymSrcDeclarations supportedStmts
  runtimeSymSrcInterfaces stmtLowering compileEnv supportedStmtTraverse vyperAST
  runtimeSymSrcContext runtimeSymSrcContextTyped runtimeSymSrcSimpleCalls
  runtimeSymSrcEmission runtimeSymSrcBlockEmission
  context loweringShapeDefs emitHelper supportedExprs supportedExprTraverse list venomInst stackPlanTypes

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

Theorem runtime_sym_custom_error_store_args[local]:
  !args tys ce dst off s u s'.
    (!e t. MEM e args ==> runtime_sym_expr_contract tops compile_expr ce t e) /\
    runtime_sym_env tops ce /\ EVERY (supported_pure_expr tops) args /\
    ~supported_exprs_exists is_self_code args /\ ~is_label_operand dst /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_custom_error_store_args ce args tys dst off s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  Induct >> Cases_on `tys` >>
  simp[compile_custom_error_store_args_def, comp_return_def,
    comp_bind_def, comp_ignore_bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rename1 `compile_expr ce (expr_type arg) arg s = _` >>
  `supported_expr tops arg /\ ~supported_expr_exists is_self_code arg` by
    gvs[supported_expr_def, supported_exprs_exists_every] >>
  `runtime_sym_expr_contract tops compile_expr ce (expr_type arg) arg` by
    (qpat_assum `!e t. _ ==> runtime_sym_expr_contract _ _ _ _ _` irule >> simp[]) >>
  qpat_x_assum `runtime_sym_expr_contract tops compile_expr ce _ _`
    (mp_tac o Q.SPEC `s` o REWRITE_RULE [runtime_sym_expr_contract_def]) >>
  simp[] >> strip_tac >>
  qpat_x_assum `(if off = 0 then _ else _) _ = _` mp_tac >>
  Cases_on `off = 0` >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  TRY (qpat_assum `emit_op ADD _ _ = _`
         (mp_then Any mp_tac runtime_sym_emit_op) >>
       simp[is_label_operand_def] >> strip_tac) >>
  drule_all runtime_sym_unwrap_value >> strip_tac >>
  drule_all runtime_sym_store_memory >> strip_tac >>
  qpat_assum `!tys ce dst off s s'. _ ==> _`
    (drule_at (Pat `compile_custom_error_store_args _ _ _ _ _ _ = _`)) >>
  fs[supported_exprs_exists_every] >> metis_tac[]
QED

Theorem runtime_sym_custom_error[local]:
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!e t. MEM e (custom_error_exprs err) ==>
    runtime_sym_expr_contract tops compile_expr ce t e) /\
  runtime_sym_env tops ce /\ EVERY (supported_pure_expr tops) (custom_error_exprs err) /\
  ~supported_exprs_exists is_self_code (custom_error_exprs err) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_revert_with_custom_error ce err s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `err` >> rename1 `CustomError id pos kw` >>
  Cases_on `ce.ce_error_info (nsid_to_string id)` >>
  simp[compile_revert_with_custom_error_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]
  >- metis_tac[runtime_sym_call_invalid] >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  qpat_assum `compile_custom_error_store_args _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_custom_error_store_args) >>
  disch_then (qspec_then `tops` mp_tac) >> simp[] >> strip_tac >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  qpat_assum `emit_void MSTORE _ _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `(if NULL _ then _ else _) _ = _` mp_tac >>
  Cases_on `NULL (custom_error_exprs (CustomError id pos kw))` >>
  simp[comp_bind_def] >> rpt (pairarg_tac >> simp[]) >> strip_tac >>
  TRY (qpat_assum `emit_op ADD [_;Lit 32w] _ = _`
         (mp_then Any mp_tac runtime_sym_emit_op) >>
       simp[is_label_operand_def] >> strip_tac >>
       qpat_assum `!b v info s op s'. _ ==> _`
         (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
       simp[] >> strip_tac) >>
  qpat_assum `emit_op ADD [_;Lit 28w] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  TRY (qpat_assum `emit_op ADD [Lit 4w;_] _ = _`
         (mp_then Any mp_tac runtime_sym_emit_op) >>
       simp[is_label_operand_def] >> strip_tac) >>
  qpat_assum `emit_inst REVERT _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_inst) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >> irule runtime_sym_labeled_inst >> simp[is_label_operand_def]
QED

Theorem runtime_sym_stmt_raise_custom[local]:
  (!ce ty e. runtime_sym_expr_contract tops compile_expr ce ty e) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_stmt_contract tops bs compile_stmt ce lc ty (Raise (RaiseCustomError err))
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_stmt_contract_def] >> rpt gen_tac >>
  simp[Once compile_stmt_def, supported_stmt_def, supported_stmt_expr_exists_def,
       supported_raise_reason_def, supported_raise_exists_def] >>
  strip_tac >>
  qpat_assum `compile_revert_with_custom_error _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_custom_error) >>
  disch_then (qspec_then `tops` mp_tac) >> simp[supported_exprs_exists_every] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem runtime_sym_stmt_assert_custom[local]:
  (!ce ty e. runtime_sym_expr_contract tops compile_expr ce ty e) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_stmt_contract tops bs compile_stmt ce lc ty (Assert cond (AssertCustomError err))
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_stmt_contract_def] >> rpt gen_tac >>
  simp[NoAsms, Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  ntac 7 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  `runtime_sym_lower_value_clause tops` by
    (irule runtime_sym_lower_value >> metis_tac[runtime_sym_unwrap_value]) >>
  rename1 `lower_value compile_expr ce (BaseT BoolT) cond s = (cond_op,cond_state)` >>
  `supported_expr tops cond /\ ~supported_expr_exists is_self_code cond` by
    fs[supported_stmt_def, supported_stmt_expr_exists_def, supported_expr_def] >>
  `EVERY runtime_sym_inst (state_insts cond_state) /\ ~is_label_operand cond_op` by
    (qpat_assum `runtime_sym_lower_value_clause tops`
       (mp_tac o REWRITE_RULE [runtime_sym_lower_value_clause_def]) >>
     disch_then (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >> simp[]) >>
  qpat_assum `fresh_label "assert_ok" _ = _`
    (mp_then Any strip_assume_tac runtime_sym_fresh_label) >>
  qpat_assum `fresh_label "assert_fail" _ = _`
    (mp_then Any strip_assume_tac runtime_sym_fresh_label) >>
  qpat_assum `emit_inst JNZ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_jnz) >> simp[] >> strip_tac >>
  imp_res_tac runtime_sym_new_block_result >>
  qpat_assum `compile_revert_with_custom_error _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_custom_error) >>
  disch_then (qspec_then `tops` mp_tac) >>
  fs[supported_stmt_def, supported_stmt_expr_exists_def,
      supported_assert_reason_def, supported_assert_exists_def, supported_exprs_exists_every] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

(* Residual ledger: expressions belong to C1.1.4; target-pointer, append
   and ABI encoding preservation belong to C1.1.3. All statement families
   and all proper-body recursion are closed below, with semantic parameters
   universally quantified so loop and declaration callbacks may change them. *)
Theorem runtime_sym_stmt:
  (!ce ty e. runtime_sym_expr_contract tops compile_expr ce ty e) /\
  (!ce bs bt e s op loc pt s'. runtime_sym_env tops ce /\
    supported_assignment tops bs (BaseTarget bt) e /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ce bs bt s op loc pt s'. runtime_sym_env tops ce /\
    (supported_target tops bs bt \/ supported_aug_target tops bs bt) /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ce target s op loc pt s'. runtime_sym_env tops ce /\
    supported_append_target tops target /\
    ~supported_target_exists is_self_code target /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce target s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ce base v ws es et st cap prim loc s u s'.
    ~is_label_operand base /\ ~is_label_operand v /\
    (!b. ce.ce_imm_alloca = SOME b ==> ~is_label_operand b) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_dynarray_append ce base v ws es et st cap prim loc s = (u,s') ==>
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
  >- suspend "assert"
  >- (rpt gen_tac >> match_mp_tac runtime_sym_log_closed >> conj_tac
      >- simp[] >> first_assum MATCH_ACCEPT_TAC)
  >- (gen_tac >> Cases_on `r` >> rpt gen_tac
      >~ [`Raise RaiseBare`] >- MATCH_ACCEPT_TAC runtime_sym_stmt_raise_bare
      >~ [`Raise RaiseUnreachable`] >- MATCH_ACCEPT_TAC runtime_sym_stmt_raise_unreachable
      >~ [`Raise (RaiseReason _)`] >-
        (irule runtime_sym_raise_reason_closed >> first_assum MATCH_ACCEPT_TAC)
      >> irule runtime_sym_stmt_raise_custom >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC)
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
      conj_tac >- first_assum MATCH_ACCEPT_TAC >>
      conj_tac >- simp[] >> first_assum MATCH_ACCEPT_TAC)
  >> simp[runtime_sym_assignment_annassign_closed]
QED

Resume runtime_sym_stmt[assert]:
  rpt gen_tac >> Cases_on `a`
  >~ [`Assert _ AssertBare`] >-
    (irule runtime_sym_assert_bare_closed >> first_assum MATCH_ACCEPT_TAC)
  >~ [`Assert _ AssertUnreachable`] >-
    (irule runtime_sym_assert_unreachable_closed >> first_assum MATCH_ACCEPT_TAC)
  >~ [`Assert _ (AssertReason _)`] >-
    (irule runtime_sym_assert_reason_closed >> conj_tac >> first_assum MATCH_ACCEPT_TAC)
  >> irule runtime_sym_stmt_assert_custom >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Finalise runtime_sym_stmt


Theorem runtime_sym_stmts:
  (!ce ty e. runtime_sym_expr_contract tops compile_expr ce ty e) /\
  (!ce bs bt e s op loc pt s'. runtime_sym_env tops ce /\
    supported_assignment tops bs (BaseTarget bt) e /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ce bs bt s op loc pt s'. runtime_sym_env tops ce /\
    (supported_target tops bs bt \/ supported_aug_target tops bs bt) /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ce target s op loc pt s'. runtime_sym_env tops ce /\
    supported_append_target tops target /\
    ~supported_target_exists is_self_code target /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce target s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ce base v ws es et st cap prim loc s u s'.
    ~is_label_operand base /\ ~is_label_operand v /\
    (!b. ce.ce_imm_alloca = SOME b ==> ~is_label_operand b) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_dynarray_append ce base v ws es et st cap prim loc s = (u,s') ==>
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
