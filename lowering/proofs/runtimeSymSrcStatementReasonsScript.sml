Theory runtimeSymSrcStatementReasons
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission runtimeSymSrcReasonMessage
  runtimeSymSrcRevertEncoder runtimeSymSrcModuleDispatch stmtLowering compileEnv
  context venomInst stackPlanTypes supportedStmts supportedStmtTraverse
  supportedExprs supportedExprTraverse

Theorem runtime_sym_stmt_raise_bare:
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Raise RaiseBare)
Proof
  simp[runtime_sym_stmt_contract_def, Once compile_stmt_def] >> rpt strip_tac >>
  irule runtime_sym_emit_inst >> goal_assum (drule_at Any) >>
  qexists `s.cs_next_id` >> simp[] >>
  irule runtime_sym_labeled_inst >> simp[is_label_operand_def]
QED

Theorem runtime_sym_stmt_raise_unreachable:
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Raise RaiseUnreachable)
Proof
  simp[runtime_sym_stmt_contract_def, Once compile_stmt_def] >> rpt strip_tac >>
  irule runtime_sym_emit_inst >> goal_assum (drule_at Any) >>
  qexists `s.cs_next_id` >> simp[] >>
  irule runtime_sym_labeled_inst >> simp[]
QED

Theorem runtime_sym_supported_reason_expr[local]:
  !tops e. supported_string_reason tops e ==> supported_expr tops e
Proof
  gen_tac >> Cases >> simp[supported_string_reason_def, supported_expr_def] >>
  Cases_on `l` >> simp[supported_string_reason_def, supported_expr_def,
                       supported_pure_expr_def]
QED

(* Literal construction, allocation and unwrap are C1.1.3 boundaries.
   The expression premise applies only to the actual reason expression. *)
Theorem runtime_sym_stmt_raise_reason:
  (!bs n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_bytelike_literal bs n s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand) /\
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand) /\
  (!ce v s op s'. runtime_sym_env ce /\ runtime_sym_value v /\
    EVERY runtime_sym_inst (state_insts s) /\ unwrap_value ce v s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Raise (RaiseReason e))
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_stmt_contract_def] >> rpt gen_tac >>
  simp[NoAsms, Once compile_stmt_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >>
  `supported_expr tops e /\ ~supported_expr_exists is_self_code e` by
    (gvs[supported_stmt_def, supported_raise_reason_def,
         supported_stmt_expr_exists_def, supported_raise_exists_def] >>
     metis_tac[runtime_sym_supported_reason_expr, supported_expr_def]) >>
  drule_all runtime_sym_reason_message >> strip_tac >>
  drule_all runtime_sym_revert_encoder >> simp[]
QED

(* The lower_value adapter is owned by C1.1.3.6; its expression
   contract is required only at this Assert's condition. *)
Theorem runtime_sym_stmt_assert_bare:
  (!e t s v s'. runtime_sym_expr_contract tops compile_expr ce t e /\
    runtime_sym_env ce /\ supported_expr tops e /\
    ~supported_expr_exists is_self_code e /\
    EVERY runtime_sym_inst (state_insts s) /\
    lower_value compile_expr ce t e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  runtime_sym_expr_contract tops compile_expr ce (BaseT BoolT) cond ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Assert cond AssertBare)
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_stmt_contract_def] >> rpt gen_tac >>
  simp[NoAsms, Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  rpt strip_tac >> gvs[] >>
  `supported_expr tops cond /\ ~supported_expr_exists is_self_code cond` by
    (gvs[supported_stmt_def, supported_stmt_expr_exists_def,
         supported_assert_exists_def, supported_expr_def]) >>
  first_assum drule_all >> strip_tac >>
  dxrule runtime_sym_fresh_label >> strip_tac >>
  dxrule runtime_sym_fresh_label >> strip_tac >> gvs[] >>
  drule_at (Pat `emit_inst JNZ _ _ _ = _`) runtime_sym_jnz >>
  simp[] >> strip_tac >>
  rev_dxrule runtime_sym_new_block_result >> strip_tac >>
  qpat_x_assum `emit_inst REVERT _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_inst) >>
  disch_then (qspec_then `s.cs_next_id` mp_tac) >>
  simp[] >> (impl_tac >- (irule runtime_sym_labeled_inst >> simp[is_label_operand_def])) >>
  strip_tac >> dxrule runtime_sym_new_block_result >> simp[]
QED

Theorem runtime_sym_stmt_assert_unreachable:
  (!e t s v s'. runtime_sym_expr_contract tops compile_expr ce t e /\
    runtime_sym_env ce /\ supported_expr tops e /\
    ~supported_expr_exists is_self_code e /\
    EVERY runtime_sym_inst (state_insts s) /\
    lower_value compile_expr ce t e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  runtime_sym_expr_contract tops compile_expr ce (BaseT BoolT) cond ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Assert cond AssertUnreachable)
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_stmt_contract_def] >> rpt gen_tac >>
  simp[NoAsms, Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rpt strip_tac >> gvs[] >>
  `supported_expr tops cond /\ ~supported_expr_exists is_self_code cond` by
    (gvs[supported_stmt_def, supported_stmt_expr_exists_def,
         supported_assert_exists_def, supported_expr_def]) >>
  first_assum drule_all >> strip_tac >>
  dxrule runtime_sym_fresh_label >> strip_tac >>
  dxrule runtime_sym_fresh_label >> strip_tac >> gvs[] >>
  drule_at (Pat `emit_inst JNZ _ _ _ = _`) runtime_sym_jnz >>
  simp[] >> strip_tac >>
  rev_dxrule runtime_sym_new_block_result >> strip_tac >>
  qpat_x_assum `emit_inst INVALID _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_inst) >>
  disch_then (qspec_then `s.cs_next_id` mp_tac) >>
  simp[] >> (impl_tac >- (irule runtime_sym_labeled_inst >> simp[])) >>
  strip_tac >> dxrule runtime_sym_new_block_result >> simp[]
QED

Theorem runtime_sym_stmt_assert_reason:
  (!e t s v s'. runtime_sym_expr_contract tops compile_expr ce t e /\
    runtime_sym_env ce /\ supported_expr tops e /\
    ~supported_expr_exists is_self_code e /\
    EVERY runtime_sym_inst (state_insts s) /\
    lower_value compile_expr ce t e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!bs n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_bytelike_literal bs n s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand) /\
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand) /\
  (!ce v s op s'. runtime_sym_env ce /\ runtime_sym_value v /\
    EVERY runtime_sym_inst (state_insts s) /\ unwrap_value ce v s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  runtime_sym_expr_contract tops compile_expr ce (BaseT BoolT) cond /\
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Assert cond (AssertReason e))
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_stmt_contract_def] >> rpt gen_tac >>
  simp[NoAsms, Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rpt strip_tac >> gvs[] >>
  `supported_expr tops cond /\ ~supported_expr_exists is_self_code cond /\
   supported_expr tops e /\ ~supported_expr_exists is_self_code e` by
    (gvs[supported_stmt_def, supported_assert_reason_def,
         supported_stmt_expr_exists_def, supported_assert_exists_def] >>
     metis_tac[runtime_sym_supported_reason_expr, supported_expr_def]) >>
  first_assum drule_all >> strip_tac >>
  dxrule runtime_sym_fresh_label >> strip_tac >>
  dxrule runtime_sym_fresh_label >> strip_tac >> gvs[] >>
  drule_at (Pat `emit_inst JNZ _ _ _ = _`) runtime_sym_jnz >>
  simp[] >> strip_tac >>
  rev_dxrule runtime_sym_new_block_result >> strip_tac >>
  drule_at (Pat `compile_reason_message _ _ _ = _`) runtime_sym_reason_message >>
  simp[] >> disch_then drule_all >> strip_tac >>
  drule_all runtime_sym_revert_encoder >> simp[] >> strip_tac >>
  dxrule runtime_sym_new_block_result >> simp[]
QED
