Theory runtimeSymSrcStatementControl
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission runtimeSymSrcEmissionProbe runtimeSymSrcModuleDispatch stmtLowering compileEnv
  supportedStmts supportedStmtTraverse supportedExprs context venomInst stackPlanTypes
  emitHelper loweringShapeDefs list

Theorem runtime_sym_range_bound_checks:
  ~is_label_operand a /\ ~is_label_operand b /\ ~is_label_operand r /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_range_bound_checks a b r n signed s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `signed` >>
  simp[compile_range_bound_checks_def, emit_op_def, emit_void_def,
       emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  fs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND] >>
  simp[runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_stmt_pass:
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty Pass
Proof
  simp[runtime_sym_stmt_contract_def, compile_stmt_def, comp_return_def]
QED

Theorem runtime_sym_stmt_break:
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty Break
Proof
  Cases_on `lc` >>
  simp[runtime_sym_stmt_contract_def, compile_stmt_def, runtime_sym_loop_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> rpt strip_tac
  >- (pairarg_tac >> gvs[] >>
      drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
      disch_then irule >>
      simp[runtime_sym_ordinary_inst]) >>
  drule_all runtime_sym_jump >> simp[]
QED

Theorem runtime_sym_stmt_continue:
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty Continue
Proof
  Cases_on `lc` >>
  simp[runtime_sym_stmt_contract_def, compile_stmt_def, runtime_sym_loop_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> rpt strip_tac
  >- (pairarg_tac >> gvs[] >>
      drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
      disch_then irule >>
      simp[runtime_sym_ordinary_inst]) >>
  drule_all runtime_sym_jump >> simp[]
QED

Theorem runtime_sym_stmt_expr:
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Expr e)
Proof
  simp[runtime_sym_stmt_contract_def, runtime_sym_expr_contract_def,
       supported_stmt_def, supported_stmt_expr_exists_def] >>
  rpt strip_tac >>
  gvs[Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED

(* lower_value: C1.1.3 expression-value boundary; body contracts refer only
   to the two proper statement-list subterms. *)
Theorem runtime_sym_stmt_if:
  (!s op s'. runtime_sym_env ce /\ supported_expr tops e /\
     ~supported_expr_exists is_self_code e /\
     EVERY runtime_sym_inst (state_insts s) /\
     lower_value compile_expr ce (BaseT BoolT) e s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  runtime_sym_stmts_contract tops bindings compile_stmts ce lc ty yes /\
  runtime_sym_stmts_contract tops bindings compile_stmts ce lc ty no ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (If e yes no)
Proof
  rewrite_tac[runtime_sym_stmt_contract_def, runtime_sym_stmts_contract_def] >>
  rpt strip_tac >>
  fs[Once supported_stmt_def, Once supported_stmt_expr_exists_def] >>
  gvs[Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
      comp_get_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `supported_expr tops e` by simp[supported_expr_def] >>
  qpat_x_assum `!s op s'. _` drule_all >> strip_tac >>
  imp_res_tac runtime_sym_fresh_label >> gvs[] >>
  qpat_assum `emit_inst JNZ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_jnz) >>
  (impl_tac >- simp[]) >> strip_tac >>
  imp_res_tac runtime_sym_new_block_result >> fs[] >>
  qpat_x_assum `!s s'. _ /\ compile_stmts ce lc ty yes s = _ ==> _`
    (drule_at (Pat `compile_stmts _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  drule_all runtime_sym_jmp_if_not_terminated >> strip_tac >>
  imp_res_tac runtime_sym_new_block_result >> fs[] >>
  qpat_x_assum `!s s'. _ /\ compile_stmts ce lc ty no s = _ ==> _`
    (drule_at (Pat `compile_stmts _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  drule_all runtime_sym_jmp_if_not_terminated >> strip_tac >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  IF_CASES_TAC >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac runtime_sym_new_block_result >> fs[] >> gvs[]
QED
