Theory runtimeSymSrcStatementRange
Ancestors
  runtimeSymSrcStatementControl runtimeSymSrcDeclarations runtimeSymSrcEmission
  runtimeSymSrcModuleDispatch runtimeSymSrcInterfaces stmtLowering compileEnv
  supportedStmts supportedStmtTraverse supportedExprs context venomInst
  stackPlanTypes emitHelper loweringShapeDefs list finite_map externalEntryShape

Theorem runtime_sym_range_rounds[local]:
  ~is_label_operand a /\ ~is_label_operand b /\
  EVERY runtime_sym_inst (state_insts s) /\
  (case (e1,e2) of
     (Literal _ (IntL n1), Literal _ (IntL n2)) =>
       comp_return (Lit (i2w n2 - i2w n1))
   | _ => emit_op SUB [b;a]) s = (r,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand r
Proof
  qspecl_then
    [`\f. ~is_label_operand a /\ ~is_label_operand b /\
            EVERY runtime_sym_inst (state_insts s) /\ f s = (r,s') ==>
            EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand r`,
     `e1`, `e2`, `\i j. comp_return (Lit (i2w j - i2w i))`,
     `emit_op SUB [b;a]`] mp_tac range_literal_case_pred >>
  simp[] >> (impl_tac >-
    (conj_tac >- (rpt strip_tac >> gvs[comp_return_def, is_label_operand_def]) >>
     strip_tac >> irule runtime_sym_emit_op >> goal_assum (drule_at Any) >> simp[])) >>
  simp[]
QED

Theorem runtime_sym_range_supported[local]:
  supported_iterator tops ty (Range a b) n ==>
  supported_expr tops a /\ supported_expr tops b
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[supported_iterator_def, supported_expr_def, supported_pure_expr_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[supported_pure_expr_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[supported_pure_expr_def]
QED

Theorem runtime_sym_range_checks[local]:
  ~is_label_operand a /\ ~is_label_operand b /\ ~is_label_operand r /\
  EVERY runtime_sym_inst (state_insts s) /\
  (case (e1,e2) of
     (Literal _ (IntL _), Literal _ (IntL _)) => comp_return ()
   | _ => compile_range_bound_checks a b r n signed) s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  qspecl_then
    [`\f. ~is_label_operand a /\ ~is_label_operand b /\ ~is_label_operand r /\
            EVERY runtime_sym_inst (state_insts s) /\ f s = (u,s') ==>
            EVERY runtime_sym_inst (state_insts s')`,
     `e1`, `e2`, `\i j. comp_return ()`,
     `compile_range_bound_checks a b r n signed`] mp_tac range_literal_case_pred >>
  simp[] >> (impl_tac >-
    (conj_tac >- (rpt strip_tac >> gvs[comp_return_def]) >>
     metis_tac[runtime_sym_range_bound_checks])) >> simp[]
QED

Theorem runtime_sym_range_store[local]:
  runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
  (case FLOOKUP ce.ce_vars id of
     SOME (MemLoc offset _) => emit_void MSTORE [Lit (n2w offset); Var v]
   | SOME (PtrVar p _) => emit_void MSTORE [p; Var v]
   | _ => emit_void INVALID []) s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[]
  >- (strip_tac >> irule runtime_sym_emit_void >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `x` >> simp[] >> strip_tac >>
  irule runtime_sym_emit_void >> goal_assum (drule_at Any) >>
  gvs[runtime_sym_env_def, runtime_sym_loc_def, is_label_operand_def] >>
  res_tac >> gvs[runtime_sym_loc_def]
QED

Theorem runtime_sym_stmt_for_range:
  (!e. e = start_e \/ e = end_e ==>
    !s op s'. runtime_sym_env ce /\ supported_expr tops e /\
      ~supported_expr_exists is_self_code e /\
      EVERY runtime_sym_inst (state_insts s) /\
      lower_value compile_expr ce fty e s = (op,s') ==>
      EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!bindings ce lc. runtime_sym_stmts_contract tops bindings compile_stmts ce lc ty stmts) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty
    (For id fty (Range start_e end_e) bound stmts)
Proof
  rewrite_tac[runtime_sym_stmt_contract_def, runtime_sym_stmts_contract_def] >>
  rpt strip_tac >>
  fs[Once supported_stmt_def, Once supported_stmt_expr_exists_def] >>
  gvs[Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 5 (pairarg_tac >> gvs[]) >>
  ntac 5 (pairarg_tac >> gvs[]) >>
  ntac 5 (pairarg_tac >> gvs[]) >>
  ntac 5 (pairarg_tac >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac runtime_sym_range_supported >>
  fs[supported_iterator_exists_def] >>
  qpat_assum `!e. _` (qspec_then `start_e` (drule_all o SRULE [])) >> strip_tac >>
  qpat_x_assum `!e. _` (qspec_then `end_e` (drule_all o SRULE [])) >> strip_tac >>
  drule_all runtime_sym_declare_local >> strip_tac >>
  drule_all runtime_sym_emit_local_alloca >> strip_tac >>
  imp_res_tac runtime_sym_fresh_label >> gvs[] >>
  qpat_assum `emit_inst JMP [Label entry_lbl] _ _ = _`
    (mp_then Any mp_tac runtime_sym_jump) >> simp[] >> strip_tac >>
  imp_res_tac runtime_sym_new_block_result >> fs[] >>
  imp_res_tac runtime_sym_fresh_var >> gvs[] >>
  qpat_assum `emit_inst ASSIGN [start_op] _ _ = _`
    (mp_then Any (qspec_then `0` mp_tac) runtime_sym_emit_inst) >>
  (impl_tac >- simp[runtime_sym_ordinary_inst]) >> strip_tac >>
  drule_all (SRULE [] runtime_sym_range_rounds) >> strip_tac >>
  FAIL_TAC "after rounds"
QED
