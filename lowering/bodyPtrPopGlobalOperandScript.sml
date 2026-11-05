Theory bodyPtrPopGlobalOperand
Ancestors
  bodyPtrPopOperandContract bodyPtrPopGlobalLegality bodyPtrPopStructLegality
  bodyPtrAssignCases bodyPtrCtrlCases bodyPtrIntCallCase bodyPtrPreds
  vyperState vyperTypeCallGraph

Theorem pop_global_assignment_body_ptr:
  !cx. body_stmt_ptr_ok cx
    (Assign (BaseTarget pop_struct_root) (TopLevelName pop_struct_ty (NONE,"B")))
Proof
  gen_tac >> irule body_assign_case_ptr >>
  simp[pop_struct_root_def, body_base_target_ptr_ok_def] >>
  irule pop_leaf_body_ptr >> simp[]
QED

Theorem pop_global_body_ptr:
  !cx. body_stmts_ptr_ok cx pop_global_body
Proof
  gen_tac >> rewrite_tac[pop_global_body_def] >>
  irule body_stmts_cons_case_ptr >>
  simp[pop_global_assignment_body_ptr] >> rpt strip_tac >>
  irule body_stmts_cons_case_ptr >>
  simp[pop_struct_return_body_ptr, body_stmts_nil_case_ptr]
QED

Theorem pop_global_index_body_ptr:
  !cx ts mut ret ty.
    get_module_code cx NONE = SOME ts /\
    lookup_callable_function cx.in_deploy "replace" ts =
      SOME (mut,F,[],[],ret,pop_global_body) ==>
    body_expr_ptr_ok cx (Call ty (IntCall (NONE,"replace")) [] NONE)
Proof
  rpt strip_tac >> irule body_intcall_case_ptr >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  gvs[lift_option_type_def, return_def,
      body_exprs_ptr_ok_def, body_results_ptr_ok_def] >>
  irule pop_global_body_ptr
QED

Theorem pop_global_target_body_ptr:
  !cx ts mut ret.
    get_module_code cx NONE = SOME ts /\
    lookup_callable_function cx.in_deploy "replace" ts =
      SOME (mut,F,[],[],ret,pop_global_body) ==>
    body_base_target_ptr_ok cx pop_global_target
Proof
  rpt strip_tac >>
  simp[pop_global_target_def, body_base_target_ptr_ok_def,
       pop_struct_field_def, pop_struct_root_def] >>
  conj_tac
  >- (rpt strip_tac >> irule pop_leaf_body_ptr >> simp[]) >>
  rpt strip_tac >> irule pop_global_index_body_ptr >>
  goal_assum (drule_at Any) >> simp[]
QED
