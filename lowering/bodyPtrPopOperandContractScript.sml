Theory bodyPtrPopOperandContract
Ancestors
  bodyPtrPopContractImports bodyPtrPopStructLegality
  exprSimPtr bodyPtrAssignCases bodyPtrExitCases bodyPtrCtrlCases
  bodyPtrIntCallCase exprSimSource bodyPtrPreds vyperTypeCallGraph vyperState

(* A noncircular bridge to the existing leaf interface. This does not
   establish source realizability of the diagnostic replacement body. *)
Theorem pop_leaf_body_ptr:
  !cx e.
    (?a id. e = Name a id) \/ (?a nsid. e = TopLevelName a nsid) \/
    (?a nsid mid. e = FlagMember a nsid mid) \/ (?a l. e = Literal a l) ==>
    body_expr_ptr_ok cx e
Proof
  rpt gen_tac >> disch_tac >> simp[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env e es` by
    (simp[expr_sim_pre_body] >>
     qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[int_calls_expr_def]) >>
  metis_tac[leaf_expr_sim_ptr]
QED

Theorem pop_struct_assignment_body_ptr:
  !cx. body_stmt_ptr_ok cx
    (Assign (BaseTarget pop_struct_root) (Name pop_struct_ty "replacement"))
Proof
  gen_tac >> irule body_assign_case_ptr >>
  simp[pop_struct_root_def, body_base_target_ptr_ok_def] >>
  irule pop_leaf_body_ptr >> simp[]
QED

Theorem pop_struct_return_body_ptr:
  !cx. body_stmt_ptr_ok cx
    (Return (SOME (Literal (BaseT (UintT 256)) (IntL 0))))
Proof
  gen_tac >> irule body_return_case_ptr >>
  irule pop_leaf_body_ptr >> simp[]
QED

Theorem pop_struct_body_ptr:
  !cx. body_stmts_ptr_ok cx pop_struct_body
Proof
  gen_tac >> rewrite_tac[pop_struct_body_def] >>
  irule body_stmts_cons_case_ptr >>
  simp[pop_struct_assignment_body_ptr] >> rpt strip_tac >>
  irule body_stmts_cons_case_ptr >>
  simp[pop_struct_return_body_ptr, body_stmts_nil_case_ptr]
QED

(* Conditional universal operand contract. The lookup assumptions do not
   certify a well-typed callable body or an initial body_inv frame. *)
Theorem pop_struct_index_body_ptr:
  !cx ts mut ret ty.
    get_module_code cx NONE = SOME ts /\
    lookup_callable_function cx.in_deploy "replace" ts =
      SOME (mut,F,[],[],ret,pop_struct_body) ==>
    body_expr_ptr_ok cx (Call ty (IntCall (NONE,"replace")) [] NONE)
Proof
  rpt strip_tac >> irule body_intcall_case_ptr >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  gvs[lift_option_type_def, return_def,
      body_exprs_ptr_ok_def, body_results_ptr_ok_def] >>
  irule pop_struct_body_ptr
QED

Theorem pop_struct_target_body_ptr:
  !cx ts mut ret ty.
    get_module_code cx NONE = SOME ts /\
    lookup_callable_function cx.in_deploy "replace" ts =
      SOME (mut,F,[],[],ret,pop_struct_body) ==>
    body_base_target_ptr_ok cx
      (SubscriptTarget
        (SubscriptTarget pop_struct_field (Literal (BaseT (UintT 256)) (IntL 0)))
        (Call ty (IntCall (NONE,"replace")) [] NONE))
Proof
  rpt strip_tac >>
  simp[body_base_target_ptr_ok_def, pop_struct_field_def, pop_struct_root_def] >>
  conj_tac
  >- (rpt strip_tac >> irule pop_leaf_body_ptr >> simp[]) >>
  rpt strip_tac >> irule pop_struct_index_body_ptr >>
  goal_assum (drule_at Any) >> simp[]
QED
