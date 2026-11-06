Theory bodyPtrPopSliceIntegration
Ancestors bodyPtrPopMaterialization bodyPtrPopCalldataSliceBoundary
  exprLowering exprCallBounds supportedExprForms supportedExprs
  compileEnv emitHelper list

Theorem pop_invalid_expr_boundary:
  pop_comp_boundary sa /\ invalid_expr_call ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[invalid_expr_call_def] >> pairarg_tac >> rpt strip_tac >> gvs[] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[]
QED

Theorem pop_expr_child_boundary:
  (!s v t. expr_size a < bound /\ pop_comp_boundary s /\
    cfn cenv (expr_type a) a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  expr_child_callback bound cfn cenv (expr_type a) a sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `expr_size a < bound` >> simp[expr_child_callback_def] >>
  rpt strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  drule_all pop_invalid_expr_boundary >> simp[]
QED

Theorem pop_slice_dispatch_boundary:
  (!s v t. pop_comp_boundary s /\ cfn cenv (expr_type a) a s = (v,t) ==>
    pop_comp_boundary t) /\ pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv ret_ty ty (CalldataSlice n) [a] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> rpt strip_tac >>
  `pop_comp_boundary st1` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     first_x_assum drule_all >> simp[]) >>
  Cases_on `compile_slice_calldata start_op (Lit (n2w n))
    (type_memory_bytes cenv ret_ty) st1` >> gvs[as_ptr_val_def] >>
  drule_all pop_compile_slice_calldata_boundary >> simp[]
QED

Theorem pop_slice_supported_form:
  supported_builtin_form tops ret_ty (CalldataSlice n) args <=>
  ?a. args = [a]
Proof
  Cases_on `args` >> simp[supported_builtin_form_def] >>
  Cases_on `t` >> simp[]
QED

Theorem pop_supported_slice_dispatch_boundary:
  supported_builtin_form tops ret_ty (CalldataSlice n) args /\
  EVERY (supported_pure_expr tops) args /\
  (!a s v t. supported_pure_expr tops a /\ expr_size a < bound /\
    pop_comp_boundary s /\ cfn cenv (expr_type a) a s = (v,t) ==>
    pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_builtin_dispatch_body (expr_child_callback bound cfn) cenv ret_ty ty
    (CalldataSlice n) args sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[pop_slice_supported_form] >> rpt strip_tac >> gvs[] >>
  drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
    pop_slice_dispatch_boundary >> disch_then irule >>
  simp[Excl "expr_child_callback_def"] >>
  rpt strip_tac >>
  drule_at (Pat `expr_child_callback _ _ _ _ _ _ = _`)
    pop_expr_child_boundary >> disch_then irule >> simp[] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED
