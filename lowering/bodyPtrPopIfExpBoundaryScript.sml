Theory bodyPtrPopIfExpBoundary
Ancestors bodyPtrPopTypedCopyBoundary bodyPtrPopMaterialization
  bodyPtrPopAllocationBoundary bodyPtrPopMathIntegration
  bodyPtrPopCompilerBoundary exprLowering compileEnv emitHelper list

Theorem pop_compile_ifexp_arm_boundary:
  pop_comp_boundary sa /\
  compile_ifexp_arm cenv res_ty arm_ty vv sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `is_word_type res_ty \/ same_memory_layout cenv arm_ty res_ty` >>
  simp[compile_ifexp_arm_def, comp_ignore_bind_def] >> rpt strip_tac
  >- (drule_all pop_unwrap_value_boundary >> simp[]) >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_all pop_unwrap_value_boundary,
         drule_all pop_compile_store_memory_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED

Theorem pop_ifexp_body_boundary:
  (!a aty s v t. (a = cond_e \/ a = then_e \/ a = else_e) /\
    pop_comp_boundary s /\ cfn cenv aty a s = (v,t) ==>
    pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty
    (IfExp rt cond_e then_e else_e) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_expr_body_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_fresh_var_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_fresh_label_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_fresh_label_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_fresh_label_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_comp_boundary_new_block >> strip_tac >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st7a` by metis_tac[] >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_compile_ifexp_arm_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_comp_boundary_new_block >> strip_tac >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st11a` by metis_tac[] >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_compile_ifexp_arm_boundary >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  dxrule_all pop_comp_boundary_new_block >> strip_tac >>
  gvs[AllCaseEqs()]
QED

Theorem pop_ifexp_child_body_boundary:
  (!a aty s v t. (a = cond_e \/ a = then_e \/ a = else_e) /\
    expr_size a < bound /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_expr_body (expr_child_callback bound cfn) bfn tfn cenv ty
    (IfExp rt cond_e then_e else_e) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  rpt strip_tac >>
  drule_at (Pat `compile_expr_body _ _ _ _ _ _ _ = _`) pop_ifexp_body_boundary >>
  disch_then irule >> simp[Excl "expr_child_callback_def"] >>
  rpt strip_tac >>
  drule_at (Pat `expr_child_callback _ _ _ _ _ _ = _`)
    pop_expr_child_typed_boundary >>
  disch_then irule >> simp[] >> metis_tac[]
QED
