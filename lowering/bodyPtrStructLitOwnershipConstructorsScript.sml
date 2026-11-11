Theory bodyPtrStructLitOwnershipConstructors
Ancestors bodyPtrStructLitOwnershipAggregateLoops bodyPtrStructLitOwnershipIfexpFrame
  bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitOwnershipSteps
  loweringShapeProps loweringShapeDefs loweringShapeRules exprLowering compileEnv
  context list

Theorem alloc_run_builtin_make_array:
  (!e. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty (MakeArray etopt bnd) args) (\v s. T)
Proof
  strip_tac >> Cases_on `etopt` >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def, comp_bind_uncurry] >> simp[SF ETA_ss] >>
  irule alloc_run_bind >>
  qexists `\b s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s b.buf_operand` >>
  simp[SRULE [cenv_shape_ok_stable]
    (Q.INST [`R` |-> `\s. cenv_shape_ok s ce`] alloc_run_alloc_buffer_frame)] >>
  gen_tac >> simp[alloc_run_def, oneline as_ptr_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[alloc_run_def] >>~- ([`compile_make_tuple _ _ _ _ _ _ = _`],
    drule_all (SRULE [alloc_run_def, shape_stable_def]
      (Q.INST [`R` |-> `\s. T`] (SPEC_ALL alloc_run_compile_make_tuple_frame))) >> simp[]) >>
  drule_all (SRULE [alloc_run_def, shape_stable_def]
    (Q.INST [`R` |-> `\s. T`] alloc_run_compile_make_array_frame)) >> simp[]
QED

Theorem alloc_run_expr_structlit:
  (!fname e. MEM (fname,e) fields ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr_body cfn bfn tfn ce ty (StructLit ann name fields)) (\v s. T)
Proof
  strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_expr_body_def, comp_bind_uncurry] >> simp[SF ETA_ss] >>
  irule alloc_run_bind >>
  qexists `\b s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s b.buf_operand` >>
  simp[SRULE [cenv_shape_ok_stable]
    (Q.INST [`R` |-> `\s. cenv_shape_ok s ce`] alloc_run_alloc_buffer_frame)] >>
  gen_tac >> simp[alloc_run_def, comp_bind_def, comp_return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[alloc_run_def, AllCaseEqs()] >>
  qpat_x_assum `UNCURRY _ _ = _` mp_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_all (SRULE [alloc_run_def, shape_stable_def]
    (Q.INST [`R` |-> `\s. T`] (SPEC_ALL alloc_run_compile_struct_lit_frame))) >> simp[]
QED
