Theory bodyPtrStructLitOwnershipScalarCases
Ancestors bodyPtrStructLitOwnershipScalar bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  loweringShapeDefs loweringShapeRules loweringShapeProps exprLowering
  builtinSimple compileEnv context list pair

Theorem alloc_run_builtin_unary_scalar:
  (bi = Not \/ bi = Neg) /\ 1 <= LENGTH args /\
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty bi args) (\v s. T)
Proof
  strip_tac >> gvs[] >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def] >>
  simp[SF ETA_ss] >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  (reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def] >>
      first_x_assum irule >> Cases_on `args` >> gvs[])) >>
  gen_tac >> simp[] >> Cases_on `expr_type (HD args) = BaseT BoolT` >> simp[] >>
  simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `fresh_outputs st1` by metis_tac[shape_state_def, shape_base_fresh_outputs] >>
  FIRST [drule_all (SRULE [alloc_run_def] alloc_run_emit_op_fresh),
    drule_all (SRULE [alloc_run_def] alloc_run_compile_invert),
    drule_all (SRULE [alloc_run_def] alloc_run_compile_neg)] >> simp[]
QED

Theorem alloc_run_builtin_binop_scalar:
  2 <= LENGTH args /\
  ~((op = In \/ op = NotIn) /\ is_ArrayT (expr_type (HD (TL args)))) /\
  ~(is_bytestring_type (expr_type (HD args)) /\ (op = Eq \/ op = NotEq)) /\
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty (Bop op) args) (\v s. T)
Proof
  strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def] >>
  simp[SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def] >>
      first_x_assum irule >> Cases_on `args` >> gvs[]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def] >>
      first_x_assum irule >> Cases_on `args` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
  gen_tac >> simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `fresh_outputs st` by metis_tac[shape_state_def, shape_base_fresh_outputs] >>
  drule_all (SRULE [alloc_run_def] alloc_run_compile_binop) >> simp[]
QED
