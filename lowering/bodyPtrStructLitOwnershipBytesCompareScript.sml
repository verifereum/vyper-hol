Theory bodyPtrStructLitOwnershipBytesCompare
Ancestors bodyPtrStructLitOwnershipScalar bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  loweringShapeDefs loweringShapeRules loweringShapeProps exprLowering
  builtinSimple compileEnv context list pair

Theorem alloc_run_compile_bytestring_hash:
  alloc_run fresh_outputs (compile_bytestring_hash ptr_op) (\v s. fresh_outputs s)
Proof
  simp[compile_bytestring_hash_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_builtin_bytestring_compare:
  (op = Eq \/ op = NotEq) /\ is_bytestring_type (expr_type (HD args)) /\
  2 <= LENGTH args /\
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v)) /\
  (!e t. MEM e args ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty (Bop op) args) (\v s. T)
Proof
  strip_tac >> gvs[] >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def] >>
  simp[SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  (reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def] >>
      `MEM (HD args) args` by (Cases_on `args` >> gvs[]) >> metis_tac[])) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  (reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def] >>
      `MEM (HD (TL args)) args` by
        (Cases_on `args` >> gvs[] >> Cases_on `t` >> gvs[]) >> metis_tac[])) >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  qexistsl [`fresh_outputs`, `\v s. fresh_outputs s`] >>
  simp[shape_state_def, shape_base_fresh_outputs] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    (reverse conj_tac >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_bytestring_hash,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh]) >> gen_tac >> simp[]) >>
  simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all (SRULE [alloc_run_def] alloc_run_emit_op_fresh) >> simp[]
QED
