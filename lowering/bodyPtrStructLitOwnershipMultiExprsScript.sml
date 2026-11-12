Theory bodyPtrStructLitOwnershipMultiExprs
Ancestors bodyPtrStructLitOwnershipInterfaces bodyPtrStructLitOwnershipSteps
  loweringShapeProps loweringShapeDefs loweringShapeRules exprLowering compileEnv

Theorem alloc_run_compile_multi_exprs_frame:
  !es R.
  (!e. MEM e es ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. T)) /\ shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce)
    (compile_multi_exprs cfn ce es)
    (\vs s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ EVERY (plain_operand s) vs)
Proof
  Induct >> simp[compile_multi_exprs_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rpt strip_tac >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac >- (irule alloc_run_lower_value_frame >> metis_tac[]) >>
  qx_gen_tac `v` >> simp[] >> irule alloc_run_bind >>
  qexists `\vs s. shape_state s /\ (R s /\ plain_operand s v) /\
    cenv_shape_ok s ce /\ EVERY (plain_operand s) vs` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> first_x_assum (qspec_then `\s. R s /\ plain_operand s v` mp_tac) >>
      impl_tac
      >- simp[shape_stable_conj, SRULE [] (Q.SPEC `[v]` shape_stable_plain_operands)] >>
      disch_then (irule_at Any) >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
