Theory bodyPtrStructLitOwnershipAccount
Ancestors bodyPtrStructLitOwnershipSliceCases bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  loweringShapeProps loweringShapeDefs loweringShapeRules exprLowering compileEnv
  context list gasShadowCompileBase

Theorem alloc_run_compile_acc:
  shape_step F compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce (BaseT AddressT) e) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (cfn ce (BaseT AddressT) e) (\v s. T) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_acc cfn ce e item) (\v s. T)
Proof
  strip_tac >> Cases_on `item` >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_acc_def, comp_bind_uncurry] >> simp[SF ETA_ss]
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`F`, `\s. T`] >> simp[shape_stable_def])
  >~ [`alloc_run _ (comp_bind (emit_inst INVALID [] []) _) _`]
  >- (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
      reverse conj_tac
      >- (irule alloc_run_conseq >>
          irule_at Any (Q.INST [`outs` |-> `[]`] alloc_run_emit_inst_fresh) >>
          simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  irule (Q.INST [`internal` |-> `F`] alloc_run_lower_value_then) >> simp[] >> gen_tac >>
  irule alloc_run_conseq >> qexistsl [`fresh_outputs`, `\v s. fresh_outputs s`] >>
  simp[shape_state_def, shape_base_fresh_outputs, alloc_run_emit_op_fresh] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_builtin_acc:
  1 <= LENGTH args /\
  (!e. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce (BaseT AddressT) e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce (BaseT AddressT) e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty (Acc item) args) (\v s. T)
Proof
  strip_tac >> `MEM (HD args) args` by (Cases_on `args` >> gvs[]) >>
  `alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_acc cfn ce (HD args) item) (\v s. T)` by
      (irule alloc_run_compile_acc >> metis_tac[]) >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def] >> simp[SF ETA_ss] >>
  fs[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
