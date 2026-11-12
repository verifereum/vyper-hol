Theory bodyPtrStructLitOwnershipAttribute
Ancestors bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps loweringShapeDefs loweringShapeProps
  exprLowering compileEnv context

Theorem alloc_run_compile_attribute:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce ty base_e) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (cfn ce ty base_e) (\v s. T) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_attribute cfn ce rt ty base_e fld) (\v s. T)
Proof
  strip_tac >> simp[compile_attribute_def] >>
  irule alloc_run_bind >> qexists `\v s. shape_state s` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_struct_child_frame >>
      qexistsl [`internal`, `ce`, `\s. T`] >> simp[shape_stable_def]) >>
  gen_tac >> simp[] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_op_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_expr_attribute:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce ty base_e) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (cfn ce ty base_e) (\v s. T) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr_body cfn bfn tfn ce ty (Attribute rt base_e fld)) (\v s. T)
Proof
  strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_expr_body_def] >> simp[SF ETA_ss] >>
  irule alloc_run_compile_attribute >> metis_tac[]
QED
