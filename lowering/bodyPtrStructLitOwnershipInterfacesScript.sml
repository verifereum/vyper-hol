Theory bodyPtrStructLitOwnershipInterfaces
Ancestors bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitOwnershipMemory
  bodyPtrStructLitOwnershipCallbacks
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipFrame
  loweringShapeProps loweringShapeDefs loweringShapeRules exprLowering
  context compileEnv exprCallBounds stackPlanTypes venomInst unitShapeDefs

Theorem alloc_run_lower_value_frame:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce) (cfn ce ty e)
    (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) (cfn ce ty e) (\v s. T) /\
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce)
    (lower_value cfn ce ty e)
    (\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s v)
Proof
  strip_tac >> simp[lower_value_def] >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ value_shape_ok s v` >>
  reverse conj_tac >- (irule alloc_run_struct_child_frame >> metis_tac[]) >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`R` |-> `\s. R s /\ cenv_shape_ok s ce`]
    alloc_run_unwrap_value_frame) >>
  qexists `R` >> simp[shape_stable_conj, cenv_shape_ok_stable]
QED

Theorem alloc_run_lower_value_reserved:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce) (cfn ce ty e)
    (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) (cfn ce ty e) (\v s. T) /\
  shape_stable R ==>
  alloc_run (\s. (shape_state s /\ R s /\ cenv_shape_ok s ce) /\
    not_fresh_at s x /\ ~alloc_owned s x)
    (lower_value cfn ce ty e)
    (\v s. (shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s v) /\
    not_fresh_at s x /\ ~alloc_owned s x)
Proof
  strip_tac >> ho_match_mp_tac alloc_run_frame_reserved >>
  irule alloc_run_lower_value_frame >> metis_tac[]
QED

Theorem ownership_invalid_expr_call_shape:
  shape_step internal compiler_label (\s. T) (invalid_expr_call ty)
    (\v s. value_shape_ok s v)
Proof
  `invalid_expr_call ty = comp_ignore_bind (emit_inst INVALID [] [])
      (comp_return (StackValue ty (Lit 0w)))` by
    (simp[FUN_EQ_THM, invalid_expr_call_def, comp_ignore_bind_def,
          comp_bind_def, comp_return_def] >> gen_tac >>
     Cases_on `emit_inst INVALID [] [] st` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule shape_step_ignore_bind >> qexists `\x s. T` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_emit_inst >>
      qexists `\s. T` >>
      simp[shape_stable_def, lowered_inst_ok_def, mk_inst_def,
           raw_opcode_ok_def, inst_shape_ok_def, label_positions_ok_def,
           operand_case_not_label, inst_jump_labels_ok_def,
           is_terminator_def, is_param_opcode_def] >>
      qexists `compiler_label` >> simp[]) >>
  gen_tac >> irule shape_step_return >>
  simp[value_shape_ok_def, plain_operand_def, is_label_operand_def]
QED

Theorem ownership_expr_child_shape:
  ~supported_expr_exists expr_shape_root e ==>
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (expr_child_callback n compile_expr ce ty e) (\v s. value_shape_ok s v)
Proof
  strip_tac >> CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[expr_child_callback_def] >>
  Cases_on `expr_size e < n`
  >- (simp[SF ETA_ss] >> irule (cj 1 compile_expr_shape) >> simp[]) >>
  simp[SF ETA_ss] >> irule shape_step_conseq >>
  irule_at Any ownership_invalid_expr_call_shape >> simp[]
QED

Theorem ownership_builtin_child_shape:
  builtin_arity bi <= LENGTH es /\ ~supported_exprs_exists expr_shape_root es ==>
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (builtin_child_callback n compile_builtin_dispatch ce rt ty bi es)
    (\v s. value_shape_ok s v)
Proof
  strip_tac >> CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[builtin_child_callback_def] >> Cases_on `list_size expr_size es < n`
  >- (simp[SF ETA_ss] >> irule (cj 2 compile_expr_shape) >> simp[]) >>
  simp[SF ETA_ss] >> irule shape_step_conseq >>
  irule_at Any ownership_invalid_expr_call_shape >> simp[]
QED

Theorem ownership_type_child_shape:
  type_builtin_arity tb <= LENGTH es /\ ~supported_exprs_exists expr_shape_root es ==>
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (type_child_callback n compile_type_builtin_dispatch ce vt ty tb rt es)
    (\v s. value_shape_ok s v)
Proof
  strip_tac >> CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[type_child_callback_def] >> Cases_on `list_size expr_size es < n`
  >- (simp[SF ETA_ss] >> irule (cj 3 compile_expr_shape) >> simp[]) >>
  simp[SF ETA_ss] >> irule shape_step_conseq >>
  irule_at Any ownership_invalid_expr_call_shape >> simp[]
QED

Theorem alloc_run_actual_expr_child_frame:
  ~supported_expr_exists expr_shape_root e /\ shape_stable R /\
  (expr_size e < n ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) (compile_expr ce ty e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce)
    (expr_child_callback n compile_expr ce ty e)
    (\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ value_shape_ok s v)
Proof
  strip_tac >> irule alloc_run_struct_child_frame >>
  irule_at Any ownership_expr_child_shape >>
  simp[] >> irule alloc_run_expr_child_callback_owned >> simp[]
QED

Theorem alloc_run_actual_builtin_child_frame:
  builtin_arity bi <= LENGTH es /\ ~supported_exprs_exists expr_shape_root es /\
  shape_stable R /\ (list_size expr_size es < n ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (compile_builtin_dispatch ce rt ty bi es) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce)
    (builtin_child_callback n compile_builtin_dispatch ce rt ty bi es)
    (\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ value_shape_ok s v)
Proof
  strip_tac >> irule alloc_run_struct_child_frame >>
  irule_at Any ownership_builtin_child_shape >>
  simp[] >> irule alloc_run_builtin_child_callback_owned >> simp[]
QED

Theorem alloc_run_actual_type_child_frame:
  type_builtin_arity tb <= LENGTH es /\ ~supported_exprs_exists expr_shape_root es /\
  shape_stable R /\ (list_size expr_size es < n ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (compile_type_builtin_dispatch ce vt ty tb rt es) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce)
    (type_child_callback n compile_type_builtin_dispatch ce vt ty tb rt es)
    (\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ value_shape_ok s v)
Proof
  strip_tac >> irule alloc_run_struct_child_frame >>
  irule_at Any ownership_type_child_shape >>
  simp[] >> irule alloc_run_type_child_callback_owned >> simp[]
QED
