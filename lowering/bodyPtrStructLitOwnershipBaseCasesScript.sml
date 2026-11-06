Theory bodyPtrStructLitOwnershipBaseCases
Ancestors bodyPtrStructLitOwnershipLiterals bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps loweringShapeDefs loweringShapeProps
  exprLowering compileEnv context finite_map vyperAST

Theorem alloc_run_compile_name_vv:
  alloc_run fresh_outputs (compile_name_vv ce rt id) (\v s. fresh_outputs s)
Proof
  simp[compile_name_vv_def] >> rpt CASE_TAC >> simp[comp_ignore_bind_def] >>
  TRY (simp[comp_return_def, alloc_run_def, alloc_frame_refl] >> NO_TAC) >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss, listTheory.EVERY_DEF] (Q.INST [`outs` |-> `[]`, `opc` |-> `INVALID`] alloc_run_emit_inst_fresh)] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_expr_body_literal:
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr_body cfn bfn tfn ce ty (Literal rt l)) (\v s. T)
Proof
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_expr_body_def, expr_type_def] >> simp[SF ETA_ss] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_compile_literal_vv >>
  simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]
QED

Theorem alloc_run_expr_body_name:
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr_body cfn bfn tfn ce ty (Name rt id)) (\v s. T)
Proof
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_expr_body_def, expr_type_def] >> simp[SF ETA_ss] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_compile_name_vv >>
  simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]
QED

Theorem alloc_run_expr_body_flag_member:
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr_body cfn bfn tfn ce ty (FlagMember rt nsid mem)) (\v s. T)
Proof
  simp[alloc_run_def, compile_expr_body_def, alloc_frame_refl]
QED

Theorem alloc_run_expr_body_top_level_name:
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr_body cfn bfn tfn ce ty (TopLevelName rt nsid)) (\v s. T)
Proof
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_expr_body_def, expr_type_def] >> rpt CASE_TAC >> simp[] >>
  TRY (simp[alloc_run_def, alloc_frame_refl] >> NO_TAC) >>
  simp[alloc_run_def, AllCaseEqs()] >> rpt strip_tac >>
  rename1 `shape_state start` >>
  `fresh_outputs start` by metis_tac[shape_state_def, shape_base_fresh_outputs] >>
  pairarg_tac >> gvs[] >>
  mp_tac (Q.INST [`outs` |-> `[]`, `ops` |-> `[]`, `opc` |-> `INVALID`]
    alloc_run_emit_inst_fresh) >>
  simp[alloc_run_def] >> disch_then drule_all >> simp[]
QED
