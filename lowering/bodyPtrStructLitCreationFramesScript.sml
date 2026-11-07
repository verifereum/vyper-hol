Theory bodyPtrStructLitCreationFrames
Ancestors bodyPtrStructLitCreationShape bodyPtrStructLitEmitterFrame
  bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitOwnershipCallSuffix
  bodyPtrStructLitOwnershipIfexpFrame bodyPtrStructLitOwnershipSteps
  loweringShapeDefs loweringShapeRules loweringShapeProps
  exprLowering builtinCreate compileEnv context list

Theorem alloc_run_create_blueprint_check_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\
      plain_operand s target /\ plain_operand s offset)
    (compile_create_blueprint_check target offset)
    (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  simp[alloc_run_compile_create_blueprint_check, create_blueprint_check_shape]
QED

Theorem alloc_run_create_proxy_buf_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s target)
    (compile_create_proxy_buf target)
    (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >> simp[compile_create_proxy_buf_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\buf s. shape_state s /\ (R s /\ plain_operand s target) /\
    plain_operand s buf.buf_operand` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_alloc_buffer_frame >>
      qexists `\s. R s /\ plain_operand s target` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[target]` shape_stable_plain_operands)]) >>
  qx_gen_tac `buf` >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[Once comp_bind_def, comp_return_def] >> simp[SF ETA_ss] >>
  rpt (FIRST [ho_match_mp_tac alloc_run_op_bind,
      ho_match_mp_tac alloc_run_void_bind] >>
    simp[SRULE [stackPlanTypesTheory.is_label_operand_def]
      (Q.INST [`op` |-> `Lit w`] (SPEC_ALL plain_operand_def))] >>
    (conj_tac >- (rpt (ho_match_mp_tac shape_stable_conj >> conj_tac) >>
      simp[SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)])) >>
    (conj_tac >- (rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[plain_operand_def,
        stackPlanTypesTheory.is_label_operand_def])) >> rpt gen_tac) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
