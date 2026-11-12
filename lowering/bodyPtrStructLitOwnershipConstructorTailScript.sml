Theory bodyPtrStructLitOwnershipConstructorTail
Ancestors
  bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipLoops
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipShape ctorShapeProps loweringShapeDefs
  bodyPtrStructLitLoopShapeDynBody bodyPtrStructLitOwnershipStmtHelpers
  loweringShapeProps loweringShapeRules unitShapeDefs venomInst
  moduleLowering compileEnv context

Theorem alloc_run_constructor_epilogue_fresh:
  alloc_run fresh_outputs (compile_constructor_epilogue rt ilen imm)
    (\u s. fresh_outputs s)
Proof
  simp[compile_constructor_epilogue_def] >> IF_CASES_TAC >>
  simp[comp_ignore_bind_def, loop_comp_return_bind] >>
  rpt (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
            SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
            SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer] >>
    gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_empty_fresh]
QED

Theorem alloc_run_simple_deploy_fresh:
  alloc_run fresh_outputs (compile_simple_deploy rt ilen)
    (\u s. fresh_outputs s)
Proof
  simp[compile_simple_deploy_def, comp_ignore_bind_def, loop_comp_return_bind] >>
  rpt (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
            SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer] >>
    gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_empty_fresh]
QED

Theorem alloc_run_constructor_epilogue_shape_fresh:
  alloc_run (\s. shape_state s /\ plain_operand s imm)
    (compile_constructor_epilogue rt ilen imm)
    (\u s. shape_state s /\ fresh_outputs s)
Proof
  irule alloc_run_conseq >> irule_at Any alloc_run_shape_join >>
  irule_at Any compile_constructor_epilogue_shape >>
  irule_at Any alloc_run_constructor_epilogue_fresh >>
  simp[shape_state_def, shape_base_fresh_outputs]
QED

Theorem alloc_run_simple_deploy_shape_fresh:
  alloc_run shape_state (compile_simple_deploy rt ilen)
    (\u s. shape_state s /\ fresh_outputs s)
Proof
  irule alloc_run_conseq >> irule_at Any alloc_run_shape_join >>
  irule_at Any compile_simple_deploy_shape >>
  irule_at Any alloc_run_simple_deploy_fresh >>
  simp[shape_state_def, shape_base_fresh_outputs]
QED

Theorem alloc_run_constructor_tail_fresh:
  alloc_run fresh_outputs
    (do cs <- comp_get;
        (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
        new_block lbl;
        (if nr then compile_nonreentrant_unlock key tr F else return ());
        compile_constructor_epilogue rt ilen imm od)
    (\u s. fresh_outputs s)
Proof
  simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\cs s. fresh_outputs s` >> reverse conj_tac
  >- simp[comp_get_def, alloc_run_def, alloc_frame_refl] >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. fresh_outputs s` >> reverse conj_tac
  >- (IF_CASES_TAC
      >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_empty_fresh]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_new_block_fresh] >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. fresh_outputs s` >> reverse conj_tac
  >- (Cases_on `nr`
      >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_nonreentrant_unlock] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  gen_tac >> simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_constructor_epilogue_fresh]
QED

Theorem structlit_constructor_fallthrough_shape:
  jump_label_ok lbl ==>
  shape_step F compiler_label (\s. T)
    (do cs <- comp_get;
        if block_is_terminated cs then return () else emit_inst JMP [Label lbl] [] od)
    (\u s. T)
Proof
  strip_tac >> irule shape_step_bind >> qexists `\cs s. T` >> conj_tac
  >- (gen_tac >> simp[] >> IF_CASES_TAC
      >- (irule shape_step_return >> simp[]) >>
      irule shape_step_conseq >> irule_at Any shape_step_emit_inst >>
      qexistsl [`\s. T`, `compiler_label`] >>
      simp[shape_stable_def, label_or_plain_def,
        stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
        venomInstTheory.mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
        inst_jump_labels_ok_def, is_terminator_def, is_read0_opcode_def,
        label_positions_ok_def, operand_case_not_label, is_param_opcode_def]) >>
  simp[shape_step_def, comp_get_def, shape_extends_refl]
QED

Theorem structlit_constructor_tail_shape:
  jump_label_ok lbl ==>
  shape_step F jump_label_ok (\s. plain_operand s imm)
    (do cs <- comp_get;
        (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
        new_block lbl;
        (if nr then compile_nonreentrant_unlock key tr F else return ());
        compile_constructor_epilogue rt ilen imm od) (\u s. T)
Proof
  strip_tac >>
  `shape_stable (\s. plain_operand s imm)` by
    (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qsuff_tac `shape_step F jump_label_ok (\s. plain_operand s imm)
    (do (do cs <- comp_get;
            if block_is_terminated cs then return () else emit_inst JMP [Label lbl] [] od);
        new_block lbl;
        (if nr then compile_nonreentrant_unlock key tr F else return ());
        compile_constructor_epilogue rt ilen imm od) (\u s. T)`
  >- simp[comp_ignore_bind_def, comp_bind_assoc] >>
  irule shape_step_ignore_bind >> qexists `\u s. plain_operand s imm` >> conj_tac
  >- (gen_tac >> simp[] >> irule shape_step_ignore_bind >>
      qexists `\u s. plain_operand s imm` >> conj_tac
      >- (gen_tac >> simp[] >> irule shape_step_ignore_bind >>
          qexists `\u s. plain_operand s imm` >> conj_tac
          >- (gen_tac >> simp[] >> irule shape_step_conseq >>
              irule_at Any compile_constructor_epilogue_shape >> simp[jump_label_ok_def]) >>
          Cases_on `nr`
          >- (simp[] >> irule shape_step_conseq >> irule_at Any shape_step_frame >>
              irule_at Any compile_nonreentrant_unlock_shape >>
              qexistsl [`\s. plain_operand s imm`, `compiler_label`] >> simp[jump_label_ok_def]) >>
          simp[] >> irule shape_step_return >> simp[]) >>
      simp[SF ETA_ss] >> irule (SRULE [SF ETA_ss] shape_step_new_block) >> simp[] >>
      metis_tac[jump_label_ok_not_internal]) >>
  irule shape_step_conseq >> irule_at Any shape_step_frame >>
  irule_at Any structlit_constructor_fallthrough_shape >>
  qexists `\s. plain_operand s imm` >> simp[jump_label_ok_def]
QED

Theorem alloc_run_constructor_tail_shape_fresh:
  jump_label_ok lbl ==>
  alloc_run (\s. shape_state s /\ plain_operand s imm)
    (do cs <- comp_get;
        (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
        new_block lbl;
        (if nr then compile_nonreentrant_unlock key tr F else return ());
        compile_constructor_epilogue rt ilen imm od)
    (\u s. shape_state s /\ fresh_outputs s)
Proof
  strip_tac >> irule alloc_run_conseq >> irule_at Any alloc_run_shape_join >>
  irule_at Any structlit_constructor_tail_shape >>
  irule_at Any alloc_run_constructor_tail_fresh >>
  simp[shape_state_def, shape_base_fresh_outputs]
QED
