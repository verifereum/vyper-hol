Theory bodyPtrStructLitLoopShapeControl
Ancestors bodyPtrStructLitLoopShapeEmit loweringShapeProps loweringShapeRules
  loweringShapeDefs compileEnv venomInst unitShapeDefs stackPlanTypes

Theorem loop_shape_header:
  shape_stable R /\ compiler_label cond /\ compiler_label body_lbl /\
  compiler_label exit /\ exit <> body_lbl /\
  (!s. R s ==> plain_operand s (Var ctr)) /\
  shape_step F compiler_label R test_code (\v s. R s /\ plain_operand s v) /\
  shape_step F compiler_label R body_lbl_code Q ==>
  shape_step F compiler_label R
    (do emit_inst ASSIGN [Lit 0w] [ctr];
        emit_inst JMP [Label cond] [];
        new_block cond;
        test <- test_code;
        emit_inst JNZ [test; Label exit; Label body_lbl] [];
        new_block body_lbl;
        body_lbl_code od) Q
Proof
  strip_tac >> irule shape_step_ignore_bind >> qexists `\u s. R s` >>
  reverse conj_tac
  >- (ho_match_mp_tac loop_shape_assign >> simp[] >>
      simp[plain_operand_def, is_label_operand_def]) >>
  gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >> qexists `\u s. R s` >>
  reverse conj_tac >- (ho_match_mp_tac loop_shape_jmp >> simp[SF ETA_ss]) >>
  gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >> qexists `\u s. R s` >>
  reverse conj_tac >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> BETA_TAC >> irule shape_step_bind >>
  qexists `\v s. R s /\ plain_operand s v` >> simp[SF ETA_ss] >>
  qx_gen_tac `v` >> irule shape_step_ignore_bind >> qexists `\u s. R s /\ plain_operand s v` >>
  reverse conj_tac
  >- (ho_match_mp_tac loop_shape_jnz >> simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >> qexists `\u s. R s` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_new_block >>
      qexistsl [`R`, `compiler_label`] >> simp[SF ETA_ss]) >>
  simp[SF ETA_ss]
QED
