Theory bodyPtrStructLitLoopShapeTail
Ancestors bodyPtrStructLitLoopShapeEmit bodyPtrStructLitEmitterFrame
  loweringShapeProps loweringShapeRules loweringShapeDefs compileEnv
  venomInst unitShapeDefs stackPlanTypes context

Theorem loop_shape_increment_exit:
  shape_stable R /\ compiler_label cond /\ compiler_label exit ==>
  shape_step F compiler_label (\s. R s /\ plain_operand s (Var ctr))
    (do next <- emit_op ADD [Var ctr; Lit 1w];
        emit_inst ASSIGN [next] [ctr];
        emit_inst JMP [Label cond] [];
        new_block exit od)
    (\u s. R s /\ plain_operand s (Var ctr))
Proof
  strip_tac >> irule loop_shape_op_bind >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands),
    SRULE [is_label_operand_def]
      (Q.INST [`op` |-> `Lit w`] (SPEC_ALL plain_operand_def))] >>
  conj_tac
  >- (rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[plain_operand_def, is_label_operand_def]) >>
  qx_gen_tac `next` >> irule shape_step_ignore_bind >>
  qexists `\u s. (R s /\ plain_operand s (Var ctr)) /\ plain_operand s next` >>
  reverse conj_tac
  >- (ho_match_mp_tac loop_shape_assign >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
  qexists `\u s. (R s /\ plain_operand s (Var ctr)) /\ plain_operand s next` >>
  reverse conj_tac
  >- (ho_match_mp_tac loop_shape_jmp >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  gen_tac >> irule shape_step_conseq >> irule_at Any shape_step_new_block >>
  qexistsl [`\s. (R s /\ plain_operand s (Var ctr)) /\ plain_operand s next`,
    `compiler_label`] >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]
QED
