Theory bodyPtrStructLitLoopShapeDynAddress
Ancestors bodyPtrStructLitLoopShapeEmit bodyPtrStructLitEmitterFrame
  loweringShapeRules loweringShapeDefs compileEnv stackPlanTypes

Theorem loop_shape_index_address:
  shape_stable R ==>
  shape_step F compiler_label
    (\s. R s /\ plain_operand s base_op /\ plain_operand s (Var ctr))
    (do scaled_op <- emit_op MUL [Var ctr; Lit scale];
        off <- emit_op ADD [Lit hdr; scaled_op];
        emit_op ADD [base_op; off] od)
    (\v s. (R s /\ plain_operand s base_op /\ plain_operand s (Var ctr)) /\ plain_operand s v)
Proof
  strip_tac >> irule loop_shape_op_bind >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands),
    SRULE [is_label_operand_def]
      (Q.INST [`op` |-> `Lit w`] (SPEC_ALL plain_operand_def))] >> conj_tac
  >- (rpt strip_tac >> irule (cj 2 loop_extra_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[plain_operand_def, is_label_operand_def]) >>
  qx_gen_tac `scaled_op` >> irule loop_shape_op_bind >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands),
    SRULE [is_label_operand_def]
      (Q.INST [`op` |-> `Lit w`] (SPEC_ALL plain_operand_def))] >> conj_tac
  >- (rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[plain_operand_def, is_label_operand_def]) >>
  qx_gen_tac `off` >> irule shape_step_conseq >> irule_at Any loop_shape_op >>
  qexists `\s. ((R s /\ plain_operand s base_op /\ plain_operand s (Var ctr)) /\
    plain_operand s scaled_op) /\ plain_operand s off` >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >>
  rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >> simp[] >> qexists `s` >> simp[]
QED

Theorem loop_shape_single_slot_address:
  shape_stable R ==>
  shape_step F compiler_label
    (\s. R s /\ plain_operand s dst /\ plain_operand s (Var ctr))
    (do off <- emit_op ADD [Var ctr; Lit 1w]; emit_op ADD [dst; off] od)
    (\v s. (R s /\ plain_operand s dst /\ plain_operand s (Var ctr)) /\ plain_operand s v)
Proof
  strip_tac >> irule loop_shape_op_bind >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands),
    SRULE [is_label_operand_def]
      (Q.INST [`op` |-> `Lit w`] (SPEC_ALL plain_operand_def))] >> conj_tac
  >- (rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[plain_operand_def, is_label_operand_def]) >>
  qx_gen_tac `off` >> irule shape_step_conseq >> irule_at Any loop_shape_op >>
  qexists `\s. (R s /\ plain_operand s dst /\ plain_operand s (Var ctr)) /\
    plain_operand s off` >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >>
  rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >> simp[] >> qexists `s` >> simp[]
QED
