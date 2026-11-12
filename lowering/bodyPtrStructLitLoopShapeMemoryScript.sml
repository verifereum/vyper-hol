Theory bodyPtrStructLitLoopShapeMemory
Ancestors bodyPtrStructLitLoopShapeEmit bodyPtrStructLitEmitterFrame
  loweringShapeProps loweringShapeRules loweringShapeDefs compileEnv
  venomInst unitShapeDefs stackPlanTypes context

Theorem loop_shape_offset:
  shape_stable R ==>
  shape_step F compiler_label
    (\s. R s /\ plain_operand s base_op /\ plain_operand s (Var ctr))
    (if scale = 1 then emit_op ADD [base_op; Var ctr]
     else do scaled <- emit_op MUL [Var ctr; Lit (n2w scale)];
             emit_op ADD [base_op; scaled] od)
    (\v s. (R s /\ plain_operand s base_op /\ plain_operand s (Var ctr)) /\
      plain_operand s v)
Proof
  strip_tac >> IF_CASES_TAC
  >- (ho_match_mp_tac loop_shape_op >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >>
      rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[]) >>
  irule loop_shape_op_bind >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands),
    SRULE [is_label_operand_def]
      (Q.INST [`op` |-> `Lit w`] (SPEC_ALL plain_operand_def))] >>
  conj_tac
  >- (rpt strip_tac >> irule (cj 2 loop_extra_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[plain_operand_def, is_label_operand_def]) >>
  gen_tac >> irule shape_step_conseq >> irule_at Any loop_shape_op >>
  qexists `\s. (R s /\ plain_operand s base_op /\ plain_operand s (Var ctr)) /\
    plain_operand s v` >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >>
  rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >>
  simp[] >> qexists `s` >> simp[]
QED

Theorem loop_shape_ptr_store:
  shape_stable R ==>
  shape_step F compiler_label
    (\s. R s /\ plain_operand s dst /\ plain_operand s src)
    (compile_ptr_store is_ctor NONE loc dst src)
    (\u s. R s /\ plain_operand s dst /\ plain_operand s src)
Proof
  strip_tac >> Cases_on `loc` >> Cases_on `is_ctor` >>
  simp[compile_ptr_store_def, compile_imm_store_word_def] >>
  ho_match_mp_tac loop_shape_void >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >>
  rpt strip_tac >>
  gvs[plain_operand_def, lowered_inst_ok_def, mk_inst_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def]
QED
