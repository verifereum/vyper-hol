Theory concretizeLayoutLocalTerminals
Ancestors ptrDiscipline venomExecSemantics venomState list frameRelocationValues passSharedFrame

Theorem concretize_stop_sink_complete:
  MEM inst.inst_opcode [STOP; SINK] /\
  dead_result_rel D (Halt s) (Halt t) /\
  step_inst_base inst s = Halt post ==>
  ?post'. step_inst_base inst t = Halt post' /\
    dead_result_rel D (Halt post) (Halt post')
Proof
  simp[MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = Halt post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >> strip_tac >> gvs[] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  fs[dead_result_rel_def, halt_state_def]
QED

Theorem concretize_invalid_complete:
  inst.inst_opcode = INVALID /\ step_inst_base inst s = Abort a post ==>
  ?post'. step_inst_base inst t = Abort a post' /\
    dead_result_rel D (Abort a post) (Abort a post')
Proof
  strip_tac >> qpat_x_assum `step_inst_base inst s = Abort a post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >> strip_tac >> gvs[] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >> simp[dead_result_rel_def]
QED

Theorem concretize_revert_complete:
  inst.inst_opcode = REVERT /\ variable_domains s t /\
  s.vs_labels = t.vs_labels /\
  step_inst_base inst s = Abort a post ==>
  ?post'. step_inst_base inst t = Abort a post' /\
    dead_result_rel D (Abort a post) (Abort a post')
Proof
  strip_tac >>
  `!op. eval_operand op s = NONE <=> eval_operand op t = NONE` by
    (gen_tac >> irule operand_domain_agreement >> simp[]) >>
  qpat_x_assum `step_inst_base inst s = Abort a post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  Cases_on `eval_operand off_op t`
  >- metis_tac[optionTheory.NOT_NONE_SOME] >>
  Cases_on `eval_operand sz_op t`
  >- metis_tac[optionTheory.NOT_NONE_SOME] >>
  simp[dead_result_rel_def]
QED

Theorem eval_operands_domain_agreement:
  !ops s t. variable_domains s t /\ s.vs_labels = t.vs_labels ==>
  (IS_SOME (eval_operands ops s) <=> IS_SOME (eval_operands ops t))
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand h s = NONE <=> eval_operand h t = NONE` by
    (irule operand_domain_agreement >> simp[]) >>
  first_x_assum (drule_then assume_tac) >>
  Cases_on `eval_operand h s` >> Cases_on `eval_operand h t` >>
  Cases_on `eval_operands ops s` >> Cases_on `eval_operands ops t` >> gvs[]
QED

Theorem concretize_static_write_abort_complete:
  MEM inst.inst_opcode [SSTORE; TSTORE; LOG] /\
  variable_domains s t /\ s.vs_labels = t.vs_labels /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  step_inst_base inst s = Abort a post ==>
  ?post'. step_inst_base inst t = Abort a post' /\
    dead_result_rel D (Abort a post) (Abort a post')
Proof
  simp[MEM] >> strip_tac >>
  drule step_inst_base_static_write_abort >> simp[] >> strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands t)` by
    (drule_all eval_operands_domain_agreement >>
     disch_then (qspec_then `inst.inst_operands` mp_tac) >> simp[]) >>
  `step_inst_base inst t = Abort ExHalt_abort (halt_state (set_returndata [] t))` by
    (irule step_inst_base_static_write_guard >> simp[]) >>
  gvs[dead_result_rel_def]
QED

val _ = if null (hyp eval_operands_domain_agreement) andalso
           null (hyp concretize_static_write_abort_complete) andalso
           null (hyp concretize_stop_sink_complete) andalso
           null (hyp concretize_invalid_complete) andalso
           null (hyp concretize_revert_complete) then ()
        else raise Fail "simple terminal exports have hypotheses";
val _ = export_theory();
