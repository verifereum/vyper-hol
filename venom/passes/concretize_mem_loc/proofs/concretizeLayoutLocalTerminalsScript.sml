Theory concretizeLayoutLocalTerminals
Ancestors ptrDiscipline venomExecSemantics venomState list

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

val _ = if null (hyp concretize_stop_sink_complete) andalso
           null (hyp concretize_invalid_complete) then ()
        else raise Fail "simple terminal exports have hypotheses";
val _ = export_theory();
