Theory makeSsaCurrentReverseRuntime
Ancestors
  o1FrameLockstep venomExecSemantics passSimulationDefs contextCodegenRel venomInst venomExecProps

Theorem current_step_copy_not_abort:
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = NOP) ==>
  step_inst fuel C inst st <> Abort a t
Proof
  strip_tac >> gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()]
QED

Theorem current_terminating_suffix_instruction:
  terminates (exec_block fuel C bb st) ==>
  ?inst. get_instruction bb st.vs_inst_idx = SOME inst
Proof
  Cases_on `get_instruction bb st.vs_inst_idx` >> simp[] >>
  simp[Once exec_block_def, terminates_def]
QED

Theorem current_terminating_suffix_active:
  lookup_block st.vs_current_bb fn.fn_blocks = SOME bb /\
  terminates (exec_block fuel C bb st) ==>
  ?inst. active_inst fn inst st
Proof
  strip_tac >> drule current_terminating_suffix_instruction >> strip_tac >>
  `bb.bb_label = st.vs_current_bb` by
    metis_tac[lookup_block_label] >>
  drule lookup_block_MEM >> strip_tac >>
  fs[get_instruction_def, AllCaseEqs()] >>
  qexists `inst` >> simp[active_inst_def] >> qexists `bb` >> simp[]
QED
