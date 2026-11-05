Theory makeSsaCurrentOriginalSingletonStep
Ancestors makeSsaCurrentOriginalFinalSlots makeSsaCurrentFinalWriteSlots
  makeSsaCurrentInstructionSingleton makeSsaCurrentValueInvariant
  makeSsaCurrentFullWrites makeSsaCurrentPairedWrites makeSsaCurrentOrdinary
  makeSsaCurrentOrdinaryJoint makeSsaCurrentOutputNames makeSsaCurrentTreeTrace
  makeSsaCurrentCertificate
  makeSsaCurrentRenameTrace makeSsaCurrentSimDefs makeSsaCurrentAllocation
  venomWf venomInst venomExecSemantics stateFrame list

Theorem current_original_step_singleton:
  wf_function fn /\ b < LENGTH fn.fn_blocks /\
  i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  inst = EL i (EL b fn.fn_blocks).bb_instructions /\
  current_history_valid U Hfinal /\
  LENGTH inst'.inst_outputs = LENGTH inst.inst_outputs /\
  (!j. j < LENGTH inst'.inst_outputs ==>
    current_token_name Hfinal (CurrentOriginal (EL b fn.fn_blocks).bb_label i j) =
      SOME (EL j inst'.inst_outputs)) /\
  current_inst_trace anns inst s rs H E inst' s' rt H' E' /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st' /\
  current_singleton_agree (current_instruction_singleton_table fn Hfinal) st st' /\
  step_inst_base inst st = OK after ==>
  ?after'. step_inst_base inst' st' = OK after' /\
    current_singleton_agree (current_instruction_singleton_table fn Hfinal) after after' /\
    execution_frame after = execution_frame after' /\
    after.vs_current_bb = after'.vs_current_bb /\ after.vs_prev_bb = after'.vs_prev_bb
Proof
  strip_tac >>
  drule current_inst_trace_base_fields >> simp[] >> strip_tac >>
  `?after' events. step_inst_base inst' st' = OK after' /\
    current_indexed_writes inst.inst_outputs events st after /\
    current_indexed_writes inst'.inst_outputs events st' after' /\
    MAP FST events = GENLIST I (LENGTH inst.inst_outputs) /\
    execution_frame after = execution_frame after' /\
    after.vs_current_bb = after'.vs_current_bb /\ after.vs_prev_bb = after'.vs_prev_bb` by
    (irule current_step_inst_base_full_writes >>
     asm_rewrite_tac[] >> qexists_tac `rs` >> metis_tac[]) >>
  `current_table_final_slots (current_instruction_singleton_table fn Hfinal)
    inst.inst_outputs inst'.inst_outputs` by
    (gvs[] >> irule current_original_output_final_slots >> metis_tac[]) >>
  `current_singleton_agree (current_instruction_singleton_table fn Hfinal) after after'` by
    (irule current_singleton_agree_final_slots >> metis_tac[]) >>
  qexists_tac `after'` >> gvs[execution_frame_def]
QED

Theorem current_event_original_step_singleton:
  wf_function fn /\ b < LENGTH fn.fn_blocks /\
  i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  inst = EL i (EL b fn.fn_blocks).bb_instructions /\
  inst' = EL (LENGTH pre+i) ren /\
  current_history_valid U Hfinal /\
  current_event_trace A Hfinal
    (l,bb,se,rse,He,Ee,ren,se1,rse1,He1,Ee1,bbs1,bbs2) /\
  current_event_valid A V
    (l,bb,se,rse,He,Ee,ren,se1,rse1,He1,Ee1,bbs1,bbs2) /\
  A l = current_block_annotations (EL b fn.fn_blocks) pre /\
  current_inst_trace anns inst s rs H E inst' s' rt H' E' /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st' /\
  current_singleton_agree (current_instruction_singleton_table fn Hfinal) st st' /\
  step_inst_base inst st = OK after ==>
  ?after'. step_inst_base inst' st' = OK after' /\
    current_singleton_agree (current_instruction_singleton_table fn Hfinal) after after' /\
    execution_frame after = execution_frame after' /\
    after.vs_current_bb = after'.vs_current_bb /\ after.vs_prev_bb = after'.vs_prev_bb
Proof
  rpt strip_tac >> irule current_original_step_singleton >>
  `LENGTH inst'.inst_outputs = LENGTH inst.inst_outputs` by
    metis_tac[current_event_original_output_length] >>
  `!j. j < LENGTH inst'.inst_outputs ==>
    current_token_name Hfinal (CurrentOriginal (EL b fn.fn_blocks).bb_label i j) =
      SOME (EL j inst'.inst_outputs)` by
    (rpt strip_tac >>
     `j < LENGTH (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs` by metis_tac[] >>
     drule_all current_event_original_output_name >> gvs[]) >>
  metis_tac[]
QED
