Theory makeSsaCurrentOrdinaryJoint
Ancestors makeSsaCurrentFinalSelector makeSsaCurrentFullWrites
  makeSsaCurrentChronologicalTransition makeSsaCurrentLastEvent
  makeSsaCurrentPairedRuntime makeSsaCurrentJointRuntime makeSsaCurrentOrdinary
  makeSsaCurrentActualRetention makeSsaCurrentRenameTrace makeSsaCurrentAllocation
  makeSsaCurrentDefs makeSsaCurrentSimDefs venomWf venomExecSemantics list alist

Theorem current_inst_trace_full_reconnect:
  current_inst_trace anns inst s rs H E inst' s' rt H' E' /\
  current_annotations_ok U H anns /\
  current_allocation_consistent U H s rs /\ current_env_realizes H E rs U /\
  current_env_history_owners H E /\ (!v. MEM v D ==> MEM v U) /\
  MAP FST events = GENLIST I (LENGTH inst.inst_outputs) /\
  (!v. MEM v (current_before_outputs inst.inst_outputs D) ==>
    ALOOKUP M v = ALOOKUP N (latest_current_name rs v)) ==>
  current_last_event_reconnect M N rt D inst.inst_outputs inst'.inst_outputs events
Proof
  strip_tac >> simp[current_last_event_reconnect_def] >> rpt strip_tac
  >- (irule current_inst_trace_last_event_hit >> metis_tac[]) >>
  `~MEM v inst.inst_outputs` by metis_tac[current_last_event_hit_full_none] >>
  `latest_current_name rt v = latest_current_name rs v` by
    metis_tac[current_inst_trace_absent_latest] >>
  fs[current_before_outputs_def, MEM_FILTER]
QED

Theorem current_inst_trace_base_fields:
  current_inst_trace anns inst s rs H E inst' s' rt H' E' /\ inst.inst_opcode <> PHI ==>
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >> gvs[] >>
  drule current_outputs_trace_owned_names >>
  disch_then (mp_tac o MATCH_MP LIST_REL_LENGTH) >> metis_tac[LENGTH_MAP]
QED

Theorem current_inst_trace_ordinary_joint:
  current_inst_trace anns inst s rs H E inst' s' rt H' E' /\
  current_annotations_ok U H anns /\
  current_allocation_consistent U H s rs /\ current_env_realizes H E rs U /\
  current_env_history_owners H E /\ (!v. MEM v D ==> MEM v U) /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  current_joint_rel V M N rs
    (venomInst$operand_vars inst.inst_operands ++ current_before_outputs inst.inst_outputs D) st st' /\
  step_inst_base inst st = OK after ==>
  current_allocation_consistent U H' s' rt /\ current_env_realizes H' E' rt U /\
  current_env_history_owners H' E' /\
  ?n events after'.
    step_inst_base inst' st' = OK after' /\
    current_indexed_writes inst.inst_outputs events st after /\
    current_indexed_writes inst'.inst_outputs events st' after' /\
    MAP FST events = GENLIST I (LENGTH inst.inst_outputs) /\
    current_joint_rel (current_event_valuation V visit l i n events)
      (current_event_origins inst.inst_outputs M visit l i n events)
      (current_event_origins inst'.inst_outputs N visit l i n events) rt D after after'
Proof
  strip_tac >>
  `current_allocation_consistent U H' s' rt /\ current_env_realizes H' E' rt U` by
    (irule current_inst_trace_preserves >> metis_tac[]) >>
  `current_env_history_owners H' E'` by metis_tac[current_inst_trace_history_owners] >>
  simp[] >>
  `inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
   inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
   LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs` by
    metis_tac[current_inst_trace_base_fields] >>
  `current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st'` by
    (drule current_joint_name_agree >> simp[current_name_agree_def]) >>
  `?after' events. step_inst_base inst' st' = OK after' /\
    current_indexed_writes inst.inst_outputs events st after /\
    current_indexed_writes inst'.inst_outputs events st' after' /\
    MAP FST events = GENLIST I (LENGTH inst.inst_outputs) /\
    execution_frame after = execution_frame after' /\
    after.vs_current_bb = after'.vs_current_bb /\ after.vs_prev_bb = after'.vs_prev_bb` by
    (irule current_step_inst_base_full_writes >>
     fs[current_joint_rel_def] >> qexists_tac `rs` >> simp[]) >>
  pop_assum strip_assume_tac >>
  `?n:num. !k. n <= k ==> current_origin_absent (visit,l,i,k) M /\
     current_origin_absent (visit,l,i,k) N` by irule current_shared_origin_ordinal_fresh >>
  pop_assum strip_assume_tac >>
  `current_origin_realizes (current_event_valuation V visit l i n events)
     (current_event_origins inst.inst_outputs M visit l i n events) after /\
   current_origin_realizes (current_event_valuation V visit l i n events)
     (current_event_origins inst'.inst_outputs N visit l i n events) after'` by
    (irule current_indexed_writes_origins >> gvs[current_joint_rel_def] >> metis_tac[]) >>
  `current_last_event_reconnect M N rt D inst.inst_outputs inst'.inst_outputs events` by
    (irule current_inst_trace_full_reconnect >> gvs[current_joint_rel_def] >> metis_tac[]) >>
  qexistsl_tac [`n`, `events`, `after'`] >>
  drule current_last_event_reconnect_origins >>
  gvs[current_joint_rel_def]
QED
