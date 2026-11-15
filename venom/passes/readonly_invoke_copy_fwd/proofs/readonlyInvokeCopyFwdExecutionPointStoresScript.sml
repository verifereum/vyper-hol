Theory readonlyInvokeCopyFwdExecutionPointStores
Ancestors
  readonlyInvokeCopyFwdExecutionPointNext readonlyInvokeCopyFwdExecutionMemoryStores
  readonlyInvokeCopyFwdExecutionWordStores
  readonlyInvokeCopyFwdExecutionSteps o1PassContract venomExecSemantics venomInst
  venomWf venomState ptrDiscipline finite_map list words

Theorem ricf_execution_point_byte_store:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  o1_ctx_shape C /\ o1_fn_shape C fn /\ wf_ssa fn /\
  ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = MSTORE8 /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
      sites maps targets stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `wf_function fn /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA /\
   inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> MCOPY` by
    fs[o1_fn_shape_def, is_terminator_def] >>
  irule ricf_execution_point_ordinary >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all ricf_execution_byte_store_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED

Theorem ricf_execution_point_word_store:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  o1_ctx_shape C /\ o1_fn_shape C fn /\ wf_ssa fn /\
  ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [MSTORE;ISTORE] /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
      sites maps targets stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `wf_function fn /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA /\
   inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> MCOPY` by
    fs[o1_fn_shape_def, MEM, is_terminator_def] >>
  irule ricf_execution_point_ordinary >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all ricf_execution_word_store_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED
