Theory readonlyInvokeCopyFwdExecutionPointLoads
Ancestors
  readonlyInvokeCopyFwdExecutionPointNext readonlyInvokeCopyFwdExecutionWordLoads
  readonlyInvokeCopyFwdExecutionSteps o1PassContract unitMemInv venomExecSemantics venomInst
  venomWf venomState ptrDiscipline finite_map list words

Theorem ricf_execution_point_wordload:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  wf_function fn /\ ssa_form fn /\ opaque_use_ok fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [MLOAD;ILOAD] /\ inst.inst_operands = [addr] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
      sites maps targets stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
   inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
   inst.inst_opcode <> MCOPY` by fs[MEM, is_terminator_def] >>
  irule ricf_execution_point_ordinary >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all ricf_execution_wordload_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED
