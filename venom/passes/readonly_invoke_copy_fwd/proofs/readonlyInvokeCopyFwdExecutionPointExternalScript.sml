Theory readonlyInvokeCopyFwdExecutionPointExternal
Ancestors
  readonlyInvokeCopyFwdExecutionPointNext readonlyInvokeCopyFwdExecutionCallNext
  readonlyInvokeCopyFwdExecutionDelegateNext readonlyInvokeCopyFwdExecutionCreateNext
  readonlyInvokeCopyFwdExecutionSteps o1PassContract unitShapeDefs
  venomExecSemantics venomInst venomWf venomState ptrDiscipline finite_map list words

Theorem ricf_execution_point_external:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  o1_ctx_shape C /\ o1_fn_shape C fn /\ wf_ssa fn /\
  ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ taint_within D C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
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
  `wf_function fn /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA /\
   inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> MCOPY` by
    fs[o1_fn_shape_def, MEM, is_terminator_def] >>
  `opaque_use_ok fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  irule ricf_execution_point_ordinary >> simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = DELEGATECALL`
  >- (drule_all ricf_execution_delegate_next >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [CREATE;CREATE2]`
  >- (drule_all ricf_execution_create_next >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  `MEM inst.inst_opcode [CALL;STATICCALL]` by fs[MEM] >>
  drule_all ricf_execution_call_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED
