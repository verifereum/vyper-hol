Theory readonlyInvokeCopyFwdExecutionPointObservers
Ancestors
  readonlyInvokeCopyFwdExecutionPointNext readonlyInvokeCopyFwdExecutionObserverOperands
  readonlyInvokeCopyFwdExecutionBump readonlyInvokeCopyFwdExecutionSteps
  o1PassContract unitShapeDefs contextCodegenRel ptrDiscipline venomWf venomExecSemantics venomInst venomState
  finite_map list words

Theorem ricf_execution_point_sha3:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  o1_fn_shape C fn /\ EVERY wf_ssa C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = SHA3 /\ step_inst fuel C inst s = OK u /\
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
  `opaque_use_ok fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  irule ricf_execution_point_ordinary >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all ricf_execution_sha3_operands_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED

Theorem ricf_execution_point_log:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  o1_fn_shape C fn /\ EVERY wf_ssa C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = LOG /\ step_inst fuel C inst s = OK u /\
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
  `opaque_use_ok fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  `fn_inst_wf fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `?tc rest. inst.inst_operands = Lit tc :: rest /\ LENGTH rest = w2n tc + 2` by
    gvs[inst_wf_def] >>
  `?addr tail. REVERSE rest = addr::tail` by
    (Cases_on `REVERSE rest` >> fs[] >> metis_tac[]) >>
  `LENGTH tail = w2n tc + 1` by
    (qpat_assum `REVERSE rest = _`
       (assume_tac o REWRITE_RULE [LENGTH_REVERSE, LENGTH] o
         AP_TERM ``LENGTH:operand list -> num``) >> decide_tac) >>
  `?sizeop tops. tail = sizeop::tops` by
    (Cases_on `tail` >> fs[] >> metis_tac[]) >>
  `rest = REVERSE (addr::sizeop::tops)` by metis_tac[REVERSE_REVERSE] >>
  `inst.inst_operands = Lit tc :: REVERSE (addr::sizeop::tops)` by simp[] >>
  irule ricf_execution_point_ordinary >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all ricf_execution_log_operands_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED

Theorem ricf_execution_point_bump:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  o1_fn_shape C fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  inst.inst_opcode = BUMP /\ step_inst fuel C inst s = OK u /\
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
  `opaque_use_ok fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  irule ricf_execution_point_ordinary >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all ricf_execution_bump_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED
