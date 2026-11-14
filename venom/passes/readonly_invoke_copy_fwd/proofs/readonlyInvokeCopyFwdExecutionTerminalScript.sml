Theory readonlyInvokeCopyFwdExecutionTerminal
Ancestors
  readonlyInvokeCopyFwdExecutionPointLocal readonlyInvokeCopyFwdExecutionAbortTransfer
  readonlyInvokeCopyFwdExecutionControl
  readonlyInvokeCopyFwdExecutionHalt readonlyInvokeCopyFwdExecutionSelfdestruct
  readonlyInvokeCopyFwdExecutionAssembly readonlyInvokeCopyFwdExecutionSteps
  readonlyInvokeCopyFwdExecutionBoundary readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdHeterogeneousLedger
  o1LowerDloadOccurrence o1LowerDloadPtrDiscipline o1LowerDloadGhost
  ptrDiscipline reachableNonhalted venomStepProps o1PassContract unitShapeDefs
  allocaFrontierBound reachableFnSim
  contextCodegenRel opcodeClass passSimulationDefs
  venomExecSemantics venomExecProofs venomExecProps venomInstProofs
  venomWf venomState venomInst finite_map list pred_set

Theorem ricf_execution_noninvoke_terminal:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~vs.vs_halted /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ mem_inv raw_mem_ok C vs /\ taint_within D C vs /\
  ricf_function_edit fn (mid_of fn) /\ ricf_inst_edit inst ti /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\
  terminates (step_inst fuel C inst s) /\
  (!u. step_inst fuel C inst s = OK u ==> is_terminator inst.inst_opcode) ==>
  ?m. block_step_rel D vs C
    (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    stk PG fn (step_inst fuel C inst s) (step_inst m Ct ti t)
Proof
  strip_tac >>
  qpat_assum `ricf_execution_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_execution_point_def]) >>
  `active_inst fn inst s` by
    (fs[active_inst_def, get_instruction_def] >>
     qexists_tac `bb` >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions` by metis_tac[frame_reachable_prov_support] >>
  `o1_fn_shape C fn /\ wf_function fn /\ fn_inst_wf fn /\
   ssa_form fn /\ opaque_use_ok fn /\
   EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM,
       wf_ssa_def] >> metis_tac[]) >>
  `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
  `inst.inst_opcode <> RETFMP /\ inst.inst_opcode <> DRET /\
   inst.inst_opcode <> DJMP` by
    (fs[EVERY_MEM, fn_ptr_ok_def, o1_fn_shape_def, fn_shape_ok_def,
       inst_shape_ok_def] >> metis_tac[]) >>
  `inst.inst_opcode <> MCOPY` by
    (strip_tac >>
     qpat_x_assum `terminates (step_inst fuel C inst s)` mp_tac >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
       AllCaseEqs(), terminates_def, is_terminator_def] >>
     rpt CASE_TAC >> gvs[] >> metis_tac[]) >>
  `ti = inst` by fs[ricf_inst_edit_def] >> gvs[] >>
  Cases_on `step_inst fuel C inst s` >> gvs[terminates_def]
  >~ [`step_inst fuel C inst s = OK u`] >- suspend "jump"
  >~ [`step_inst fuel C inst s = Halt sh`] >- suspend "halt"
  >~ [`step_inst fuel C inst s = IntRet ret se`] >- suspend "return" >>
  rename1 `step_inst fuel C inst s = Abort reason se` >>
  drule_all ricf_execution_noninvoke_abort >>
  disch_then (qspec_then `Ct` strip_assume_tac) >>
  qexists_tac `fuel` >> simp[block_step_rel_def, fn_run_rel_def, dead_result_rel_def]
QED

Resume ricf_execution_noninvoke_terminal[jump]:
  `inst_wf inst` by
    (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[EL_MEM]) >>
  `is_terminator inst.inst_opcode` by metis_tac[] >>
  `MEM inst.inst_opcode [JMP;JNZ]` by
    (simp[MEM] >> metis_tac[step_inst_ok_terminator_jump]) >>
  `~u.vs_halted` by metis_tac[frame_reachable_not_halted, step_inst_ok_halted] >>
  Cases_on `inst.inst_opcode = JMP`
  >- (`?lbl. inst.inst_operands = [Label lbl]` by gvs[inst_wf_def] >>
      drule_all ricf_execution_point_jmp >>
      disch_then (qspec_then `Ct` strip_assume_tac) >>
      qexists_tac `fuel` >> gvs[]) >>
  `inst.inst_opcode = JNZ` by fs[MEM] >>
  `?cond l1 l2. inst.inst_operands = [cond;Label l1;Label l2]` by
    gvs[inst_wf_def] >>
  drule_all ricf_execution_point_jnz >>
  disch_then (qspec_then `Ct` strip_assume_tac) >>
  qexists_tac `fuel` >> gvs[]
QED

Resume ricf_execution_noninvoke_terminal[halt]:
  `MEM inst.inst_opcode [STOP;SINK;SELFDESTRUCT;RETURN]` by
    (simp[MEM] >> metis_tac[step_inst_halt_opcodes]) >>
  Cases_on `MEM inst.inst_opcode [STOP;SINK]`
  >- (drule_all ricf_execution_stop_sink >>
      disch_then (qspec_then `Ct` strip_assume_tac) >>
      qexists_tac `fuel` >> simp[block_step_rel_def, fn_run_rel_def]) >>
  Cases_on `inst.inst_opcode = SELFDESTRUCT`
  >- (drule_all ricf_execution_selfdestruct_halt >>
      disch_then (qspec_then `Ct` strip_assume_tac) >>
      qexists_tac `fuel` >> simp[block_step_rel_def, fn_run_rel_def]) >>
  `inst.inst_opcode = RETURN` by fs[MEM] >>
  `~in_revert_forward fn s` by
    (strip_tac >> fs[in_revert_forward_def, revert_forward_at_def,
       revert_forward_pair_def] >> gvs[]) >>
  drule_all ricf_execution_return_result >>
  disch_then (qspec_then `Ct` strip_assume_tac) >>
  qexists_tac `fuel` >> simp[block_step_rel_def, fn_run_rel_def]
QED

Resume ricf_execution_noninvoke_terminal[return]:
  `inst.inst_opcode = RET` by
    (qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
     simp[step_inst_non_invoke] >> strip_tac >>
     drule step_inst_base_intret_opcodes >> simp[]) >>
  `active_inst (mid_of fn) inst t` by
    (drule_all ricf_execution_raw_block >> strip_tac >>
     drule_all ricf_block_edit_fetch >> strip_tac >>
     `ti = inst` by (fs[ricf_inst_edit_def] >> gvs[]) >>
     drule ricf_execution_point_control >> strip_tac >>
     simp[active_inst_def] >> qexists_tac `tb` >>
     fs[get_instruction_def] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  drule_all ricf_execution_point_ret_step >>
  disch_then (qspec_then `Ct` strip_assume_tac) >>
  qexists_tac `fuel` >> gvs[]
QED

Finalise ricf_execution_noninvoke_terminal
