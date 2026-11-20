Theory requestCutStoppedAssert
Ancestors
  requestCutAssertCursor requestCutStoppedTerminal
  o1ContractCfgNormJointCursors jointRequestCut frameJointTrace
  frameRawProjection stepWriteFootprintBase
  fnFramePrefixDriver fnFrameSymbolicPrefix codegenEntryRel
  asmFrameRel asmOptimizer asmDataEnv asmSem asmSymSem contextCodegenRel codegenRel
  o1PassContract unitShapeDefs venomExecSemantics
  venomState venomInst venomWf asmIR vfmExecution list
  codegenSymRel fnPlanPlaceRevertPostamble asmRelocDataEnv

(* The selected walk already supplies the concrete and symbolic prefix.
   Extend that exact prefix by the assertion at its stopped cursor. *)
Theorem request_cut_joint_assert_terminal[local]:
  cfg_norm_joint_cursors C8 unit.cu_context (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  MEM inst8.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\
  step_inst m C8 inst8 s8 = Abort ab s8' /\
  EVERY wf_function unit.cu_context.ctx_functions /\
  joint_trace vs0 unit.cu_context q90 evs9 qs9
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ==>
  active_inst fn9 inst9 s9 /\ inst9.inst_opcode <> INVOKE /\
  source_memory_reads_disjoint cpl inst9 s9 /\
  context_source_memory_writes_disjoint cpl inst9 s9 /\
  (?a u. step_inst 0 unit.cu_context inst9 s9 = Abort a u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all cfg_norm_joint_assert_abort >> strip_tac >>
  `active_inst fn9 inst9 s9` by
    (drule joint_trace_reachable >> strip_tac >>
     metis_tac[joint_config_raw, raw_reachable_active]) >>
  `MEM inst9.inst_opcode [ASSERT; ASSERT_UNREACHABLE]` by metis_tac[] >>
  `inst9.inst_opcode <> INVOKE /\ source_memory_reads_disjoint cpl inst9 s9 /\
   context_source_memory_writes_disjoint cpl inst9 s9` by
    fs[source_memory_reads_disjoint_def, source_memory_read_ranges_def,
       context_source_memory_writes_disjoint_def, source_memory_write_ranges_def] >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem request_cut_stopped_assert_crossed_own:
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  asm_frame_prog_ok prog' /\ vs0.vs_code = assemble prog' ++ vs0.vs_data_section /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es
    (entry_asm_state vs0 es) es /\
  run_call es = SOME (result,final) /\ ~frame_resource_starved es result final /\
  asm_steps (lo_reloc prog prog') (build_offset_to_pc prog)
    prog n (entry_asm_state vs0 es) = AsmOK ast /\
  q9 = JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9 /\
  (fin = K SOME ==> normal_frame_plan rp unit cpl prog planner_base es q9 ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps_mode T prog (asm_data_env prog' vs0.vs_code) vs0.vs_code n
      (sym_init (entry_asm_state vs0 es)) = SymOK ss /\
    normal_frame_symbolic_plan_own T (lo_reloc prog prog')
      (asm_data_env prog' vs0.vs_code) vs0.vs_code rp unit cpl prog vs0 es q9 ast ss /\
    focus_s7_symbolic_context_own T unit prog /\
    asm_data_env_lo_ok (lo_reloc prog prog') prog (asm_data_env prog' vs0.vs_code)
      vs0.vs_code) /\
  cfg_norm_joint_cursors C8 unit.cu_context (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8) q9 /\
  MEM inst8.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\
  step_inst m C8 inst8 s8 = Abort ab s8' /\
  joint_trace vs0 unit.cu_context q90 evs9 qs9 q9 /\
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  raw_variant fmp vs vs0 /\ EVERY wf_function C.ctx_functions /\
  EVERY wf_function unit.cu_context.ctx_functions /\
  raw_reachable vs C fn inst s /\ inst.inst_opcode <> INVOKE /\
  LENGTH s.vs_requests = k /\ step_inst fuel C inst s = OK post /\
  k < LENGTH post.vs_requests ==>
  k < LENGTH s9.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `q9 = _` SUBST_ALL_TAC >>
  drule_all request_cut_joint_assert_terminal >>
  disch_then (qspec_then `cpl` (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`err`, `u`] assume_tac)))))) >>
  mp_tac (Q.INST [
    `q9` |-> `JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9`,
    `stk` |-> `stk9`, `PG` |-> `PG9`, `G` |-> `G9`, `tn` |-> `tn9`,
    `oms` |-> `oms9`, `om` |-> `om9`, `hs` |-> `hs9`, `hist` |-> `hist9`,
    `m` |-> `0`, `post9` |-> `u`] request_cut_stopped_terminal_crossed_own) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >>
  disch_then ACCEPT_TAC
QED
