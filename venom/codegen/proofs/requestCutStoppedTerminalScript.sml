Theory requestCutStoppedTerminal
Ancestors
  requestCutOrdinaryAbort requestCutOrdinaryHalt requestCutTerminalPrefix fnFrameSymbolicPrefix
  fnFramePrefixDriver frameJointTransition codegenEntryRel asmFrameRel
  asmOptimizer asmDataEnv asmSem asmSymSem contextCodegenRel o1PassContract
  unitShapeDefs venomExecSemantics venomState venomInst
  vfmExecution list

Theorem request_cut_stopped_terminal_crossed:
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  asm_frame_prog_ok prog' /\ vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es
    (entry_asm_state vs0 es with as_code := assemble prog' ++ vs0.vs_data_section) es /\
  run_call es = SOME (result,final) /\ ~frame_resource_starved es result final /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog n (entry_asm_state vs0 es) = AsmOK ast /\
  q9 = JointConfig stk PG G tn fn9 inst9 s9 oms om hs hist /\
  (fin = K SOME ==> normal_frame_plan rp unit cpl prog planner_base es q9 ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog (asm_data_env prog vs0.vs_code) n
      (sym_init (entry_asm_state vs0 es)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code)
      rp unit cpl prog vs0 es q9 ast ss /\ focus_s7_symbolic_context unit prog) /\
  active_inst fn9 inst9 s9 /\ inst9.inst_opcode <> INVOKE /\
  source_memory_reads_disjoint cpl inst9 s9 /\
  context_source_memory_writes_disjoint cpl inst9 s9 /\
  (step_inst m unit.cu_context inst9 s9 = Halt post9 \/
   ?ab. step_inst m unit.cu_context inst9 s9 = Abort ab post9) /\
  raw_variant fmp vs vs0 /\ raw_reachable vs C fn inst s /\
  inst.inst_opcode <> INVOKE /\ LENGTH s.vs_requests = k /\
  step_inst fuel C inst s = OK post /\ k < LENGTH post.vs_requests ==>
  k < LENGTH s9.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `q9 = _` SUBST_ALL_TAC >>
  `(?steps out.
    (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog steps ast = AsmHalt out \/
     asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog steps ast = AsmRevert out \/
     asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog steps ast = AsmFault out) /\
    out.as_requests = s9.vs_requests) /\
    (fin = asm_opt_finalizer ==>
      label_disciplined (asm_data_env prog (assemble prog ++ vs0.vs_data_section))
        prog (entry_asm_state vs0 es))` by
    (Cases_on `fin = asm_opt_finalizer`
     >- (Cases_on `step_inst m unit.cu_context inst9 s9 = Halt post9` >> fs[]
         >- (drule_all_then strip_assume_tac request_cut_symbolic_halt_prefix >>
             metis_tac[]) >>
         drule_all_then strip_assume_tac request_cut_symbolic_abort_prefix >>
         metis_tac[]) >>
     `fin = K SOME` by fs[accepted_finalizers_def] >>
     Cases_on `step_inst m unit.cu_context inst9 s9 = Halt post9` >> fs[]
     >- (drule_all_then strip_assume_tac request_cut_normal_halt_terminal >>
         metis_tac[]) >>
     drule_all_then strip_assume_tac request_cut_normal_abort_terminal >>
     metis_tac[]) >>
  rename1 `asm_steps _ _ prog steps ast = _` >>
  mp_tac (Q.INST [`t` |-> `s9`, `m` |-> `steps`]
    request_cut_terminal_prefix_crossed) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  simp[]
QED
