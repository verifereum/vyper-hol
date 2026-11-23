Theory requestCutStoppedTerminal
Ancestors
  requestCutOrdinaryAbort requestCutOrdinaryHalt requestCutTerminalPrefix fnFrameSymbolicPrefix
  fnFramePrefixDriver frameJointTransition codegenEntryRel asmFrameRel
  asmOptimizer asmDataEnv asmSem asmSymSem contextCodegenRel o1PassContract
  unitShapeDefs venomExecSemantics venomState venomInst
  vfmExecution list codegenSymRel codegenSymbolicTerminalOwn finalizerContractOwn
  fnPlanPlaceRevertPostamble asmRelocDataEnv

Theorem request_cut_stopped_terminal_crossed_own:
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  asm_frame_prog_ok prog' /\ vs0.vs_code = assemble prog' ++ vs0.vs_data_section /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es
    (entry_asm_state vs0 es) es /\
  run_call es = SOME (result,final) /\ ~frame_resource_starved es result final /\
  asm_steps (lo_reloc prog prog') (build_offset_to_pc prog)
    prog n (entry_asm_state vs0 es) = AsmOK ast /\
  q9 = JointConfig stk PG G tn fn9 inst9 s9 oms om hs hist /\
  (fin = K SOME ==> normal_frame_plan rp unit cpl prog planner_base es q9 ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps_mode T prog (asm_data_env prog' vs0.vs_code) vs0.vs_code n
      (sym_init (entry_asm_state vs0 es)) = SymOK ss /\
    normal_frame_symbolic_plan_own T (lo_reloc prog prog')
      (asm_data_env prog' vs0.vs_code) vs0.vs_code rp unit cpl prog vs0 es q9 ast ss /\
    focus_s7_symbolic_context_own T unit prog /\
    asm_data_env_lo_ok (lo_reloc prog prog') prog (asm_data_env prog' vs0.vs_code)
      vs0.vs_code) /\
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
  `code_labels_agree prog (lo_reloc prog prog')` by simp[lo_reloc_code_labels_agree] >>
  `(?steps out.
    (asm_steps (lo_reloc prog prog') (build_offset_to_pc prog)
       prog steps ast = AsmHalt out \/
     asm_steps (lo_reloc prog prog') (build_offset_to_pc prog)
       prog steps ast = AsmRevert out \/
     asm_steps (lo_reloc prog prog') (build_offset_to_pc prog)
       prog steps ast = AsmFault out) /\
    out.as_requests = s9.vs_requests) /\
   (fin = asm_opt_finalizer ==>
     asm_static_wf prog /\
     asm_data_env_lo_ok (lo_reloc prog prog') prog (asm_data_env prog' vs0.vs_code)
       vs0.vs_code /\
     label_disciplined_own (asm_data_env prog' vs0.vs_code) vs0.vs_code
       prog (entry_asm_state vs0 es))` by
    (Cases_on `fin = asm_opt_finalizer`
     >- (fs[] >>
         `asm_static_wf prog` by fs[focus_s7_symbolic_context_own_def] >>
         `?steps out.
            (asm_steps (lo_reloc prog prog') (build_offset_to_pc prog)
               prog steps ast = AsmHalt out \/
             asm_steps (lo_reloc prog prog') (build_offset_to_pc prog)
               prog steps ast = AsmRevert out \/
             asm_steps (lo_reloc prog prog') (build_offset_to_pc prog)
               prog steps ast = AsmFault out) /\
            out.as_requests = s9.vs_requests /\
            sym_terminal (sym_steps_mode T prog (asm_data_env prog' vs0.vs_code)
              vs0.vs_code steps ss)` by
           (FIRST
              [drule_all_then strip_assume_tac request_cut_symbolic_normal_halt_terminal_own,
               drule_all_then strip_assume_tac request_cut_symbolic_normal_abort_terminal_own] >>
            metis_tac[]) >>
         `sym_terminal (sym_steps_mode T prog (asm_data_env prog' vs0.vs_code)
           vs0.vs_code (n + steps) (sym_init (entry_asm_state vs0 es)))` by
           (qpat_assum `sym_steps_mode T prog _ _ n _ = SymOK ss`
              (fn prefix => simp_tac bool_ss [sym_steps_mode_add, prefix, sym_result_case_def]) >>
            first_assum ACCEPT_TAC) >>
         drule_all sym_steps_mode_terminal_disciplined >> simp[] >> metis_tac[]) >>
     `fin = K SOME` by fs[accepted_finalizers_def] >>
     gvs[combinTheory.K_THM, lo_reloc_refl] >>
     FIRST [drule_all_then strip_assume_tac request_cut_normal_halt_terminal,
            drule_all_then strip_assume_tac request_cut_normal_abort_terminal] >>
     metis_tac[]) >>
  rename1 `asm_steps _ _ prog steps ast = _` >>
  mp_tac (Q.INST [`t` |-> `s9`, `m` |-> `steps`]
    request_cut_terminal_prefix_crossed_own) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  simp[]
QED
