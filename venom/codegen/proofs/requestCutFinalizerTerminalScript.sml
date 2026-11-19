Theory requestCutFinalizerTerminal
Ancestors
  codegenAsmOpt asmOptFinalizerCorrect finalizerContract asmSymBridge
  asmFrameTerminalOutcomes codegenRequestPrefix
  asmFrameRel asmDataEnv asmOptimizer asmSem asmSymSem
  vfmExecution callTrace contextCodegenRel list rich_list

Theorem asm_finalizer_terminal_oracle:
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  asm_frame_prog_ok prog' /\
  s.as_pc = 0 /\ s.as_code = assemble prog ++ data /\
  (fin = asm_opt_finalizer ==>
    label_disciplined (asm_data_env prog (assemble prog ++ data)) prog s) /\
  asm_frame_rel_tail [] prog' data es
    (s with as_code := assemble prog' ++ data) es /\
  run_call es = SOME (r,final) /\ ~frame_resource_starved es r final /\
  (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     prog n s = AsmHalt a \/
   asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     prog n s = AsmRevert a \/
   asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     prog n s = AsmFault a) ==>
  a.as_outcomes = [] /\ call_requests es <<= a.as_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `fin = asm_opt_finalizer`
  >- (gvs[] >>
      `asm_refines prog prog'` by
        metis_tac[asm_opt_finalizer_meets_contract, finalizer_correct_def] >>
      `sym_terminal (asm_result_sym
        (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
          prog n s))` by metis_tac[asm_result_sym_def, sym_terminal_def] >>
      drule_all asm_opt_transfer >> disch_then (qx_choose_then `n'` assume_tac) >>
      Cases_on `asm_steps (SND (compute_label_offsets prog'))
        (build_offset_to_pc prog') prog' n' (s with as_code := assemble prog' ++ data)` >>
      gvs[asm_result_sym_def, sym_result_rel_def, sym_obs_def, sym_init_def,
          asm_frame_rel_tail_nil, asm_state_component_equality] >>
      metis_tac[asm_frame_run_terminal_outcomes, asm_frame_run_requests]) >>
  `fin = K SOME` by fs[accepted_finalizers_def] >>
  `s with as_code := assemble prog ++ data = s` by simp[asm_state_component_equality] >>
  gvs[asm_frame_rel_tail_nil] >> metis_tac[asm_frame_run_terminal_outcomes, asm_frame_run_requests]
QED
