Theory requestCutFinalizerTerminal
Ancestors
  codegenAsmOpt asmOptFinalizerCorrect finalizerContract asmSymBridge
  asmFrameTerminalOutcomes codegenRequestPrefix
  asmFrameRel asmDataEnv asmOptimizer asmSem asmSymSem
  asmRelocDataEnv asmOptFinalizerOwn finalizerContractOwn
  fnPlanPlaceRevertPostamble
  vfmExecution callTrace contextCodegenRel list rich_list

Theorem asm_finalizer_terminal_oracle_own:
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  asm_frame_prog_ok prog' /\
  s.as_pc = 0 /\ s.as_code = assemble prog' ++ data /\
  (fin = asm_opt_finalizer ==>
    asm_static_wf prog /\
    asm_data_env_lo_ok (lo_reloc prog prog') prog (asm_data_env prog' s.as_code) s.as_code /\
    label_disciplined_own (asm_data_env prog' s.as_code) s.as_code prog s) /\
  asm_frame_rel_tail [] prog' data es s es /\
  run_call es = SOME (r,final) /\ ~frame_resource_starved es r final /\
  (asm_steps (lo_reloc prog prog') (build_offset_to_pc prog) prog n s = AsmHalt a \/
   asm_steps (lo_reloc prog prog') (build_offset_to_pc prog) prog n s = AsmRevert a \/
   asm_steps (lo_reloc prog prog') (build_offset_to_pc prog) prog n s = AsmFault a) ==>
  a.as_outcomes = [] /\ call_requests es <<= a.as_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `fin = asm_opt_finalizer`
  >- (gvs[] >>
      drule asm_opt_finalizer_refines_own >> strip_tac >>
      `sym_terminal (asm_result_sym
        (asm_steps (lo_reloc prog prog') (build_offset_to_pc prog) prog n s))` by
        metis_tac[asm_result_sym_def, sym_terminal_def] >>
      mp_tac (Q.INST [`lo` |-> `lo_reloc prog prog'`,
        `env` |-> `asm_data_env prog' s.as_code`] asm_opt_transfer_own_terminal) >>
      (impl_tac >- simp[lo_reloc_code_labels_agree, asm_data_env_ok_asm_data_env]) >>
      disch_then (qx_choose_then `n'` assume_tac) >>
      Cases_on `asm_steps (SND (compute_label_offsets prog'))
        (build_offset_to_pc prog') prog' n' s` >>
      gvs[asm_result_sym_def, sym_result_rel_def, sym_obs_def, sym_init_def,
          asm_frame_rel_tail_nil, asm_state_component_equality] >>
      metis_tac[asm_frame_run_terminal_outcomes, asm_frame_run_requests]) >>
  `fin = K SOME` by fs[accepted_finalizers_def] >>
  gvs[combinTheory.K_THM, lo_reloc_refl, asm_frame_rel_tail_nil] >>
  metis_tac[asm_frame_run_terminal_outcomes, asm_frame_run_requests]
QED
