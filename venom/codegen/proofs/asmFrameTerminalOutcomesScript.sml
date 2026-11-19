Theory asmFrameTerminalOutcomes
Ancestors
  asmFrameRun asmFrameRel asmSem asmWf symbolResolve frameStep frameObsStep
  callTrace vfmExecution extCallOracle list

Theorem asm_frame_terminal_no_unread_outcomes:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
  a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
  (asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL a.as_pc prog) a = AsmHalt b \/
   asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL a.as_pc prog) a = AsmRevert b \/
   asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL a.as_pc prog) a = AsmFault b) ==>
  a.as_outcomes = []
Proof
  strip_tac >>
  `frame_last es` by (drule_all asm_frame_step >> simp[] >> metis_tac[]) >>
  `call_trace es = []` by
    (Cases_on `step es` >> rename1 `step es = (result,succ)` >>
     Cases_on `result` >> gvs[frame_last_def] >>
     drule frame_obs_terminal >> simp[]) >>
  gvs[asm_frame_rel_def]
QED

Theorem asm_primitives_terminal_outcomes[local]:
  !f. MEM f [asm_binop bin; asm_unop un; asm_ternop tern;
             asm_push_val v; asm_pop; asm_dup n; asm_swap n;
             asm_mload; asm_mstore; asm_mstore8; asm_sload; asm_sstore;
             asm_tload; asm_tstore; asm_jump pc; asm_jumpi pc;
             asm_return_op; asm_revert_op; asm_log n; asm_sha3;
             asm_copy_to_mem bytes; asm_returndatacopy; asm_extcodecopy;
             asm_mcopy; asm_selfdestruct; asm_exec_call static;
             asm_exec_staticcall; asm_exec_delegatecall;
             asm_exec_create; asm_exec_create2] ==>
  (f a = AsmHalt b \/ f a = AsmRevert b \/ f a = AsmFault b) ==>
  b.as_outcomes = a.as_outcomes
Proof
  rw[MEM] >>
  gvs[asm_binop_def, asm_unop_def, asm_ternop_def, asm_push_val_def,
       asm_pop_def, asm_dup_def, asm_swap_def, asm_next_def,
       asm_mload_def, asm_mstore_def, asm_mstore8_def, asm_sload_def,
       asm_sstore_def, asm_tload_def, asm_tstore_def, asm_jump_def,
       asm_jumpi_def, asm_return_op_def, asm_revert_op_def, asm_log_def,
       asm_sha3_def, asm_copy_to_mem_def, asm_returndatacopy_def,
       asm_extcodecopy_def, asm_mcopy_def, asm_selfdestruct_def,
       asm_exec_call_def, asm_exec_staticcall_def, asm_exec_delegatecall_def,
       asm_exec_create_def, asm_exec_create2_def, asm_call_request_def,
       asm_create_request_def, asm_consume_call_outcome_def,
       asm_consume_create_outcome_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem asm_groups_terminal_outcomes[local]:
  !step. MEM step [asm_step_arith; asm_step_compare; asm_step_bitwise;
                  asm_step_memory; asm_step_control pc; asm_step_copy;
                  asm_step_extcall] ==>
  (step name a = SOME (AsmHalt b) \/
   step name a = SOME (AsmRevert b) \/
   step name a = SOME (AsmFault b)) ==>
  b.as_outcomes = a.as_outcomes
Proof
  rw[MEM] >>
  gvs[asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
      asm_step_memory_def, asm_step_control_def, asm_step_copy_def,
      asm_step_extcall_def, AllCaseEqs()] >>
  irule asm_primitives_terminal_outcomes >> simp[MEM] >> metis_tac[]
QED

Theorem asm_context_not_terminal[local]:
  asm_step_context name a <> SOME (AsmHalt b) /\
  asm_step_context name a <> SOME (AsmRevert b) /\
  asm_step_context name a <> SOME (AsmFault b)
Proof
  rw[asm_step_context_def] >>
  gvs[asm_push_val_def, asm_next_def, asm_state_unop_def, asm_gas_def,
      AllCaseEqs()]
QED

Theorem asm_op_terminal_outcomes[local]:
  (asm_step_op pc name a = AsmHalt b \/
   asm_step_op pc name a = AsmRevert b \/
   asm_step_op pc name a = AsmFault b) ==>
  b.as_outcomes = a.as_outcomes
Proof
  mp_tac asm_groups_terminal_outcomes >>
  simp[MEM, DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
  simp[asm_step_op_def] >>
  Cases_on `asm_step_arith name a` >> simp[]
  >- (Cases_on `asm_step_compare name a` >> simp[]
      >- (Cases_on `asm_step_bitwise name a` >> simp[]
          >- (Cases_on `asm_step_memory name a` >> simp[]
              >- (Cases_on `asm_step_control pc name a` >> simp[]
                  >- (Cases_on `asm_step_extcall name a` >> simp[]
                      >- (Cases_on `asm_step_copy name a` >> simp[]
                          >- (Cases_on `asm_step_context name a` >> simp[]
                              >- (Cases_on `ALOOKUP dup_table name` >> simp[]
                                  >- (Cases_on `ALOOKUP swap_table name` >> simp[]
                                      >- (Cases_on `ALOOKUP log_table name` >> simp[] >>
                                          gvs[asm_log_def, asm_dup_def, asm_swap_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
                                      gvs[asm_log_def, asm_dup_def, asm_swap_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
                                  gvs[asm_log_def, asm_dup_def, asm_swap_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
                              metis_tac[asm_context_not_terminal]) >> metis_tac[]) >>
                      metis_tac[]) >> metis_tac[]) >> metis_tac[]) >> metis_tac[]) >>
      metis_tac[]) >> metis_tac[]
QED

Theorem asm_step_terminal_outcomes:
  (asm_step labels pc inst a = AsmHalt b \/
   asm_step labels pc inst a = AsmRevert b \/
   asm_step labels pc inst a = AsmFault b) ==>
  b.as_outcomes = a.as_outcomes
Proof
  Cases_on `inst` >> simp[asm_step_def]
  >- metis_tac[asm_op_terminal_outcomes] >>
  rpt CASE_TAC >> simp[]
QED

Theorem asm_frame_run_terminal_outcomes:
  !n prog data es0 a es r final b.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
    run_call es = SOME (r,final) /\ ~frame_resource_starved es0 r final /\
    (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n a = AsmHalt b \/
     asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n a = AsmRevert b \/
     asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n a = AsmFault b) ==>
    b.as_outcomes = []
Proof
  Induct >- simp[asm_steps_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `a.as_pc < LENGTH prog` by (spose_not_then assume_tac >> gvs[asm_steps_def]) >>
  `~is_data_inst (EL a.as_pc prog)` by
    (spose_not_then assume_tac >> Cases_on `EL a.as_pc prog` >>
     gvs[is_data_inst_def, asm_steps_def, asm_step_def]) >>
  Cases_on `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
              (EL a.as_pc prog) a`
  >- (rename1 `asm_step _ _ _ a = AsmOK a1` >>
      `asm_frame_rel_tail [] prog data es0 a es` by simp[asm_frame_rel_tail_nil] >>
      `asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
         prog (SUC 0) a = AsmOK a1` by simp[asm_steps_def] >>
      drule_all asm_frame_prefix_tail >> rewrite_tac[asm_frame_rel_tail_nil] >>
      strip_tac >> gvs[asm_steps_def] >> first_x_assum irule >> metis_tac[]) >>
  gvs[asm_steps_def] >>
  metis_tac[asm_frame_terminal_no_unread_outcomes, asm_step_terminal_outcomes]
QED
