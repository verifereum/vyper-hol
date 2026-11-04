Theory dftHiddenClock
Ancestors
  dftInaccessibleCaller dftPendingSuspension dftOpenHistory
  dftOccurrenceReplay dftOccurrenceMachine dftOpenErase dftOpenMachine
  venomExecSemantics list arithmetic

Theorem dft_clock_fill[local,simp]:
  dft_history_counter (dft_fill k c) = dft_history_counter c
Proof
  Cases_on `c` >> simp[dft_fill_def, dft_history_counter_def]
QED

Theorem dft_clock_invoke[local,simp]:
  dft_history_counter (dft_open_invoke C fn b bb inst s stack n) = n
Proof
  simp[dft_open_invoke_def] >>
  Cases_on `decode_invoke inst` >> simp[dft_history_counter_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 C.ctx_functions` >> simp[dft_history_counter_def] >>
  Cases_on `eval_operands x1 s` >> simp[dft_history_counter_def] >>
  rename1 `setup_callee callee args s` >>
  Cases_on `setup_callee callee args s` >> simp[dft_history_counter_def]
QED

(* Stack payload cannot influence the GAS clock, even on a failing restore. *)
Theorem dft_clock_next_stack[local]:
  dft_history_counter (dft_open_next a C (DftOpen ctl stackL n)) =
  dft_history_counter (dft_open_next a C (DftOpen ctl stackR n))
Proof
  Cases_on `ctl`
  >- (rename1 `DftEnter fn fuel s` >>
      simp[dft_open_next_def] >> Cases_on `fuel` >> simp[dft_history_counter_def] >>
      Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[dft_history_counter_def] >>
      rename1 `lookup_block _ _ = SOME bb` >>
      Cases_on `eval_phis s bb.bb_instructions` >> simp[dft_history_counter_def])
  >- (rename1 `DftAt fn fuel bb s` >> simp[dft_open_next_def] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[dft_history_counter_def] >>
      rename1 `get_instruction _ _ = SOME inst` >>
      Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
      Cases_on `inst.inst_opcode = GAS` >> simp[] >>
      Cases_on `inst.inst_outputs` >> simp[dft_history_counter_def] >>
      rename1 `inst.inst_outputs = out::outs` >>
      Cases_on `outs` >> simp[dft_history_counter_def]) >>
  simp[dft_open_next_def]
QED

Theorem dft_clock_occ_count[local]:
  dft_occ_count c = dft_history_counter c.dft_occ_core
Proof
  Cases_on `c.dft_occ_core` >> simp[dft_occ_count_def, dft_history_counter_def]
QED

Theorem dft_hidden_caller_next_count:
  dft_hidden_caller R fL fR tL tR savedL savedR path visit l r /\
  dft_occ_count l = dft_occ_count r ==>
  dft_occ_count (dft_occ_oracle_next w C l) =
  dft_occ_count (dft_occ_oracle_next w C r)
Proof
  strip_tac >>
  `dft_occ_address l = dft_occ_address r` by
    (drule dft_hidden_caller_address >> simp[]) >>
  gvs[dft_hidden_caller_def] >>
  `nL = nR` by gvs[dft_occ_count_def] >> gvs[] >>
  pure_rewrite_tac[dft_clock_occ_count, dft_occ_oracle_next_def,
                   dft_occ_next_projection] >>
  simp[dft_next_inf_def, dft_erase_def, dft_fill_def, dft_clock_next_stack]
QED

Theorem dft_pending_suspended_next_count:
  dft_pending_suspended us fL fR tL tR savedL savedR path visit l r /\
  dft_occ_count l = dft_occ_count r ==>
  dft_occ_count (dft_occ_oracle_next w C l) =
  dft_occ_count (dft_occ_oracle_next w C r)
Proof
  rewrite_tac[dft_pending_suspended_hidden] >>
  metis_tac[dft_hidden_caller_next_count]
QED
