Theory dftIndexedOriginalRuntime
Ancestors
  dftOriginalRuntime dftOriginalCutLifecycle dftOriginalScheduleRuntime
  dftProtectedRuntime dftOccurrenceAvailability dftOccurrenceMachine
  dftOpenMachine venomExecSemantics venomExecProofs venomWf venomInst venomState list

Definition dft_all_original_control_def:
  (dft_all_original_control (DftEnter fn k s) <=>
    k = 0 /\ (!f. dft_original_function f fn ==>
      fn_reachable f s.vs_current_bb /\ strict_dom_vars_defined f s)) /\
  (dft_all_original_control (DftAt fn k q s) <=>
    k = 0 /\ MEM q fn.fn_blocks /\
    (!f. dft_original_function f fn ==>
      fn_reachable f s.vs_current_bb /\
      (!b. dft_original_block f b q ==> dft_original_cut f b q s))) /\
  (dft_all_original_control (DftDone r) <=> T)
End

Definition dft_all_original_frame_def:
  dft_all_original_frame (DftCaller fn k q inst s) <=>
    dft_all_original_control (DftAt fn k q s) /\
    get_instruction q s.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE
End

Definition dft_all_original_core_def:
  dft_all_original_core (DftOpen ctl stack n) <=>
    dft_all_original_control ctl /\ EVERY dft_all_original_frame stack
End

Definition dft_all_original_ready_def:
  dft_all_original_ready c <=> dft_all_original_core c.dft_occ_core
End

Theorem dft_all_original_root:
  fn_entry_label fn = SOME s.vs_current_bb ==>
  dft_all_original_ready (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
Proof
  simp[dft_all_original_ready_def, dft_occ_init_def,
       dft_all_original_core_def, dft_all_original_control_def] >>
  rpt strip_tac
  >- (drule dft_original_function_entry >>
      simp[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]) >>
  metis_tac[dft_original_root_dom]
QED

Theorem dft_all_original_entry_cut:
  dft_all_original_control (DftEnter fn 0 s) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME q /\
  eval_phis s q.bb_instructions = OK sp ==>
  dft_all_original_control (DftAt fn 0 q
    (sp with vs_inst_idx := phi_prefix_length q.bb_instructions))
Proof
  simp[dft_all_original_control_def] >> strip_tac >>
  `MEM q fn.fn_blocks /\ q.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  simp[] >> rpt strip_tac
  >- (drule_all dft_original_function_lookup_block >> strip_tac >>
      `dft_original_cut f b q
        (sp with vs_inst_idx := phi_prefix_length q.bb_instructions)` by
        metis_tac[dft_original_cut_phis_entry] >>
      fs[dft_original_cut_def, dft_activation_cut_def] >> metis_tac[]) >>
  metis_tac[dft_original_cut_phis_entry]
QED

Theorem dft_all_original_return_cut:
  dft_all_original_frame (DftCaller fn 0 q inst caller) /\
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fn 0 q inst caller::stack) n /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 q t) stack' n' ==>
  dft_all_original_control (DftAt fn 0 q t)
Proof
  simp[dft_all_original_frame_def, dft_all_original_control_def] >>
  strip_tac >> simp[] >> rpt strip_tac
  >- (drule_all dft_occ_return_control >> simp[]) >>
  metis_tac[dft_original_cut_return]
QED
