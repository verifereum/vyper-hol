Theory dftOriginalCutLifecycle
Ancestors
  dftOriginalScheduleRuntime dftProtectedRuntime dftOccurrenceAvailability
  dftOccurrenceMachine dftOpenMachine venomExecSemantics venomWf venomInst
  sccpCorrectnessProofs

Theorem dft_original_cut_phis_entry:
  dft_original_block f b q /\ q.bb_label = s.vs_current_bb /\
  strict_dom_vars_defined f s /\ eval_phis s q.bb_instructions = OK sp ==>
  dft_original_cut f b q
    (sp with vs_inst_idx := phi_prefix_length q.bb_instructions)
Proof
  strip_tac >> simp[dft_original_cut_def] >> conj_tac
  >- fs[dft_original_block_def] >>
  irule dft_activation_cut_phis >> goal_assum drule >> simp[]
QED

Theorem dft_original_cut_advance:
  dft_original_cut f b q s /\ get_instruction q s.vs_inst_idx = SOME inst /\
  t.vs_inst_idx = SUC s.vs_inst_idx /\ t.vs_current_bb = s.vs_current_bb /\
  FDOM t.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs ==>
  dft_original_cut f b q t
Proof
  strip_tac >> fs[dft_original_cut_def] >>
  irule dft_activation_cut_advance >> goal_assum drule >> simp[]
QED

Theorem dft_original_cut_nonphi:
  dft_original_cut f b q s /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) stack n /\
  get_instruction q s.vs_inst_idx = SOME inst /\ inst_wf inst /\
  inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 q t) stack' n' ==>
  dft_original_cut f b q t
Proof
  strip_tac >> drule_all dft_occ_nonphi_fdom >> strip_tac >>
  drule_all dft_occ_ordinary_control >> strip_tac >>
  irule dft_original_cut_advance >> goal_assum drule >> simp[] >> metis_tac[]
QED

Theorem dft_original_cut_return:
  dft_original_cut f b q caller /\
  get_instruction q caller.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE /\
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fn 0 q inst caller::stack) n /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 q t) stack' n' ==>
  dft_original_cut f b q t
Proof
  strip_tac >> drule_all dft_occ_return_fdom >> strip_tac >>
  drule_all dft_occ_return_control >> strip_tac >>
  irule dft_original_cut_advance >> goal_assum drule >> simp[] >> metis_tac[]
QED

Theorem dft_original_root_dom:
  dft_original_function f g /\ fn_entry_label g = SOME s.vs_current_bb ==>
  strict_dom_vars_defined f s
Proof
  strip_tac >> irule strict_dom_vars_defined_entry >>
  metis_tac[dft_original_function_entry]
QED

Theorem dft_original_callee_dom:
  dft_original_function f g /\ setup_callee g args caller = SOME cs ==>
  strict_dom_vars_defined f cs
Proof
  strip_tac >> irule dft_original_root_dom >> goal_assum (drule_at Any) >>
  gvs[setup_callee_def, fn_entry_label_def, entry_block_def, AllCaseEqs()]
QED
