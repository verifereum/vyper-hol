Theory dftOccurrenceAvailability
Ancestors
  dftOccurrenceReplay dftOccurrenceMachine dftOpenErase dftOpenMachine
  venomExecProps venomExecSemantics venomState venomInst finite_map list

Theorem dft_occ_ordinary_fdom:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst_wf inst /\
  ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 bb t) stack' n'
  ==> FDOM t.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs
Proof
  strip_tac >>
  qpat_x_assum `(dft_occ_oracle_next _ _ _).dft_occ_core = _` mp_tac >>
  simp[dft_occ_oracle_next_def, dft_next_inf_def, dft_erase_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def] >>
  Cases_on `inst.inst_opcode = GAS`
  >- (simp[] >> Cases_on `inst.inst_outputs` >>
      simp[dft_fill_def, dft_fill_control_def] >>
      rename1 `inst.inst_outputs = h::outs` >> Cases_on `outs` >> simp[dft_open_deliver_def, dft_open_continue_def,
        dft_fill_def, dft_fill_control_def, update_var_def] >>
      rpt strip_tac >> gvs[] >> simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  simp[] >> Cases_on `step_inst_base inst s` >>
  simp[dft_open_deliver_def, dft_open_continue_def, dft_fill_def,
       dft_fill_control_def] >> rpt strip_tac >> gvs[] >>
  irule step_inst_base_fdom >> simp[] >>
  metis_tac[is_pseudo_def]
QED

Theorem dft_occ_return_fdom:
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fn 0 bb inst caller::stack) n /\
  inst.inst_opcode = INVOKE /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 bb t) stack' n'
  ==> FDOM t.vs_vars = FDOM caller.vs_vars UNION set inst.inst_outputs
Proof
  strip_tac >>
  qpat_x_assum `(dft_occ_oracle_next _ _ _).dft_occ_core = _` mp_tac >>
  simp[dft_occ_oracle_next_def, dft_next_inf_def, dft_erase_def,
       dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
       dft_open_next_def, dft_open_return_def] >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  simp[dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
       dft_fill_def, dft_fill_control_def] >> strip_tac >> gvs[] >>
  drule bind_outputs_fdom >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED
