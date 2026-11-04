Theory dftOccurrenceAvailability
Ancestors
  dftOccurrenceReplay dftOccurrenceMachine dftOpenErase dftOpenMachine
  venomExecProps venomExecProofs venomExecSemantics venomState venomInst finite_map list
  sccpCorrectnessProofs

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

Definition dft_activation_cut_def:
  dft_activation_cut fn bb s <=>
    bb.bb_label = s.vs_current_bb /\ strict_dom_vars_defined fn s /\
    (!d v. MEM d (TAKE s.vs_inst_idx bb.bb_instructions) /\
           MEM v d.inst_outputs ==> v IN FDOM s.vs_vars)
End

Theorem dft_activation_cut_phis:
  bb.bb_label = s.vs_current_bb /\ strict_dom_vars_defined fn s /\
  eval_phis s bb.bb_instructions = OK sp ==>
  dft_activation_cut fn bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  strip_tac >>
  drule eval_phis_vars_grow >> strip_tac >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (mp_tac o Q.AP_TERM `\st. st.vs_current_bb`) >>
  simp[] >> strip_tac >>
  simp[dft_activation_cut_def] >> conj_tac
  >- (gvs[strict_dom_vars_defined_def, pred_setTheory.SUBSET_DEF] >>
      metis_tac[]) >>
  metis_tac[eval_phis_outputs_in_fdom_mem]
QED

Theorem dft_activation_cut_prefix:
  dft_activation_cut fn bb s /\ bb.bb_instructions = pre ++ todo /\
  s.vs_inst_idx = LENGTH pre ==>
  (!d v. MEM d pre /\ MEM v d.inst_outputs ==> v IN FDOM s.vs_vars)
Proof
  strip_tac >> gvs[dft_activation_cut_def, TAKE_APPEND1]
QED

Theorem dft_occ_ordinary_control[local]:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 bb t) stack' n'
  ==> t.vs_inst_idx = SUC s.vs_inst_idx /\ t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  qpat_x_assum `(dft_occ_oracle_next _ _ _).dft_occ_core = _` mp_tac >>
  simp[dft_occ_oracle_next_def, dft_next_inf_def, dft_erase_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def] >>
  Cases_on `inst.inst_opcode = GAS`
  >- (simp[] >> Cases_on `inst.inst_outputs` >>
      simp[dft_fill_def, dft_fill_control_def] >>
      rename1 `inst.inst_outputs = h::outs` >> Cases_on `outs` >>
      simp[dft_open_deliver_def, dft_open_continue_def,
        dft_fill_def, dft_fill_control_def, update_var_def] >>
      rpt strip_tac >> gvs[]) >>
  simp[] >> Cases_on `step_inst_base inst s` >>
  simp[dft_open_deliver_def, dft_open_continue_def, dft_fill_def,
       dft_fill_control_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[venomInstProofs1Theory.step_inst_base_preserves_all]
QED

Theorem dft_foldl_update_current[local]:
  !kvs s. (FOLDL (\st (k,v). update_var k v st) s kvs).vs_current_bb =
    s.vs_current_bb
Proof
  Induct >> simp[] >> Cases >> simp[update_var_def]
QED

Theorem dft_bind_outputs_current[local]:
  bind_outputs outs vals s = SOME t ==> t.vs_current_bb = s.vs_current_bb
Proof
  rw[bind_outputs_def, AllCaseEqs()] >> simp[dft_foldl_update_current]
QED

Theorem dft_occ_return_control[local]:
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fn 0 bb inst caller::stack) n /\
  inst.inst_opcode = INVOKE /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 bb t) stack' n'
  ==> t.vs_inst_idx = SUC caller.vs_inst_idx /\
      t.vs_current_bb = caller.vs_current_bb
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
  drule dft_bind_outputs_current >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem dft_activation_cut_advance[local]:
  dft_activation_cut fn bb s /\ get_instruction bb s.vs_inst_idx = SOME inst /\
  t.vs_inst_idx = SUC s.vs_inst_idx /\ t.vs_current_bb = s.vs_current_bb /\
  FDOM t.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs ==>
  dft_activation_cut fn bb t
Proof
  strip_tac >>
  `TAKE t.vs_inst_idx bb.bb_instructions =
    TAKE s.vs_inst_idx bb.bb_instructions ++ [inst]` by
    (gvs[get_instruction_def, AllCaseEqs()] >>
     metis_tac[rich_listTheory.SNOC_EL_TAKE, SNOC_APPEND]) >>
  gvs[dft_activation_cut_def, MEM_APPEND, strict_dom_vars_defined_def,
      pred_setTheory.IN_UNION] >> metis_tac[]
QED

Theorem dft_activation_cut_ordinary:
  dft_activation_cut fn bb s /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst_wf inst /\
  ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 bb t) stack' n'
  ==> dft_activation_cut fn bb t
Proof
  strip_tac >> drule_all dft_occ_ordinary_fdom >> strip_tac >>
  drule_all dft_occ_ordinary_control >> strip_tac >>
  irule dft_activation_cut_advance >> goal_assum drule >> simp[] >>
  metis_tac[]
QED

Theorem dft_activation_cut_return:
  dft_activation_cut fn bb caller /\
  get_instruction bb caller.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fn 0 bb inst caller::stack) n /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftAt fn 0 bb t) stack' n'
  ==> dft_activation_cut fn bb t
Proof
  strip_tac >> drule_all dft_occ_return_fdom >> strip_tac >>
  drule_all dft_occ_return_control >> strip_tac >>
  irule dft_activation_cut_advance >> goal_assum drule >> simp[] >>
  metis_tac[]
QED
