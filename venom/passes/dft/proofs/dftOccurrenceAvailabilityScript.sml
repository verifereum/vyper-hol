Theory dftOccurrenceAvailability
Ancestors
  dftOccurrenceReplay dftOccurrenceMachine dftOpenErase dftOpenMachine
  venomExecProps venomExecProofs venomExecSemantics venomState venomInst finite_map list
  sccpCorrectnessProofs dftAvailability venomWf

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

Theorem dft_setup_callee_dom:
  setup_callee fn args caller = SOME cs ==> strict_dom_vars_defined fn cs
Proof
  strip_tac >> irule strict_dom_vars_defined_entry >>
  gvs[setup_callee_def, fn_entry_label_def, entry_block_def, AllCaseEqs()]
QED

Theorem dft_activation_cut_root_phis:
  fn_entry_label fn = SOME s.vs_current_bb /\
  bb.bb_label = s.vs_current_bb /\ eval_phis s bb.bb_instructions = OK sp ==>
  dft_activation_cut fn bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  strip_tac >> irule dft_activation_cut_phis >>
  goal_assum drule >> simp[] >> metis_tac[strict_dom_vars_defined_entry]
QED

Theorem dft_activation_cut_callee_phis:
  setup_callee fn args caller = SOME cs /\
  bb.bb_label = cs.vs_current_bb /\ eval_phis cs bb.bb_instructions = OK sp ==>
  dft_activation_cut fn bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  strip_tac >> irule dft_activation_cut_phis >>
  goal_assum drule >> simp[] >> metis_tac[dft_setup_callee_dom]
QED

Theorem dft_occ_terminator_exit[local]:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  (dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftEnter fn 0 t) stack' n'
  ==> step_inst_base inst s = OK t /\ ~t.vs_halted
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  qpat_x_assum `(dft_occ_oracle_next _ _ _).dft_occ_core = _` mp_tac >>
  simp[dft_occ_oracle_next_def, dft_next_inf_def, dft_erase_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def] >>
  Cases_on `step_inst_base inst s` >>
  simp[dft_open_deliver_def, dft_open_continue_def, dft_fill_def,
       dft_fill_control_def] >>
  rename1 `step_inst_base inst s = OK after` >>
  Cases_on `after.vs_halted` >> simp[dft_fill_control_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem dft_terminator_vars[local]:
  step_inst_base inst s = OK t /\ is_terminator inst.inst_opcode ==>
  t.vs_vars = s.vs_vars
Proof
  strip_tac >>
  `step_inst 0 C inst s = OK t` by
    (simp[step_inst_def] >>
     `inst.inst_opcode <> INVOKE` by
       (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >> simp[]) >>
  drule_all step_terminator_preserves_vars >>
  simp[lookup_var_def, finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM]
QED

Theorem dft_terminator_last[local]:
  bb_well_formed bb /\ get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode ==>
  s.vs_inst_idx = PRE (LENGTH bb.bb_instructions) /\
  inst = LAST bb.bb_instructions
Proof
  gvs[bb_well_formed_def, get_instruction_def, AllCaseEqs()] >>
  strip_tac >>
  `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >>
  simp[] >> metis_tac[LAST_EL]
QED

Theorem dft_cut_exit_outputs[local]:
  dft_activation_cut fn bb s /\ bb_well_formed bb /\
  EVERY inst_wf bb.bb_instructions /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode ==>
  !d v. MEM d bb.bb_instructions /\ MEM v d.inst_outputs ==>
    v IN FDOM s.vs_vars
Proof
  strip_tac >> drule_all dft_terminator_last >> strip_tac >>
  `inst_wf inst` by
    (fs[EVERY_MEM, get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  `inst.inst_outputs = []` by
    metis_tac[venomExecProofsTheory.terminator_no_outputs] >>
  rpt strip_tac >>
  `?i. i < LENGTH bb.bb_instructions /\ d = EL i bb.bb_instructions` by
    metis_tac[MEM_EL] >>
  `i <> s.vs_inst_idx` by
    (strip_tac >> gvs[get_instruction_def, AllCaseEqs()]) >>
  `i < s.vs_inst_idx` by decide_tac >>
  `MEM d (TAKE s.vs_inst_idx bb.bb_instructions)` by
    (simp[MEM_EL] >> qexists `i` >> simp[EL_TAKE, LENGTH_TAKE] >> decide_tac) >>
  fs[dft_activation_cut_def] >> metis_tac[]
QED

Theorem dft_occ_successor_available:
  wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  fn_reachable fn s.vs_current_bb /\ dft_activation_cut fn bb s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  (dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftEnter fn 0 t) stack' n'
  ==> fn_reachable fn t.vs_current_bb /\ strict_dom_vars_defined fn t
Proof
  strip_tac >> drule_all dft_occ_terminator_exit >> strip_tac >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `inst_wf inst` by
    (fs[EVERY_MEM, get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  drule_all step_inst_base_term_succs >> strip_tac >>
  drule_all dft_terminator_last >> strip_tac >>
  `t.vs_vars = s.vs_vars` by metis_tac[dft_terminator_vars] >>
  `MEM t.vs_current_bb (bb_succs bb)` by
    (Cases_on `bb.bb_instructions` >>
     gvs[bb_succs_def, bb_well_formed_def]) >>
  `fn_cfg_edge fn s.vs_current_bb t.vs_current_bb` by
    (fs[dft_activation_cut_def, fn_cfg_edge_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[fn_reachable_step] >>
  irule dft_dominance_transfer >> simp[] >> qexistsl [`bb`, `s`] >>
  simp[] >>
  `!d v. MEM d bb.bb_instructions /\ MEM v d.inst_outputs ==>
      v IN FDOM s.vs_vars` by metis_tac[dft_cut_exit_outputs] >>
  fs[dft_activation_cut_def] >> metis_tac[]
QED
