Theory makeSsaCurrentActualAvailable
Ancestors makeSsaCurrentActualPath makeSsaCurrentAvailability simplifyCfgAvailability
  venomExecProofs venomExecProps venomWf venomInst venomState finite_map list

Theorem current_path_available_lookup:
  wf_function fn /\ scfg_path_defined fn path bb i st /\
  lookup_block l fn.fn_blocks = SOME bb /\ current_available fn v l i ==>
  ?value. lookup_var v st = SOME value
Proof
  simp[current_available_def] >> rpt strip_tac >>
  `bb' = bb` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `LAST path = l` by metis_tac[scfg_path_defined_def, lookup_block_label] >>
  qpat_x_assum `!path. _` (qspec_then `path` mp_tac) >>
  simp[] >>
  `path <> [] /\ is_fn_path fn path /\
    (?entry. fn_entry_label fn = SOME entry /\ HD path = entry)` by
    metis_tac[scfg_path_defined_def] >> simp[] >> strip_tac
  >- (`lookup_block (EL k path) fn.fn_blocks = SOME db` by
        (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
      fs[scfg_path_defined_def] >>
      `IS_SOME (lookup_var v st)` by metis_tac[] >>
      Cases_on `lookup_var v st` >> gvs[]) >>
  fs[scfg_path_defined_def] >>
  `IS_SOME (lookup_var v st)` by metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS] >>
  Cases_on `lookup_var v st` >> gvs[]
QED

Theorem current_actual_body_available:
  wf_function fn /\ current_actual_domain_cut fn (CurrentBody fuel bb) st /\
  current_available fn v st.vs_current_bb st.vs_inst_idx ==>
  ?value. lookup_var v st = SOME value
Proof
  simp[current_actual_domain_cut_def] >> metis_tac[current_path_available_lookup]
QED

Theorem current_actual_predecessor_exit_available:
  wf_function fn /\ current_actual_domain_cut fn (CurrentBody fuel bb) before /\
  get_instruction bb before.vs_inst_idx = SOME inst /\ inst_wf inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst before = OK after /\
  current_available fn v before.vs_current_bb (LENGTH bb.bb_instructions) ==>
  ?value. lookup_var v after = SOME value
Proof
  simp[current_actual_domain_cut_def] >> rpt strip_tac >>
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed, lookup_block_MEM] >>
  `before.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL before.vs_inst_idx bb.bb_instructions = inst` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `scfg_path_defined fn path bb (LENGTH bb.bb_instructions) after` by
    metis_tac[scfg_path_defined_end] >>
  metis_tac[current_path_available_lookup]
QED

Theorem current_actual_prefix_body_available:
  wf_function fn /\ fn_inst_wf fn /\ fn_entry_state fn seed /\
  current_actual_prefix fn ctx (CurrentEntry f) seed phases
    (SOME (CurrentBody fuel bb)) (OK before) before /\
  current_available fn v before.vs_current_bb before.vs_inst_idx ==>
  ?value. lookup_var v before = SOME value
Proof
  metis_tac[current_actual_entry_prefix_cut, current_actual_body_available]
QED

Theorem current_actual_exit_demand_defined:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  current_actual_domain_cut fn (CurrentBody fuel bb) before /\
  get_instruction bb before.vs_inst_idx = SOME inst /\ inst_wf inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst before = OK after /\
  current_demand fn v before.vs_current_bb (LENGTH bb.bb_instructions) ==>
  ?value. lookup_var v after = SOME value
Proof
  metis_tac[current_demand_available, current_actual_predecessor_exit_available]
QED
