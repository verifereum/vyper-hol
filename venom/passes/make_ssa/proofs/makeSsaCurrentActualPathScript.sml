Theory makeSsaCurrentActualPath
Ancestors simplifyCfgAvailability makeSsaCurrentExecutionHistory venomExecProofs
  venomExecProps venomInstProps venomWf venomInst venomState finite_map list

Definition current_actual_domain_cut_def:
  (current_actual_domain_cut fn (CurrentBody fuel bb) st <=>
    lookup_block st.vs_current_bb fn.fn_blocks = SOME bb /\
    ?path. scfg_path_defined fn path bb st.vs_inst_idx st) /\
  (current_actual_domain_cut fn (CurrentEntry fuel) st <=>
    fn_entry_state fn st \/
    ?path bb. scfg_path_defined fn path bb (LENGTH bb.bb_instructions) st /\
      lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
      fn_cfg_edge fn bb.bb_label st.vs_current_bb)
End

Theorem current_actual_domain_cut_init:
  fn_entry_state fn st ==> current_actual_domain_cut fn (CurrentEntry fuel) st
Proof
  simp[current_actual_domain_cut_def]
QED

Theorem current_actual_domain_cut_dispatch:
  current_actual_domain_cut fn (CurrentEntry (SUC fuel)) before /\
  lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis before bb.bb_instructions = OK post ==>
  current_actual_domain_cut fn (CurrentBody fuel bb)
    (post with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  simp[current_actual_domain_cut_def] >> strip_tac >>
  `post.vs_current_bb = before.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >> simp[] >>
  Cases_on `fn_entry_state fn before`
  >- metis_tac[scfg_path_defined_entry] >>
  gvs[] >>
  `bb.bb_label = before.vs_current_bb` by metis_tac[lookup_block_label] >>
  metis_tac[scfg_path_defined_append]
QED

Theorem current_actual_domain_cut_ordinary:
  current_actual_domain_cut fn (CurrentBody fuel bb) before /\
  get_instruction bb before.vs_inst_idx = SOME inst /\ inst_wf inst /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst before = OK post ==>
  current_actual_domain_cut fn (CurrentBody fuel bb)
    (post with vs_inst_idx := SUC before.vs_inst_idx)
Proof
  simp[current_actual_domain_cut_def] >> rpt strip_tac >>
  `post.vs_current_bb = before.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >> simp[] >>
  `before.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL before.vs_inst_idx bb.bb_instructions = inst` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `scfg_path_defined fn path bb (SUC before.vs_inst_idx) post` by
    metis_tac[scfg_path_defined_step] >>
  qexists_tac `path` >> gvs[scfg_path_defined_def, lookup_var_def] >> metis_tac[]
QED

Theorem current_actual_domain_cut_terminator:
  wf_function fn /\ current_actual_domain_cut fn (CurrentBody fuel bb) before /\
  get_instruction bb before.vs_inst_idx = SOME inst /\ inst_wf inst /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst before = OK post /\ ~post.vs_halted ==>
  current_actual_domain_cut fn (CurrentEntry fuel) post
Proof
  simp[current_actual_domain_cut_def] >> rpt strip_tac >> disj2_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = before.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed] >>
  `before.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL before.vs_inst_idx bb.bb_instructions = inst` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `scfg_path_defined fn path bb (LENGTH bb.bb_instructions) post` by
    metis_tac[scfg_path_defined_end] >>
  `LAST bb.bb_instructions = inst` by
    (gvs[bb_well_formed_def, LAST_EL] >> metis_tac[]) >>
  `MEM post.vs_current_bb (get_successors inst)` by
    metis_tac[step_inst_base_term_succs, venomExecSemanticsTheory.step_inst_non_invoke] >>
  `MEM post.vs_current_bb (bb_succs bb)` by
    (Cases_on `bb.bb_instructions` >> gvs[bb_succs_def, MEM_nub, MEM_REVERSE]) >>
  qexistsl_tac [`path`, `bb`] >> simp[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem current_actual_domain_cut_edge:
  !loc before phases next result after.
  current_execution_edge fn ctx loc before phases next result after ==>
  wf_function fn /\ fn_inst_wf fn /\ current_actual_domain_cut fn loc before ==>
  !nextloc. next = SOME nextloc /\ result = OK after ==>
    current_actual_domain_cut fn nextloc after
Proof
  ho_match_mp_tac current_execution_edge_ind >> rpt conj_tac >> rpt gen_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[current_actual_domain_cut_dispatch])
  >- (rpt strip_tac >> gvs[] >> metis_tac[current_actual_domain_cut_ordinary])
  >- (rpt strip_tac >> gvs[AllCaseEqs()] >>
      metis_tac[current_actual_domain_cut_terminator]) >>
  rpt strip_tac >> gvs[]
QED

Theorem current_actual_domain_cut_prefix:
  !loc before phases next result after.
  current_actual_prefix fn ctx loc before phases next result after ==>
  wf_function fn /\ fn_inst_wf fn /\ current_actual_domain_cut fn loc before ==>
  !nextloc. next = SOME nextloc /\ result = OK after ==>
    current_actual_domain_cut fn nextloc after
Proof
  ho_match_mp_tac current_actual_prefix_ind >> rpt conj_tac >> rpt gen_tac
  >- (simp[])
  >- metis_tac[current_actual_domain_cut_edge]
  >- metis_tac[current_actual_domain_cut_edge] >>
  simp[]
QED

Theorem current_actual_entry_prefix_cut:
  wf_function fn /\ fn_inst_wf fn /\ fn_entry_state fn seed /\
  current_actual_prefix fn ctx (CurrentEntry fuel) seed phases
    (SOME next) (OK after) after ==>
  current_actual_domain_cut fn next after
Proof
  metis_tac[current_actual_domain_cut_init, current_actual_domain_cut_prefix]
QED

Theorem current_actual_body_path:
  current_actual_domain_cut fn (CurrentBody fuel bb) st ==>
  lookup_block st.vs_current_bb fn.fn_blocks = SOME bb /\
  ?path. scfg_path_defined fn path bb st.vs_inst_idx st /\
    path <> [] /\ is_fn_path fn path /\
    fn_entry_label fn = SOME (HD path) /\ LAST path = st.vs_current_bb /\
    (!k b inst v. k < LENGTH path - 1 /\
      lookup_block (EL k path) fn.fn_blocks = SOME b /\
      MEM inst b.bb_instructions /\ MEM v inst.inst_outputs ==>
      v IN FDOM st.vs_vars) /\
    (!k v. k < st.vs_inst_idx /\ k < LENGTH bb.bb_instructions /\
      MEM v (EL k bb.bb_instructions).inst_outputs ==> v IN FDOM st.vs_vars)
Proof
  simp[current_actual_domain_cut_def] >> rpt strip_tac >>
  qexists_tac `path` >>
  `bb.bb_label = st.vs_current_bb` by metis_tac[lookup_block_label] >>
  gvs[scfg_path_defined_def, lookup_var_def, FLOOKUP_DEF, COND_RAND] >> metis_tac[]
QED

Theorem current_actual_pending_path:
  current_actual_domain_cut fn (CurrentEntry fuel) st /\ ~fn_entry_state fn st ==>
  ?path bb. scfg_path_defined fn path bb (LENGTH bb.bb_instructions) st /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    fn_cfg_edge fn bb.bb_label st.vs_current_bb
Proof
  simp[current_actual_domain_cut_def] >> metis_tac[]
QED

Theorem current_actual_raw_ok_path:
  current_actual_domain_cut fn (CurrentBody fuel bb) before /\
  get_instruction bb before.vs_inst_idx = SOME inst /\ inst_wf inst /\
  step_inst fuel ctx inst before = OK post ==>
  ?path. scfg_path_defined fn path bb before.vs_inst_idx before /\
    scfg_path_defined fn path bb (SUC before.vs_inst_idx) post
Proof
  simp[current_actual_domain_cut_def] >> rpt strip_tac >>
  `before.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL before.vs_inst_idx bb.bb_instructions = inst` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  metis_tac[scfg_path_defined_step]
QED
