Theory loadElimActualGeneration
Ancestors
  loadElimBackwardSelectionAudit loadElimOccurrenceCoverage
  loadElimSupportHelpers loadElimGeneratedSupport loadElimConvergence
  loadElimNonempty loadElimPopulation loadElimSolverProvenance
  loadElimDefs dfAnalyzeDefs cfgDefs venomWf finite_map list
  sccpCorrectnessProofs simplifyCfgPhiSemantics rich_list
  loadElimTransferProvenance loadElimOccurrence

(* Exact selection needs both nonemptiness and duplicate freedom. *)
Theorem le_analyze_boundary_singleton_selection:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) lbl)) key = SOME ws /\
  (!x. MEM x ws ==> MEM x [op]) ==>
  ws = [op]
Proof
  strip_tac >>
  `ALL_DISTINCT ws` by
    (drule_all le_analyze_boundary_supported >>
     simp[le_lattice_supported_def] >> metis_tac[]) >>
  `ws <> []` by metis_tac[le_analyze_boundary_lookup_nonempty] >>
  irule le_distinct_singleton_selection >> simp[]
QED

Theorem le_analyze_point_singleton_selection:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  n <= LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) lbl n)) key = SOME ws /\
  (!x. MEM x ws ==> MEM x [op]) ==>
  ws = [op]
Proof
  strip_tac >>
  `ALL_DISTINCT ws` by
    (drule_all le_analyze_point_supported >>
     simp[le_lattice_supported_def] >> metis_tac[]) >>
  `ws <> []` by metis_tac[le_analyze_point_lookup_nonempty] >>
  irule le_distinct_singleton_selection >> simp[]
QED

Theorem le_analyze_singleton_predecessor:
  wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM pred (cfg_preds_of (cfg_analyze fn) lbl) /\
  MEM pred (cfg_analyze fn).cfg_dfs_pre /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) lbl 0)) key = SOME [op] ==>
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) pred)) key = SOME [op]
Proof
  strip_tac >>
  `?m. df_boundary NONE (load_analyze ctx fn) pred = SOME m` by
    metis_tac[le_analyze_boundary_some] >>
  drule_all le_analyze_selected_predecessor >> strip_tac >>
  `ws = [op]` by
    (irule le_analyze_boundary_singleton_selection >>
     conj_tac >- simp[] >>
     qexistsl [`ctx`, `fn`, `key`, `pred`] >>
     simp[unwrap_load_lattice_def]) >>
  gvs[unwrap_load_lattice_def]
QED

Theorem le_analyze_singleton_exit:
  wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) lbl)) key = SOME [op] ==>
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) lbl (LENGTH bb.bb_instructions))) key = SOME [op]
Proof
  strip_tac >>
  `?exit. df_at NONE (load_analyze ctx fn) lbl (LENGTH bb.bb_instructions) = SOME exit` by
    (irule le_analyze_at_some >> simp[]) >>
  drule_all le_analyze_selected_exit >> strip_tac >>
  `ws = [op]` by
    (irule le_analyze_point_singleton_selection >>
     conj_tac >- simp[] >>
     qexistsl [`bb`, `ctx`, `fn`, `key`, `lbl`, `LENGTH bb.bb_instructions`] >>
     simp[unwrap_load_lattice_def]) >>
  gvs[unwrap_load_lattice_def]
QED

Theorem le_configured_phi_fold:
  !xs ll. le_configured_context ctx /\
  EVERY (\i. i.inst_opcode = PHI) xs ==>
  FOLDL (\a i. load_transfer ctx i a) ll xs =
    if xs = [] then ll else SOME (unwrap_load_lattice ll)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `load_transfer ctx h ll = SOME (unwrap_load_lattice ll)` by
    metis_tac[le_configured_phi_transfer] >>
  simp[] >> first_x_assum drule_all >>
  simp[unwrap_load_lattice_def]
QED

Theorem le_phi_prefix_all_phi[local]:
  !xs. EVERY (\i. i.inst_opcode = PHI)
    (TAKE (phi_prefix_length xs) xs)
Proof
  Induct >- simp[venomExecSemanticsTheory.phi_prefix_length_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[venomExecSemanticsTheory.phi_prefix_length_def]
QED

Theorem le_analyze_phi_prefix_lookup:
  wf_function fn /\ le_configured_context ctx /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  unwrap_load_lattice (df_at NONE (load_analyze ctx fn) lbl
    (phi_prefix_length bb.bb_instructions)) =
  unwrap_load_lattice (df_at NONE (load_analyze ctx fn) lbl 0)
Proof
  strip_tac >>
  `phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
    simp[venomExecProofsTheory.phi_prefix_length_le] >>
  drule_all le_analyze_prefix_fold >> disch_then SUBST1_TAC >>
  drule le_configured_phi_fold >>
  disch_then (qspecl_then
    [`TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions`,
     `df_at NONE (load_analyze ctx fn) lbl 0`] mp_tac) >>
  simp[le_phi_prefix_all_phi] >> strip_tac >> simp[] >>
  IF_CASES_TAC >> simp[unwrap_load_lattice_def]
QED

Theorem le_analyze_entry_no_lookup:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  fn_entry_label fn = SOME lbl ==>
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) lbl 0)) key = NONE
Proof
  strip_tac >> drule_all le_analyze_entry_join >>
  disch_then (qspec_then `ctx` SUBST1_TAC) >>
  simp[df_joined_val_def] >>
  qmatch_goalsub_abbrev_tac `load_join (SOME FEMPTY) rest` >>
  Cases_on `FLOOKUP (unwrap_load_lattice
    (load_join (SOME FEMPTY) rest)) key` >> simp[] >>
  drule_at Any le_join_selected_lookup_left >> simp[]
QED

Theorem le_occ_prefix_dfs:
  le_occ_prefix C fn s0 es i s /\ wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb ==>
  MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
Proof
  strip_tac >> drule_all le_occ_prefix_route >> strip_tac >>
  irule fn_reachable_in_dfs_pre >> simp[] >>
  irule scfg_path_member_reachable >>
  qexists `le_occ_route es` >> simp[] >> metis_tac[rich_listTheory.LAST_MEM]
QED

Theorem le_analyze_singleton_step:
  wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  n < LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) lbl (SUC n))) key = SOME [op] ==>
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) lbl n)) key = SOME [op] \/
  le_transfer_generates ctx (EL n bb.bb_instructions) key op
Proof
  strip_tac >>
  `SUC n <= LENGTH bb.bb_instructions` by simp[] >>
  `n <= LENGTH bb.bb_instructions` by simp[] >>
  `df_at NONE (load_analyze ctx fn) lbl (SUC n) =
    FOLDL (\a i. load_transfer ctx i a)
      (df_at NONE (load_analyze ctx fn) lbl 0)
      (TAKE (SUC n) bb.bb_instructions)` by
    (irule le_analyze_prefix_fold >> simp[]) >>
  `df_at NONE (load_analyze ctx fn) lbl n =
    FOLDL (\a i. load_transfer ctx i a)
      (df_at NONE (load_analyze ctx fn) lbl 0)
      (TAKE n bb.bb_instructions)` by
    (irule le_analyze_prefix_fold >> simp[]) >>
  gvs[TAKE_SUC, FOLDL_APPEND] >>
  drule le_transfer_lookup_origin >> simp[]
QED

Theorem le_occ_prefix_singleton_generation:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
  !ctx key op.
  wf_function fn /\ fn_inst_wf fn /\ le_configured_context ctx /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [op] ==>
  ?bb n fuel pre post. MEM (StepOcc bb n fuel pre post) es /\
    le_transfer_generates ctx (EL n bb.bb_instructions) key op
Proof
  ho_match_mp_tac le_occ_prefix_strongind >> rpt conj_tac
  >- suspend "start"
  >- suspend "next"
  >> suspend "block"
QED

Resume le_occ_prefix_singleton_generation[start]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `p.vs_current_bb = s0.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  `MEM s0.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[sccpProofsBaseTheory.entry_label_in_dfs_pre] >>
  gvs[] >>
  `unwrap_load_lattice (df_at NONE (load_analyze ctx fn) s0.vs_current_bb
     (phi_prefix_length bb.bb_instructions)) =
   unwrap_load_lattice (df_at NONE (load_analyze ctx fn) s0.vs_current_bb 0)` by
    (irule le_analyze_phi_prefix_lookup >> simp[]) >>
  `FLOOKUP (unwrap_load_lattice
     (df_at NONE (load_analyze ctx fn) s0.vs_current_bb 0)) key = NONE` by
    (irule le_analyze_entry_no_lookup >> simp[] >> metis_tac[]) >> gvs[]
QED

Resume le_occ_prefix_singleton_generation[next]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[le_occ_prefix_dfs] >>
  gvs[] >>
  `FLOOKUP (unwrap_load_lattice
     (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [op] \/
   le_transfer_generates ctx (EL s.vs_inst_idx bb.bb_instructions) key op` by
    (irule le_analyze_singleton_step >> simp[] >> metis_tac[])
  >- (first_x_assum drule_all >> strip_tac >> metis_tac[]) >>
  qexistsl [`bb`, `s.vs_inst_idx`, `k`, `s`, `u`] >> simp[]
QED

Resume le_occ_prefix_singleton_generation[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[le_occ_prefix_dfs] >>
  `active_inst fn i s` by metis_tac[le_occ_prefix_active] >>
  `fn_cfg_edge fn bb.bb_label u.vs_current_bb` by
    metis_tac[le_active_terminator_edge] >>
  `bb.bb_label = s.vs_current_bb /\ p.vs_current_bb = u.vs_current_bb` by
    metis_tac[venomExecProofsTheory.lookup_block_label,
      venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  `MEM u.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[fn_cfg_edge_in_dfs_pre] >>
  `MEM bb.bb_label (cfg_preds_of (cfg_analyze fn) u.vs_current_bb)` by
    (gvs[venomWfTheory.fn_cfg_edge_def] >>
     metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond,
       cfgAnalysisPropsTheory.bb_succs_in_cfg_succs,
       venomWfTheory.wf_function_def, venomExecProofsTheory.lookup_block_label]) >>
  gvs[] >>
  `unwrap_load_lattice (df_at NONE (load_analyze ctx fn) u.vs_current_bb
     (phi_prefix_length next.bb_instructions)) =
   unwrap_load_lattice (df_at NONE (load_analyze ctx fn) u.vs_current_bb 0)` by
    (irule le_analyze_phi_prefix_lookup >> simp[]) >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
     u.vs_current_bb 0)) key = SOME [op]` by metis_tac[] >>
  `FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn)
     s.vs_current_bb)) key = SOME [op]` by
    (irule le_analyze_singleton_predecessor >> simp[] >> metis_tac[]) >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
     s.vs_current_bb (LENGTH bb.bb_instructions))) key = SOME [op]` by
    (irule le_analyze_singleton_exit >> simp[] >> metis_tac[]) >>
  `SUC s.vs_inst_idx = LENGTH bb.bb_instructions` by
    (`bb_well_formed bb` by
       metis_tac[venomExecProofsTheory.wf_function_bb_well_formed,
         venomExecProofsTheory.lookup_block_MEM] >>
     gvs[venomWfTheory.bb_well_formed_def] >> metis_tac[]) >>
  `FLOOKUP (unwrap_load_lattice
     (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [op] \/
   le_transfer_generates ctx (EL s.vs_inst_idx bb.bb_instructions) key op` by
    (irule le_analyze_singleton_step >> simp[] >> metis_tac[])
  >- (first_x_assum drule_all >> strip_tac >> metis_tac[]) >>
  qexistsl [`bb`, `s.vs_inst_idx`, `k`, `s`, `u`] >> simp[]
QED

Finalise le_occ_prefix_singleton_generation
