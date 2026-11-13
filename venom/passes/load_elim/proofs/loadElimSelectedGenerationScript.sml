Theory loadElimSelectedGeneration
Ancestors
  loadElimStaticGeneration loadElimActualGeneration loadElimTransferProvenance
  loadElimSolverProvenance loadElimPopulation loadElimNonempty loadElimDefs
  venomInst venomWf venomExecProofs dfAnalyzeDefs cfgDefs finite_map list rich_list

Theorem le_fold_member_origin[local]:
  !insts initial vs.
  FLOOKUP (unwrap_load_lattice
    (FOLDL (\ll i. load_transfer ctx i ll) initial insts)) key = SOME vs ==>
  FLOOKUP (unwrap_load_lattice initial) key = SOME vs \/
  ?op inst. MEM op vs /\ MEM inst insts /\ le_transfer_generates ctx inst key op
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac
  >- (drule le_transfer_lookup_origin >> strip_tac >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem le_analyze_member_prefix[local]:
  wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ n <= LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) lbl n)) key = SOME vs ==>
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) lbl 0)) key = SOME vs \/
  ?op inst. MEM op vs /\ MEM inst (TAKE n bb.bb_instructions) /\
    le_transfer_generates ctx inst key op
Proof
  strip_tac >> drule_all le_analyze_prefix_fold >> strip_tac >>
  gvs[] >> drule le_fold_member_origin >> simp[]
QED

Theorem le_selected_snoc_parts[local]:
  !path. path <> [] /\ is_fn_path fn (SNOC lbl path) ==>
  is_fn_path fn path /\ fn_cfg_edge fn (LAST path) lbl
Proof
  Induct >> simp[] >> Cases_on `path` >> gvs[is_fn_path_def]
QED

Theorem le_static_path_member_generation:
  !path bb n vs.
  wf_function fn /\ fn_inst_wf fn /\ le_configured_context ctx /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  is_fn_path fn path /\ path <> [] /\
  fn_entry_label fn = SOME (HD path) /\ LAST path = bb.bb_label /\
  MEM bb fn.fn_blocks /\ n <= LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label n)) key = SOME vs ==>
  ?op. MEM op vs /\
    ((?j gb inst. j < LENGTH path - 1 /\ MEM gb fn.fn_blocks /\
       gb.bb_label = EL j path /\ MEM inst gb.bb_instructions /\
       le_transfer_generates ctx inst key op) \/
     (?inst. MEM inst (TAKE n bb.bb_instructions) /\
       le_transfer_generates ctx inst key op))
Proof
  ho_match_mp_tac SNOC_INDUCT >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (irule le_static_path_dfs >> metis_tac[LAST_MEM]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[] >> gvs[wf_function_def, fn_labels_def]) >>
  drule_all le_analyze_member_prefix >> strip_tac
  >- suspend "boundary"
  >> metis_tac[]
QED

Resume le_static_path_member_generation[boundary]:
  Cases_on `path = []`
  >- (gvs[] >> drule_all le_analyze_entry_no_lookup >>
      disch_then (qspecl_then [`key`, `ctx`] mp_tac) >> simp[]) >>
  drule_all le_selected_snoc_parts >> strip_tac >>
  `fn_entry_label fn = SOME (HD path)` by
    (Cases_on `path` >> gvs[]) >>
  `MEM (LAST path) (cfg_analyze fn).cfg_dfs_pre` by
    (irule le_static_path_dfs >> metis_tac[LAST_MEM]) >>
  `MEM (LAST path) (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
    (irule le_static_edge_pred >> gvs[]) >>
  `?prev. lookup_block (LAST path) fn.fn_blocks = SOME prev` by
    (gvs[fn_cfg_edge_def] >> qexists `bb'` >>
     irule MEM_lookup_block >> simp[] >> gvs[wf_function_def, fn_labels_def]) >>
  `?m. df_boundary NONE (load_analyze ctx fn) (LAST path) = SOME m` by
    metis_tac[le_analyze_boundary_some] >>
  drule_all le_analyze_selected_predecessor >>
  disch_then (qx_choose_then `ws` strip_assume_tac) >>
  `?exit. df_at NONE (load_analyze ctx fn) (LAST path)
    (LENGTH prev.bb_instructions) = SOME exit` by
    (irule le_analyze_at_some >> simp[]) >>
  `FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) (LAST path))) key = SOME ws` by
    simp[unwrap_load_lattice_def] >>
  drule_all le_analyze_selected_exit >>
  disch_then (qx_choose_then `zs` strip_assume_tac) >>
  `MEM prev fn.fn_blocks /\ prev.bb_label = LAST path` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  first_x_assum (qspecl_then [`prev`, `LENGTH prev.bb_instructions`, `zs`] mp_tac) >>
  impl_tac >- (simp[] >> gvs[unwrap_load_lattice_def]) >>
  disch_then (qx_choose_then `op` assume_tac) >>
  `MEM op vs` by metis_tac[] >>
  qexists `op` >> simp[] >>
  pop_assum kall_tac >>
  qpat_x_assum `MEM op zs /\ _` strip_assume_tac
  >- (disj1_tac >> qexistsl [`j`, `gb`, `inst`] >>
      simp[EL_SNOC] >> `j < LENGTH path` by decide_tac >> simp[]) >>
  disj1_tac >> qexistsl [`LENGTH path - 1`, `prev`, `inst`] >>
  simp[EL_SNOC] >>
  `LENGTH path - 1 < LENGTH path` by (Cases_on `path` >> gvs[]) >>
  gvs[SNOC_APPEND, EL_APPEND1, TAKE_LENGTH_ID_rwt, LAST_EL] >>
  `PRE (LENGTH path) = LENGTH path - 1` by decide_tac >> simp[]
QED
Finalise le_static_path_member_generation
