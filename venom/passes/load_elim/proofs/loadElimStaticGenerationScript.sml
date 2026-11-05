Theory loadElimStaticGeneration
Ancestors
  loadElimActualGeneration loadElimTransferProvenance loadElimDefs
  venomInst venomWf venomExecProofs dfAnalyzeDefs cfgDefs cfgAnalysisProps
  sccpCorrectnessProofs simplifyCfgPhiSemantics finite_map list rich_list

Theorem le_analyze_singleton_prefix:
  !n. wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  n <= LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) lbl n)) key = SOME [op] ==>
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) lbl 0)) key = SOME [op] \/
  ?inst. MEM inst (TAKE n bb.bb_instructions) /\
    le_transfer_generates ctx inst key op
Proof
  Induct >> simp[] >> strip_tac >>
  `n < LENGTH bb.bb_instructions` by simp[] >>
  `n <= LENGTH bb.bb_instructions` by simp[] >>
  drule_all le_analyze_singleton_step >> strip_tac
  >- (first_x_assum drule_all >> strip_tac >> simp[] >>
      disj2_tac >> qexists `inst` >> simp[TAKE_SUC, MEM_APPEND]) >>
  disj2_tac >> qexists `EL n bb.bb_instructions` >>
  simp[TAKE_SUC, MEM_APPEND]
QED

Theorem le_static_path_dfs:
  wf_function fn /\ fn_inst_wf fn /\ is_fn_path fn path /\ path <> [] /\
  fn_entry_label fn = SOME (HD path) /\ MEM lbl path ==>
  MEM lbl (cfg_analyze fn).cfg_dfs_pre
Proof
  strip_tac >> irule fn_reachable_in_dfs_pre >> simp[] >>
  irule scfg_path_member_reachable >> metis_tac[]
QED

Theorem le_static_path_snoc_parts[local]:
  !path. path <> [] /\ is_fn_path fn (SNOC lbl path) ==>
  is_fn_path fn path /\ fn_cfg_edge fn (LAST path) lbl
Proof
  Induct >> simp[] >> Cases_on `path` >> gvs[is_fn_path_def]
QED

Theorem le_static_edge_pred:
  wf_function fn /\ fn_cfg_edge fn src dst ==>
  MEM src (cfg_preds_of (cfg_analyze fn) dst)
Proof
  gvs[fn_cfg_edge_def] >> rpt strip_tac >>
  metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond,
    cfgAnalysisPropsTheory.bb_succs_in_cfg_succs, wf_function_def,
    venomExecProofsTheory.lookup_block_label]
QED

Theorem le_static_path_singleton_generation:
  !path bb n.
  wf_function fn /\ fn_inst_wf fn /\ le_configured_context ctx /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  is_fn_path fn path /\ path <> [] /\
  fn_entry_label fn = SOME (HD path) /\ LAST path = bb.bb_label /\
  MEM bb fn.fn_blocks /\ n <= LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label n)) key = SOME [op] ==>
  (?j gb inst. j < LENGTH path - 1 /\ MEM gb fn.fn_blocks /\
     gb.bb_label = EL j path /\ MEM inst gb.bb_instructions /\
     le_transfer_generates ctx inst key op) \/
  (?inst. MEM inst (TAKE n bb.bb_instructions) /\
     le_transfer_generates ctx inst key op)
Proof
  ho_match_mp_tac SNOC_INDUCT >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (irule le_static_path_dfs >> metis_tac[LAST_MEM]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[] >> gvs[wf_function_def, fn_labels_def]) >>
  drule_all le_analyze_singleton_prefix >> strip_tac
  >- suspend "boundary"
  >> metis_tac[]
QED

Resume le_static_path_singleton_generation[boundary]:
  Cases_on `path = []`
  >- (gvs[] >> drule_all le_analyze_entry_no_lookup >>
      disch_then (qspecl_then [`key`, `ctx`] mp_tac) >> simp[]) >>
  drule_all le_static_path_snoc_parts >> strip_tac >>
  `fn_entry_label fn = SOME (HD path)` by
    (Cases_on `path` >> gvs[]) >>
  `MEM (LAST path) (cfg_analyze fn).cfg_dfs_pre` by
    (irule le_static_path_dfs >> metis_tac[LAST_MEM]) >>
  `MEM (LAST path) (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
    (irule le_static_edge_pred >> gvs[]) >>
  `?prev. lookup_block (LAST path) fn.fn_blocks = SOME prev` by
    (gvs[fn_cfg_edge_def] >> qexists `bb'` >>
     irule MEM_lookup_block >> simp[] >> gvs[wf_function_def, fn_labels_def]) >>
  drule_all le_analyze_singleton_predecessor >> strip_tac >>
  drule_all le_analyze_singleton_exit >> strip_tac >>
  `MEM prev fn.fn_blocks /\ prev.bb_label = LAST path` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
      prev.bb_label (LENGTH prev.bb_instructions))) key = SOME [op]` by
    metis_tac[] >>
  first_x_assum (qspecl_then [`prev`, `LENGTH prev.bb_instructions`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (disj1_tac >> qexistsl [`j`, `gb`, `inst`] >>
      simp[EL_SNOC] >> `j < LENGTH path` by decide_tac >> simp[]) >>
  disj1_tac >> qexistsl [`LENGTH path - 1`, `prev`, `inst`] >>
  simp[EL_SNOC] >>
  `LENGTH path - 1 < LENGTH path` by (Cases_on `path` >> gvs[]) >>
  gvs[SNOC_APPEND, EL_APPEND1, TAKE_LENGTH_ID_rwt, LAST_EL] >>
  `PRE (LENGTH path) = LENGTH path - 1` by decide_tac >> simp[]
QED
Finalise le_static_path_singleton_generation
