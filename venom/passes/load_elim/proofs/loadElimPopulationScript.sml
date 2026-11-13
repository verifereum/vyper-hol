Theory loadElimPopulation
Ancestors cfgCorrectnessProof
  loadElimConvergence loadElimSolverProvenance loadElimSolverHelpers
  loadElimDefs cfgDefs cfgAnalysisProps dfAnalyzeDefs venomWf venomInst venomExecProps
  finite_map list rich_list relation dfAnalyzeProofs

Theorem le_transfer_some:
  ?m. load_transfer ctx inst ll = SOME m
Proof
  simp[load_transfer_def]
QED

Theorem le_transfer_fold_some:
  !xs ll. ll <> NONE ==>
    FOLDL (\a i. load_transfer ctx i a) ll xs <> NONE
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  metis_tac[le_transfer_some, optionTheory.NOT_NONE_SOME]
QED

Theorem le_transfer_nonempty_fold_some:
  xs <> [] ==> FOLDL (\a i. load_transfer ctx i a) ll xs <> NONE
Proof
  Cases_on `xs` >> simp[] >>
  match_mp_tac le_transfer_fold_some >>
  metis_tac[le_transfer_some, optionTheory.NOT_NONE_SOME]
QED

Theorem le_join_some:
  a <> NONE \/ b <> NONE ==> load_join a b <> NONE
Proof
  Cases_on `a` >> Cases_on `b` >> simp[load_join_def]
QED

Theorem le_analyze_exit_some:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  df_at NONE (load_analyze ctx fn) lbl (LENGTH bb.bb_instructions) <> NONE
Proof
  rpt strip_tac >>
  `MEM bb fn.fn_blocks` by
    metis_tac[lookup_block_def, venomExecPropsTheory.FIND_MEM] >>
  `bb.bb_instructions <> []` by
    fs[wf_function_def, bb_well_formed_def] >>
  `is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn)` by
    metis_tac[le_load_analyze_fixpoint, le_solver_process_def] >>
  mp_tac (Q.SPEC `LENGTH bb.bb_instructions` le_analyze_prefix_fold) >>
  simp[] >>
  metis_tac[le_transfer_nonempty_fold_some]
QED

Theorem le_analyze_boundary_some:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
  ?m. df_boundary NONE (load_analyze ctx fn) lbl = SOME m
Proof
  rpt strip_tac >>
  `MEM lbl (fn_labels fn)` by
    (irule cfg_analyze_reachable_in_labels >>
     drule cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  fs[fn_labels_def] >> drule lookup_block_exists >> strip_tac >>
  drule_all le_analyze_exit_some >> strip_tac >>
  drule_all le_analyze_boundary_absorbs >> strip_tac >>
  Cases_on `df_boundary NONE (load_analyze ctx fn) lbl` >>
  gvs[load_join_def] >>
  qpat_x_assum `!ctx'. _` (qspec_then `ctx` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem le_join_fold_some:
  !xs a. a <> NONE \/ (?m. MEM (SOME m) xs) ==>
    FOLDL load_join a xs <> NONE
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  fs[] >> first_x_assum irule >> Cases_on `h` >> gvs[] >>
  metis_tac[le_join_some, optionTheory.NOT_NONE_SOME]
QED

Theorem le_reached_predecessor:
  wf_function fn /\ entry_block fn = SOME entry /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\ lbl <> entry.bb_label ==>
  ?pred. MEM pred (cfg_analyze fn).cfg_dfs_pre /\
    MEM pred (cfg_preds_of (cfg_analyze fn) lbl)
Proof
  rpt strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by
    (drule cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  drule_all cfg_analyze_semantic_reachability >> strip_tac >>
  `cfg_path (cfg_analyze fn) entry.bb_label lbl` by metis_tac[] >>
  qpat_x_assum `cfg_path _ _ lbl` mp_tac >>
  simp[cfg_path_def, Once RTC_CASES2] >> strip_tac >> gvs[] >>
  rename1 `MEM lbl (cfg_succs_of (cfg_analyze fn) pred)` >>
  qexists `pred` >> simp[GSYM cfg_edge_symmetry_uncond] >>
  `cfg_reachable_of (cfg_analyze fn) pred` by
    metis_tac[cfg_path_def] >>
  drule cfg_analyze_reachable_sets >> simp[pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

Theorem le_analyze_entry_some:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  df_at NONE (load_analyze ctx fn) lbl 0 <> NONE
Proof
  rpt gen_tac >> strip_tac >>
  `?entry. entry_block fn = SOME entry` by
    (Cases_on `fn.fn_blocks` >> fs[wf_function_def, fn_has_entry_def,
      entry_block_def]) >>
  `fn_entry_label fn = SOME entry.bb_label` by simp[fn_entry_label_def] >>
  `df_at NONE (load_analyze ctx fn) lbl 0 =
    df_joined_val Forward NONE load_join load_edge_transfer ctx
      (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) (load_analyze ctx fn) lbl` by
    (irule le_analyze_entry_join >> simp[]) >>
  simp[df_joined_val_def, load_edge_transfer_def] >>
  Cases_on `lbl = entry.bb_label`
  >- (simp[] >> irule le_join_some >> simp[]) >>
  simp[] >>
  drule_all le_reached_predecessor >> strip_tac >>
  `?m. df_boundary NONE (load_analyze ctx fn) pred = SOME m` by
    (irule le_analyze_boundary_some >> simp[]) >>
  Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >- gvs[] >>
  simp[] >> irule le_join_fold_some >>
  Cases_on `pred = h` >- (gvs[] >> simp[load_join_def]) >>
  disj2_tac >> qexists `m` >> simp[MEM_MAP] >> qexists `pred` >> gvs[]
QED

Theorem le_analyze_at_some:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ n <= LENGTH bb.bb_instructions ==>
  ?m. df_at NONE (load_analyze ctx fn) lbl n = SOME m
Proof
  strip_tac >>
  `df_at NONE (load_analyze ctx fn) lbl 0 <> NONE` by
    (irule le_analyze_entry_some >> simp[]) >>
  `is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn)` by
    metis_tac[le_load_analyze_fixpoint, le_solver_process_def] >>
  `df_at NONE (load_analyze ctx fn) lbl n =
   FOLDL (\a i. load_transfer ctx i a)
     (df_at NONE (load_analyze ctx fn) lbl 0) (TAKE n bb.bb_instructions)` by
    (irule le_analyze_prefix_fold >> simp[]) >>
  Cases_on `df_at NONE (load_analyze ctx fn) lbl n` >> simp[] >>
  `FOLDL (\a i. load_transfer ctx i a) (df_at NONE (load_analyze ctx fn) lbl 0)
    (TAKE n bb.bb_instructions) <> NONE` by
    (irule le_transfer_fold_some >> simp[]) >> gvs[]
QED
