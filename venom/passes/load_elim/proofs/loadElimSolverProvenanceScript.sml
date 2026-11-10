Theory loadElimSolverProvenance
Ancestors
  loadElimLatticeSoundHelpers loadElimDefs loadElimTransferProvenance
  loadElimConvergence
  dfAnalyzeProps dfAnalyzeDefs cfgDefs venomWf finite_map list rich_list

Theorem le_join_selected_lookup:
  b = SOME m /\
  FLOOKUP (unwrap_load_lattice (load_join a b)) k = SOME vs ==>
  ?ws. FLOOKUP m k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)
Proof
  strip_tac >> gvs[] >> Cases_on `a` >>
  gvs[load_join_def, unwrap_load_lattice_def] >>
  drule load_join_raw_lookup >> strip_tac >> gvs[] >>
  metis_tac[mem_operand_list_union]
QED

Theorem le_join_selected_lookup_left:
  a = SOME m /\
  FLOOKUP (unwrap_load_lattice (load_join a b)) k = SOME vs ==>
  ?ws. FLOOKUP m k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)
Proof
  strip_tac >> gvs[] >> Cases_on `b` >>
  gvs[load_join_def, unwrap_load_lattice_def] >>
  drule load_join_raw_lookup >> strip_tac >> gvs[] >>
  metis_tac[mem_operand_list_union]
QED

Theorem le_join_fold_lookup_acc[local]:
  !xs m vs.
  FLOOKUP (unwrap_load_lattice (FOLDL load_join (SOME m) xs)) k = SOME vs ==>
  ?ws. FLOOKUP m k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)
Proof
  Induct_on `xs` >- (simp[unwrap_load_lattice_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >>
  Cases_on `h` >> gvs[load_join_def] >>
  first_x_assum drule >> strip_tac >>
  drule load_join_raw_lookup >> strip_tac >> gvs[] >>
  metis_tac[mem_operand_list_union]
QED

Theorem le_join_fold_selected_lookup_general[local]:
  !xs a vs.
  MEM (SOME m) xs /\
  FLOOKUP (unwrap_load_lattice (FOLDL load_join a xs)) k = SOME vs ==>
  ?ws. FLOOKUP m k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)
Proof
  Induct_on `xs` >- simp[] >>
  rpt gen_tac >> simp[] >> strip_tac
  >- (gvs[] >>
      Cases_on `a` >> gvs[load_join_def] >>
      drule le_join_fold_lookup_acc >> simp[] >> strip_tac >>
      drule load_join_raw_lookup >> strip_tac >> gvs[] >>
      metis_tac[mem_operand_list_union]) >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem le_join_fold_selected_lookup:
  MEM (SOME m) xs /\
  FLOOKUP (unwrap_load_lattice (FOLDL load_join NONE xs)) k = SOME vs ==>
  ?ws. FLOOKUP m k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)
Proof
  metis_tac[le_join_fold_selected_lookup_general]
QED

Theorem le_boundary_absorbed_lookup:
  boundary = load_join boundary (SOME exit) /\
  FLOOKUP (unwrap_load_lattice boundary) k = SOME vs ==>
  ?ws. FLOOKUP exit k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)
Proof
  metis_tac[le_join_selected_lookup]
QED

Theorem le_analyze_intra_transfer[local]:
  wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  SUC n <= LENGTH bb.bb_instructions ==>
  df_at NONE (load_analyze ctx fn) lbl (SUC n) =
  load_transfer ctx (EL n bb.bb_instructions)
    (df_at NONE (load_analyze ctx fn) lbl n)
Proof
  simp[load_analyze_def] >> rpt strip_tac >>
  irule (cj 1 (SRULE [LET_THM] df_at_intra_transfer)) >>
  simp[] >> metis_tac[]
QED

Theorem le_analyze_prefix_fold:
  !n. wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  n <= LENGTH bb.bb_instructions ==>
  df_at NONE (load_analyze ctx fn) lbl n =
  FOLDL (\ll i. load_transfer ctx i ll)
    (df_at NONE (load_analyze ctx fn) lbl 0) (TAKE n bb.bb_instructions)
Proof
  Induct >- simp[] >> rpt strip_tac >>
  `df_at NONE (load_analyze ctx fn) lbl (SUC n) =
    load_transfer ctx (EL n bb.bb_instructions)
      (df_at NONE (load_analyze ctx fn) lbl n)` by
    (irule le_analyze_intra_transfer >> simp[]) >>
  `n <= LENGTH bb.bb_instructions` by simp[] >>
  first_x_assum drule_all >> strip_tac >>
  simp[TAKE_SUC, FOLDL_APPEND]
QED

Theorem le_analyze_boundary_absorbs:
  wf_function fn /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  df_boundary NONE (load_analyze ctx fn) lbl =
  load_join (df_boundary NONE (load_analyze ctx fn) lbl)
    (df_at NONE (load_analyze ctx fn) lbl (LENGTH bb.bb_instructions))
Proof
  simp[load_analyze_def] >> rpt strip_tac >>
  irule (cj 1 (SRULE [LET_THM] df_boundary_fixpoint)) >>
  simp[] >> metis_tac[le_load_analyze_fixpoint, loadElimSolverHelpersTheory.le_solver_process_def,
    load_analyze_def]
QED

Theorem le_analyze_entry_join:
  wf_function fn /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  df_at NONE (load_analyze ctx fn) lbl 0 =
  df_joined_val Forward NONE load_join load_edge_transfer ctx
    (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) (load_analyze ctx fn) lbl
Proof
  simp[load_analyze_def] >> rpt strip_tac >>
  irule (cj 1 (SRULE [LET_THM] df_at_inter_transfer)) >>
  simp[] >> metis_tac[le_load_analyze_fixpoint, loadElimSolverHelpersTheory.le_solver_process_def,
    load_analyze_def]
QED

Theorem le_empty_join_no_lookup[local]:
  FLOOKUP (unwrap_load_lattice (load_join (SOME FEMPTY) a)) k <> SOME vs
Proof
  strip_tac >> drule_at Any le_join_selected_lookup_left >> simp[]
QED

Theorem le_analyze_selected_predecessor:
  wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM pred (cfg_preds_of (cfg_analyze fn) lbl) /\
  df_boundary NONE (load_analyze ctx fn) pred = SOME m /\
  FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) lbl 0)) k = SOME vs ==>
  ?ws. FLOOKUP m k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)
Proof
  rpt strip_tac >>
  drule_all le_analyze_entry_join >> strip_tac >> gvs[] >>
  qpat_x_assum `FLOOKUP _ _ = SOME vs` mp_tac >>
  simp[df_joined_val_def, load_edge_transfer_def] >>
  Cases_on `fn_entry_label fn` >> simp[] >>
  TRY (IF_CASES_TAC >> simp[le_empty_join_no_lookup]) >>
  Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> gvs[] >>
  strip_tac >> irule le_join_fold_selected_lookup >>
  qexists `MAP (\nbr. df_boundary NONE (load_analyze ctx fn) nbr) (h::t)` >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem le_analyze_selected_exit:
  wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  df_at NONE (load_analyze ctx fn) lbl (LENGTH bb.bb_instructions) = SOME exit /\
  FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn) lbl)) k = SOME vs ==>
  ?ws. FLOOKUP exit k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)
Proof
  rpt strip_tac >> drule_all le_analyze_boundary_absorbs >>
  simp[] >> strip_tac >> irule le_boundary_absorbed_lookup >>
  metis_tac[]
QED

Theorem le_analyze_multivalue_prefix:
  wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  m <= n /\ n <= LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) lbl n)) k = SOME vs /\
  1 < LENGTH vs ==>
  FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) lbl m)) k = SOME vs
Proof
  rpt strip_tac >>
  `m <= LENGTH bb.bb_instructions` by decide_tac >>
  `df_at NONE (load_analyze ctx fn) lbl m =
   FOLDL (\ll i. load_transfer ctx i ll)
     (df_at NONE (load_analyze ctx fn) lbl 0) (TAKE m bb.bb_instructions)` by
    (irule le_analyze_prefix_fold >> simp[]) >>
  `df_at NONE (load_analyze ctx fn) lbl n =
   FOLDL (\ll i. load_transfer ctx i ll)
     (df_at NONE (load_analyze ctx fn) lbl 0) (TAKE n bb.bb_instructions)` by
    (irule le_analyze_prefix_fold >> simp[]) >>
  `TAKE n bb.bb_instructions = TAKE m bb.bb_instructions ++
     DROP m (TAKE n bb.bb_instructions)` by
    metis_tac[TAKE_DROP, TAKE_TAKE_T] >>
  gvs[] >> irule le_transfer_fold_multivalue_prefix >> metis_tac[]
QED

Theorem le_analyze_multivalue_origin:
  wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  n <= LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) lbl n)) k = SOME vs /\
  1 < LENGTH vs ==>
  FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) lbl 0)) k = SOME vs
Proof
  strip_tac >> irule le_analyze_multivalue_prefix >> simp[] >> metis_tac[]
QED

Theorem le_analyze_singleton_origin:
  wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  n <= LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) lbl n)) k = SOME [v] ==>
  (!p q. TAKE n bb.bb_instructions = p ++ q ==>
    FLOOKUP (unwrap_load_lattice
      (FOLDL (\ll i. load_transfer ctx i ll)
        (df_at NONE (load_analyze ctx fn) lbl 0) p)) k = SOME [v]) \/
  (?before inst after.
    TAKE n bb.bb_instructions = before ++ inst::after /\
    le_transfer_generates ctx inst k v /\
    !p q. after = p ++ q ==>
      FLOOKUP (unwrap_load_lattice
        (FOLDL (\ll i. load_transfer ctx i ll)
          (df_at NONE (load_analyze ctx fn) lbl 0) (before ++ inst::p))) k = SOME [v])
Proof
  rpt strip_tac >> drule_all le_analyze_prefix_fold >> strip_tac >>
  gvs[] >> drule le_transfer_fold_singleton_origin >> simp[]
QED
