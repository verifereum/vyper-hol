Theory loadElimAllBlockPopulation
Ancestors
  loadElimDefs loadElimConvergence loadElimBoundaryProvenance
  loadElimTransferProvenance dfAnalyzeDefs dfAnalyzeProps dfAnalyzeProofs
  venomInst venomWf cfgDefs finite_map list pred_set
Libs
  pairLib

Theorem le_funion_fold_lookup_preserved[local]:
  !ls acc. FLOOKUP acc k = SOME v /\
    (!l. MEM l ls ==> FLOOKUP (f l) k = NONE \/ FLOOKUP (f l) k = SOME v) ==>
    FLOOKUP (FOLDL (\acc l. FUNION (f l) acc) acc ls) k = SOME v
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[FLOOKUP_FUNION] >>
  Cases_on `FLOOKUP (f h) k` >> simp[] >>
  first_x_assum (qspec_then `h` mp_tac) >> simp[]
QED

Theorem le_funion_fold_lookup[local]:
  !ls acc. MEM lbl ls /\ FLOOKUP (f lbl) k = SOME v /\
    (!l. MEM l ls ==> FLOOKUP (f l) k = NONE \/ FLOOKUP (f l) k = SOME v) ==>
    FLOOKUP (FOLDL (\acc l. FUNION (f l) acc) acc ls) k = SOME v
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac
  >- (gvs[] >> irule le_funion_fold_lookup_preserved >>
      simp[FLOOKUP_FUNION] >> metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem le_inst_fold_projection[local]:
  !ls st. (FOLDL (\s l. s with ds_inst := FUNION (f l) s.ds_inst) st ls).ds_inst =
    FOLDL (\acc l. FUNION (f l) acc) st.ds_inst ls
Proof
  Induct >> simp[]
QED

Theorem le_population_inst_map[local]:
  !lbls st. (df_populate_inst dir bottom join transfer edge ctx entry cfg bbs lbls st).ds_inst =
    FOLDL (\acc lbl. FUNION
      (SND (df_fold_block dir (transfer ctx) lbl
        (case lookup_block lbl bbs of NONE => [] | SOME bb => bb.bb_instructions)
        (df_joined_val dir bottom join edge ctx entry cfg st lbl))) acc) st.ds_inst lbls
Proof
  simp[df_populate_inst_def, pairTheory.ELIM_UNCURRY,
       le_inst_fold_projection]
QED

Theorem le_fold_block_other_label[local]:
  l <> lbl ==>
  FLOOKUP (SND (df_fold_block dir tr l xs init)) (lbl,n) = NONE
Proof
  strip_tac >> Cases_on `df_fold_block dir tr l xs init` >> simp[] >>
  drule df_fold_block_keys >> disch_then (qspec_then `(lbl,n)` mp_tac) >>
  Cases_on `FLOOKUP r (lbl,n)` >> simp[]
QED

Theorem le_population_lookup:
  MEM lbl lbls /\ lookup_block lbl bbs = SOME bb /\
  FLOOKUP (SND (df_fold_block dir (transfer ctx) lbl bb.bb_instructions
    (df_joined_val dir bottom join edge ctx entry cfg st lbl))) (lbl,n) = SOME v ==>
  FLOOKUP (df_populate_inst dir bottom join transfer edge ctx entry cfg bbs lbls st).ds_inst
    (lbl,n) = SOME v
Proof
  strip_tac >> simp[le_population_inst_map] >>
  ho_match_mp_tac le_funion_fold_lookup >> simp[] >>
  qx_gen_tac `l` >> strip_tac >> Cases_on `l = lbl` >> gvs[] >>
  simp[le_fold_block_other_label]
QED

Theorem le_fold_forward_prefix[local]:
  !n xs acc fv im.
  df_fold_forward tr lbl xs 0 acc FEMPTY = (fv,im) /\ n <= LENGTH xs ==>
  FLOOKUP im (lbl,n) = SOME (FOLDL (\a i. tr i a) acc (TAKE n xs))
Proof
  Induct >- (rpt strip_tac >> drule df_fold_forward_at >> simp[]) >>
  rpt strip_tac >>
  `n < LENGTH xs` by simp[] >>
  `FLOOKUP im (lbl,n) = SOME (FOLDL (\a i. tr i a) acc (TAKE n xs))` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule df_fold_forward_at >> strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[GSYM rich_listTheory.SNOC_EL_TAKE, SNOC_APPEND, rich_listTheory.FOLDL_APPEND]
QED

Theorem le_inst_fold_boundary[local]:
  !ls st. (FOLDL (\s l. s with ds_inst := f l s.ds_inst) st ls).ds_boundary = st.ds_boundary
Proof
  Induct >> simp[]
QED

Theorem le_population_joined:
  df_joined_val dir bottom join edge ctx entry cfg
    (df_populate_inst dir bottom join transfer edge ctx entry cfg bbs lbls st) lbl =
  df_joined_val dir bottom join edge ctx entry cfg st lbl
Proof
  simp[df_joined_val_def, df_boundary_def, df_populate_inst_def,
    pairTheory.ELIM_UNCURRY, le_inst_fold_boundary]
QED

Theorem le_population_forward_prefix:
  MEM lbl lbls /\ lookup_block lbl bbs = SOME bb /\ n <= LENGTH bb.bb_instructions ==>
  df_at bottom (df_populate_inst Forward bottom join transfer edge ctx entry cfg bbs lbls st) lbl n =
  FOLDL (\a i. transfer ctx i a)
    (df_joined_val Forward bottom join edge ctx entry cfg st lbl)
    (TAKE n bb.bb_instructions)
Proof
  strip_tac >> simp[df_at_def] >>
  `?fv im. df_fold_forward (transfer ctx) lbl bb.bb_instructions 0
    (df_joined_val Forward bottom join edge ctx entry cfg st lbl) FEMPTY = (fv,im)` by
    metis_tac[pairTheory.PAIR] >>
  drule_all le_fold_forward_prefix >> strip_tac >>
  `FLOOKUP (df_populate_inst Forward bottom join transfer edge ctx entry cfg bbs lbls st).ds_inst
    (lbl,n) = SOME (FOLDL (\a i. transfer ctx i a)
      (df_joined_val Forward bottom join edge ctx entry cfg st lbl) (TAKE n bb.bb_instructions))` by
    (irule le_population_lookup >> simp[df_fold_block_def] >> metis_tac[]) >> simp[]
QED

Theorem le_analyze_all_block_prefix:
  wf_function fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  n <= LENGTH bb.bb_instructions ==>
  df_at NONE (load_analyze ctx fn) lbl n =
  FOLDL (\a i. load_transfer ctx i a)
    (df_joined_val Forward NONE load_join load_edge_transfer ctx
      (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) (load_analyze ctx fn) lbl)
    (TAKE n bb.bb_instructions)
Proof
  strip_tac >>
  `MEM lbl (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (fs[lookup_block_def] >>
     drule venomExecPropsTheory.FIND_P >> simp[] >> strip_tac >>
     drule venomExecPropsTheory.FIND_MEM >> simp[MEM_MAP] >> metis_tac[]) >>
  simp_tac std_ss [load_analyze_def, df_analyze_def, LET_THM, direction_case_def] >>
  simp_tac std_ss [le_population_joined] >>
  irule le_population_forward_prefix >> simp[]
QED

Theorem le_analyze_all_block_multivalue_origin:
  wf_function fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  n <= LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) lbl n)) k = SOME ops /\
  1 < LENGTH ops ==>
  FLOOKUP (unwrap_load_lattice
    (df_joined_val Forward NONE load_join load_edge_transfer ctx
      (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) (load_analyze ctx fn) lbl)) k = SOME ops
Proof
  strip_tac >> drule_all le_analyze_all_block_prefix >> strip_tac >>
  irule le_transfer_fold_multivalue_origin >> metis_tac[]
QED
