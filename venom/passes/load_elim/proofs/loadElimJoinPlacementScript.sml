Theory loadElimJoinPlacement
Ancestors
  loadElimDefs loadElimStaticGeneration loadElimOccurrenceCoverage
  loadElimReachableBoundary loadElimTransferProvenance
  cfgDefs venomWf list rich_list pred_set finite_map

(* Finite paths oriented from entry to consumer, using predecessor edges. *)
Definition le_pred_path_def:
  le_pred_path cfg [] = T /\
  le_pred_path cfg [x] = T /\
  le_pred_path cfg (x::y::xs) =
    (MEM x (cfg_preds_of cfg y) /\ le_pred_path cfg (y::xs))
End

Theorem le_pred_path_snoc:
  !xs x. le_pred_path cfg (SNOC x xs) <=>
    le_pred_path cfg xs /\
    (xs = [] \/ MEM (LAST xs) (cfg_preds_of cfg x))
Proof
  Induct_on `xs` >- simp[le_pred_path_def] >>
  Cases_on `xs` >> fs[le_pred_path_def, SNOC] >> metis_tac[]
QED

Theorem le_find_join_path_aux:
  !xs visited. xs <> [] /\ le_pred_path cfg xs ==>
    MEM (find_join_block cfg visited (LAST xs)) xs \/
    find_join_block cfg visited (LAST xs) IN visited \/
    (?p. cfg_preds_of cfg (HD xs) = [p])
Proof
  Induct using SNOC_INDUCT >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `xs = []`
  >- (gvs[SNOC, le_pred_path_def] >>
      simp[Once find_join_block_def] >>
      Cases_on `x IN visited` >> simp[] >>
      Cases_on `cfg_preds_of cfg x` >> simp[] >>
      Cases_on `t` >> simp[]) >>
  gvs[le_pred_path_snoc] >>
  `HD (SNOC x xs) = HD xs` by (Cases_on `xs` >> gvs[SNOC]) >>
  simp[LAST_SNOC] >>
  Cases_on `x IN visited` >- simp[Once find_join_block_def] >>
  Cases_on `?p. cfg_preds_of cfg x = [p]`
  >- (pop_assum strip_assume_tac >>
      `p = LAST xs` by gvs[] >> gvs[] >>
      `find_join_block cfg visited x =
       find_join_block cfg (x INSERT visited) (LAST xs)` by
        simp[Once find_join_block_def] >>
      asm_rewrite_tac[] >>
      first_x_assum (qspec_then `x INSERT visited` mp_tac) >>
      simp[] >> metis_tac[]) >>
  simp[Once find_join_block_def] >>
  Cases_on `cfg_preds_of cfg x` >> simp[] >>
  Cases_on `t` >> gvs[]
QED

Theorem le_find_join_path:
  xs <> [] /\ le_pred_path cfg xs /\ visited SUBSET set xs ==>
  MEM (find_join_block cfg visited (LAST xs)) xs \/
  (?p. cfg_preds_of cfg (HD xs) = [p])
Proof
  strip_tac >> drule_all le_find_join_path_aux >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem le_find_join_path_escape:
  xs <> [] /\ le_pred_path cfg xs /\
  ~MEM (find_join_block cfg {} (LAST xs)) xs ==>
  ?p. cfg_preds_of cfg (HD xs) = [p]
Proof
  strip_tac >> drule_all le_find_join_path_aux >>
  disch_then (qspec_then `{}` mp_tac) >> simp[]
QED

Theorem le_find_join_path_placement:
  xs <> [] /\ le_pred_path cfg xs /\
  (!p. cfg_preds_of cfg (HD xs) <> [p]) ==>
  MEM (find_join_block cfg {} (LAST xs)) xs
Proof
  metis_tac[le_find_join_path_escape]
QED

Theorem le_fn_path_pred_path:
  !xs. wf_function fn /\ is_fn_path fn xs ==>
    le_pred_path (cfg_analyze fn) xs
Proof
  Induct >> simp[le_pred_path_def] >>
  Cases_on `xs` >> simp[is_fn_path_def, le_pred_path_def] >>
  metis_tac[le_static_edge_pred]
QED

Theorem le_occ_prefix_pred_route:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb ==>
  le_occ_route es <> [] /\
  le_pred_path (cfg_analyze fn) (le_occ_route es) /\
  HD (le_occ_route es) = s0.vs_current_bb /\
  LAST (le_occ_route es) = s.vs_current_bb
Proof
  metis_tac[le_occ_prefix_route, le_fn_path_pred_path]
QED

Theorem le_two_distinct_boundary_preserves:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn) bb.bb_label)) k = SOME ops /\
  MEM a ops /\ MEM b ops /\ a <> b ==>
  le_fold_preserves ctx bb.bb_instructions k
Proof
  strip_tac >>
  qspec_then `bb.bb_instructions` strip_assume_tac le_fold_lookup_classification
  >- (metis_tac[le_analyze_boundary_deleted, optionTheory.NOT_NONE_SOME]) >>
  drule_all le_analyze_boundary_constant >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem le_two_distinct_boundary_nonentry:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn) bb.bb_label)) k = SOME ops /\
  MEM a ops /\ MEM b ops /\ a <> b ==>
  fn_entry_label fn <> SOME bb.bb_label
Proof
  strip_tac >>
  `le_fold_preserves ctx bb.bb_instructions k` by
    metis_tac[le_two_distinct_boundary_preserves] >>
  metis_tac[le_analyze_boundary_entry, optionTheory.NOT_NONE_SOME]
QED

Theorem le_two_distinct_find_join_aux:
  !xs ops visited. wf_function fn /\ xs <> [] /\
  le_pred_path (cfg_analyze fn) xs /\
  EVERY (\l. ?bb. MEM bb fn.fn_blocks /\ bb.bb_label = l) xs /\
  fn_entry_label fn = SOME (HD xs) /\
  FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn) (LAST xs))) k = SOME ops /\
  MEM a ops /\ MEM b ops /\ a <> b ==>
  MEM (find_join_block (cfg_analyze fn) visited (LAST xs)) xs \/
  find_join_block (cfg_analyze fn) visited (LAST xs) IN visited
Proof
  Induct using SNOC_INDUCT >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `xs = []`
  >- (gvs[SNOC] >> metis_tac[le_two_distinct_boundary_nonentry]) >>
  gvs[le_pred_path_snoc, EVERY_SNOC] >>
  `HD (SNOC bb.bb_label xs) = HD xs` by (Cases_on `xs` >> gvs[SNOC]) >>
  Cases_on `bb.bb_label IN visited`
  >- simp[Once find_join_block_def] >>
  Cases_on `?p. cfg_preds_of (cfg_analyze fn) bb.bb_label = [p]`
  >- (pop_assum strip_assume_tac >>
      `p = LAST xs` by gvs[] >> gvs[] >>
      `le_fold_preserves ctx bb.bb_instructions k` by
        metis_tac[le_two_distinct_boundary_preserves] >>
      `fn_entry_label fn <> SOME bb.bb_label` by
        metis_tac[le_two_distinct_boundary_nonentry] >>
      drule_all le_analyze_boundary_preserving_reverse >> strip_tac >>
      `MEM a ys /\ MEM b ys` by (fs[SUBSET_DEF] >> metis_tac[]) >>
      `find_join_block (cfg_analyze fn) visited bb.bb_label =
       find_join_block (cfg_analyze fn) (bb.bb_label INSERT visited) (LAST xs)` by
        simp[Once find_join_block_def] >>
      asm_rewrite_tac[] >>
      first_x_assum (qspecl_then [`ys`, `bb.bb_label INSERT visited`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  simp[Once find_join_block_def] >>
  Cases_on `cfg_preds_of (cfg_analyze fn) bb.bb_label` >> simp[] >>
  Cases_on `t` >> gvs[]
QED

Theorem le_two_distinct_find_join:
  wf_function fn /\ xs <> [] /\ le_pred_path (cfg_analyze fn) xs /\
  EVERY (\l. ?bb. MEM bb fn.fn_blocks /\ bb.bb_label = l) xs /\
  fn_entry_label fn = SOME (HD xs) /\
  FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn) (LAST xs))) k = SOME ops /\
  MEM a ops /\ MEM b ops /\ a <> b ==>
  MEM (find_join_block (cfg_analyze fn) {} (LAST xs)) xs
Proof
  strip_tac >> drule_all le_two_distinct_find_join_aux >>
  disch_then (qspec_then `{}` mp_tac) >> simp[]
QED
