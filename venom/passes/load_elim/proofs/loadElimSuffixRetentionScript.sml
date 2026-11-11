Theory loadElimSuffixRetention
Ancestors
  loadElimJoinPlacement loadElimReachableBoundary loadElimSolverProvenance
  loadElimDefs loadElimTransferProvenance cfgDefs venomWf
  list rich_list pred_set finite_map

(* Reverse a sole-predecessor suffix up to its latest selected join.
   Lists may grow at each predecessor boundary. *)
Theorem le_find_join_suffix_boundaries:
  !post ops visited.
  wf_function fn /\
  le_pred_path (cfg_analyze fn) (j::post) /\
  EVERY (\l. ?bb. MEM bb fn.fn_blocks /\ bb.bb_label = l) (j::post) /\
  ~MEM j post /\
  find_join_block (cfg_analyze fn) visited (LAST (j::post)) = j /\
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) (LAST (j::post)))) k = SOME ops /\
  MEM a ops /\ MEM b ops /\ a <> b ==>
  !l. MEM l (j::post) ==>
    ?vs. FLOOKUP (unwrap_load_lattice
      (df_boundary NONE (load_analyze ctx fn) l)) k = SOME vs /\
      MEM a vs /\ MEM b vs
Proof
  Induct using SNOC_INDUCT
  >- (simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `j::SNOC x post = SNOC x (j::post)` by simp[] >>
  `le_pred_path (cfg_analyze fn) (j::post) /\
   MEM (LAST (j::post)) (cfg_preds_of (cfg_analyze fn) x)` by
    metis_tac[le_pred_path_snoc, NOT_CONS_NIL] >>
  `LAST (j::SNOC x post) = x` by metis_tac[LAST_SNOC] >>
  qpat_x_assum `j::SNOC x post = _` kall_tac >>
  fs[EVERY_SNOC] >>
  `?endbb. MEM endbb fn.fn_blocks /\ endbb.bb_label = x` by metis_tac[] >>
  `fn_entry_label fn <> SOME endbb.bb_label` by
    metis_tac[le_two_distinct_boundary_nonentry] >>
  `le_fold_preserves ctx endbb.bb_instructions k` by
    metis_tac[le_two_distinct_boundary_preserves] >>
  `~(endbb.bb_label IN visited)` by
    (strip_tac >>
     `x IN visited` by metis_tac[] >>
     qpat_x_assum `find_join_block _ visited _ = j` mp_tac >>
     simp[Once find_join_block_def]) >>
  `x NOTIN visited` by metis_tac[] >>
  `cfg_preds_of (cfg_analyze fn) x = [LAST (j::post)]` by
    (qpat_x_assum `find_join_block _ visited _ = j` mp_tac >>
     simp[Once find_join_block_def] >>
     Cases_on `cfg_preds_of (cfg_analyze fn) x` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  `?ys. FLOOKUP (unwrap_load_lattice
     (df_boundary NONE (load_analyze ctx fn) (LAST (j::post)))) k = SOME ys /\
     set ops SUBSET set ys` by
    (irule le_analyze_boundary_preserving_reverse >>
     metis_tac[]) >>
  `MEM a ys /\ MEM b ys` by (fs[SUBSET_DEF] >> metis_tac[]) >>
  `find_join_block (cfg_analyze fn) (endbb.bb_label INSERT visited)
      (LAST (j::post)) = j` by
    (qpat_x_assum `find_join_block _ visited _ = j` mp_tac >>
     simp[Once find_join_block_def]) >>
  first_x_assum (qspecl_then [`ys`, `endbb.bb_label INSERT visited`] mp_tac) >>
  simp[] >> metis_tac[]
QED
