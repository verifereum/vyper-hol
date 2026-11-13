Theory loadElimBoundaryProvenance
Ancestors
  loadElimDefs loadElimTransferProvenance loadElimOrderHelpers
  loadElimLatticeSoundHelpers loadElimSolverHelpers loadElimConvergence
  loadElimPopulation loadElimJoinProps dfAnalyzeDefs dfAnalyzeProofs
  worklistDefs worklistProofs cfgAnalysisProps venomWf venomExecProofs
  finite_map pred_set list venomInst

(* Conditional operand inclusion, with unreached predecessors kept separate. *)
Definition le_pred_lookup_rel_def:
  le_pred_lookup_rel k p b <=>
    (p = NONE ==> FLOOKUP (unwrap_load_lattice b) k = NONE) /\
    (!ys xs. FLOOKUP (unwrap_load_lattice p) k = SOME ys /\
             FLOOKUP (unwrap_load_lattice b) k = SOME xs ==>
             set xs SUBSET set ys)
End

Theorem le_pred_lookup_rel_refl:
  le_pred_lookup_rel k a a
Proof
  Cases_on `a` >> simp[le_pred_lookup_rel_def, unwrap_load_lattice_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem le_pred_lookup_rel_empty:
  FLOOKUP (unwrap_load_lattice b) k = NONE ==> le_pred_lookup_rel k a b
Proof
  simp[le_pred_lookup_rel_def]
QED

Theorem le_join_lookup_missing:
  b <> NONE /\ FLOOKUP (unwrap_load_lattice b) k = NONE ==>
  FLOOKUP (unwrap_load_lattice (load_join a b)) k = NONE
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[load_join_def, unwrap_load_lattice_def, le_join_raw_lookup_eq] >>
  Cases_on `FLOOKUP x k` >> simp[]
QED

Theorem le_pred_lookup_rel_join_right:
  le_pred_lookup_rel k p b ==> le_pred_lookup_rel k p (load_join b p)
Proof
  Cases_on `p` >> Cases_on `b` >>
  simp[load_join_def, unwrap_load_lattice_def, le_pred_lookup_rel_def,
       le_join_raw_lookup_eq] >>
  rpt strip_tac >> gvs[AllCaseEqs(), mem_operand_list_union, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem le_pred_lookup_rel_join_left:
  le_pred_lookup_rel k p b ==> le_pred_lookup_rel k (load_join p a) b
Proof
  Cases_on `p` >> Cases_on `a` >>
  simp[load_join_def, unwrap_load_lattice_def, le_pred_lookup_rel_def,
       le_join_raw_lookup_eq] >>
  rpt strip_tac >> gvs[AllCaseEqs(), mem_operand_list_union, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem le_pred_lookup_rel_join_preserving:
  le_pred_lookup_rel k p b /\ fresh <> NONE /\
  FLOOKUP (unwrap_load_lattice fresh) k = FLOOKUP (unwrap_load_lattice p) k ==>
  le_pred_lookup_rel k p (load_join b fresh)
Proof
  Cases_on `p` >> Cases_on `b` >> Cases_on `fresh` >>
  simp[load_join_def, unwrap_load_lattice_def, le_pred_lookup_rel_def,
       le_join_raw_lookup_eq] >>
  rpt strip_tac >> gvs[AllCaseEqs(), mem_operand_list_union, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem le_join_lookup_bounded:
  (!xs. FLOOKUP (unwrap_load_lattice a) k = SOME xs ==> set xs SUBSET vals) /\
  (!ys. FLOOKUP (unwrap_load_lattice b) k = SOME ys ==> set ys SUBSET vals) ==>
  !zs. FLOOKUP (unwrap_load_lattice (load_join a b)) k = SOME zs ==>
       set zs SUBSET vals
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[load_join_def, unwrap_load_lattice_def, le_join_raw_lookup_eq] >>
  rpt strip_tac >> gvs[AllCaseEqs(), mem_operand_list_union, SUBSET_DEF] >>
  metis_tac[]
QED

Definition le_boundary_provenance_def:
  le_boundary_provenance ctx fn st <=>
    !bb k. MEM bb fn.fn_blocks ==>
      (!v xs. le_fold_constant ctx bb.bb_instructions k v /\
        FLOOKUP (unwrap_load_lattice (df_boundary NONE st bb.bb_label)) k = SOME xs ==>
        set xs SUBSET {v}) /\
      (le_fold_deletes ctx bb.bb_instructions k ==>
        FLOOKUP (unwrap_load_lattice (df_boundary NONE st bb.bb_label)) k = NONE) /\
      (!p. fn_entry_label fn <> SOME bb.bb_label /\
        cfg_preds_of (cfg_analyze fn) bb.bb_label = [p] /\
        le_fold_preserves ctx bb.bb_instructions k ==>
        le_pred_lookup_rel k (df_boundary NONE st p)
          (df_boundary NONE st bb.bb_label)) /\
      (fn_entry_label fn = SOME bb.bb_label /\
        le_fold_preserves ctx bb.bb_instructions k ==>
        FLOOKUP (unwrap_load_lattice (df_boundary NONE st bb.bb_label)) k = NONE)
End

Theorem le_boundary_provenance_empty:
  (!lbl k. FLOOKUP (unwrap_load_lattice (df_boundary NONE st lbl)) k = NONE) ==>
  le_boundary_provenance ctx fn st
Proof
  simp[le_boundary_provenance_def, le_pred_lookup_rel_def]
QED

Theorem le_init_boundary_none:
  df_boundary NONE (init_df_state NONE labels) lbl = NONE
Proof
  simp[df_boundary_def, init_df_state_def] >>
  Cases_on `FLOOKUP (FOLDL (\m l. m |+ (l,NONE)) FEMPTY labels) lbl` >>
  simp[] >> drule foldl_fempty_val >> simp[]
QED

Theorem le_boundary_update:
  df_boundary NONE (st with ds_boundary := st.ds_boundary |+ (lbl,v)) other =
    if other = lbl then v else df_boundary NONE st other
Proof
  simp[df_boundary_def, FLOOKUP_UPDATE] >> IF_CASES_TAC >> simp[]
QED

Theorem le_boundary_provenance_init:
  le_boundary_provenance ctx fn
    (case fn_entry_label fn of
       NONE => init_df_state NONE (fn_labels fn)
     | SOME lbl => (init_df_state NONE (fn_labels fn)) with
         ds_boundary := (init_df_state NONE (fn_labels fn)).ds_boundary |+
           (lbl, SOME FEMPTY))
Proof
  irule le_boundary_provenance_empty >>
  Cases_on `fn_entry_label fn` >>
  simp[le_init_boundary_none, unwrap_load_lattice_def] >>
  map_every qx_gen_tac [`lbl`, `k`] >> Cases_on `lbl = x` >>
  simp[le_boundary_update, le_init_boundary_none, unwrap_load_lattice_def]
QED

Theorem le_fold_forward_fst:
  !xs idx acc im.
    FST (df_fold_forward transfer lbl xs idx acc im) =
      FOLDL (\a i. transfer i a) acc xs
Proof
  Induct >> simp[df_fold_forward_def]
QED

Theorem le_process_boundary:
  df_boundary NONE (le_solver_process ctx fn lbl st) other =
    if other = lbl then
      load_join (df_boundary NONE st lbl)
        (FOLDL (\a i. load_transfer ctx i a)
          (df_joined_val Forward NONE load_join load_edge_transfer ctx
            (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
            (cfg_analyze fn) st lbl)
          (case lookup_block lbl fn.fn_blocks of
             NONE => [] | SOME bb => bb.bb_instructions))
    else df_boundary NONE st other
Proof
  simp[le_solver_process_def, df_process_block_def] >>
  pairarg_tac >> simp[] >>
  `final_val = FOLDL (\a i. load_transfer ctx i a)
    (df_joined_val Forward NONE load_join load_edge_transfer ctx
      (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) st lbl)
    (case lookup_block lbl fn.fn_blocks of
       NONE => [] | SOME bb => bb.bb_instructions)` by
    (fs[df_fold_block_def] >>
     metis_tac[le_fold_forward_fst, pairTheory.FST]) >>
  IF_CASES_TAC >> simp[le_boundary_update] >>
  Cases_on `other = lbl` >> gvs[]
QED

Theorem le_joined_sole_pred:
  fn_entry_label fn <> SOME lbl /\
  cfg_preds_of (cfg_analyze fn) lbl = [p] ==>
  df_joined_val Forward NONE load_join load_edge_transfer ctx
    (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) st lbl = df_boundary NONE st p
Proof
  strip_tac >> Cases_on `fn_entry_label fn` >>
  gvs[df_joined_val_def, load_edge_transfer_def, load_join_def]
QED

Theorem le_joined_entry_missing:
  fn_entry_label fn = SOME lbl ==>
  FLOOKUP (unwrap_load_lattice
    (df_joined_val Forward NONE load_join load_edge_transfer ctx
      (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) st lbl)) k = NONE
Proof
  strip_tac >> simp[df_joined_val_def, load_edge_transfer_def] >>
  Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >>
  simp[unwrap_load_lattice_def] >>
  Cases_on `FOLDL load_join (df_boundary NONE st h)
    (MAP (\nbr. df_boundary NONE st nbr) t)` >>
  simp[load_join_def, unwrap_load_lattice_def, le_join_raw_lookup_eq]
QED

Theorem le_process_boundary_block:
  wf_function fn /\ MEM bb fn.fn_blocks ==>
  df_boundary NONE (le_solver_process ctx fn bb.bb_label st) other =
    if other = bb.bb_label then
      load_join (df_boundary NONE st bb.bb_label)
        (FOLDL (\a i. load_transfer ctx i a)
          (df_joined_val Forward NONE load_join load_edge_transfer ctx
            (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
            (cfg_analyze fn) st bb.bb_label) bb.bb_instructions)
    else df_boundary NONE st other
Proof
  strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  simp[le_process_boundary]
QED

Theorem le_process_constant_bound:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  le_boundary_provenance ctx fn st /\
  le_fold_constant ctx bb.bb_instructions k v ==>
  !xs. FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (le_solver_process ctx fn lbl st) bb.bb_label)) k = SOME xs ==>
    set xs SUBSET {v}
Proof
  rpt strip_tac >> Cases_on `lbl = bb.bb_label`
  >- (gvs[] >> drule_all le_process_boundary_block >>
      disch_then (qspecl_then [`st`, `bb.bb_label`, `ctx`] mp_tac) >> simp[] >>
      disch_then SUBST_ALL_TAC >>
      irule le_join_lookup_bounded >>
      goal_assum (drule_at Any) >> conj_tac
      >- metis_tac[le_boundary_provenance_def] >>
      gvs[le_fold_constant_def]) >>
  gvs[le_process_boundary] >> metis_tac[le_boundary_provenance_def]
QED

Theorem le_wf_block_fold_some:
  wf_function fn /\ MEM bb fn.fn_blocks ==>
  FOLDL (\a i. load_transfer ctx i a) input bb.bb_instructions <> NONE
Proof
  strip_tac >> irule le_transfer_nonempty_fold_some >>
  gvs[wf_function_def, bb_well_formed_def, EVERY_MEM] >> metis_tac[]
QED

Theorem le_process_deleted_missing:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  le_boundary_provenance ctx fn st /\
  le_fold_deletes ctx bb.bb_instructions k ==>
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (le_solver_process ctx fn lbl st) bb.bb_label)) k = NONE
Proof
  strip_tac >> Cases_on `lbl = bb.bb_label`
  >- (gvs[] >> drule_all le_process_boundary_block >>
      disch_then (qspecl_then [`st`, `bb.bb_label`, `ctx`] mp_tac) >> simp[] >>
      disch_then SUBST1_TAC >> irule le_join_lookup_missing >>
      conj_tac >- metis_tac[le_wf_block_fold_some] >>
      gvs[le_fold_deletes_def]) >>
  gvs[le_process_boundary] >> metis_tac[le_boundary_provenance_def]
QED

Theorem le_process_entry_missing:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  le_boundary_provenance ctx fn st /\
  fn_entry_label fn = SOME bb.bb_label /\
  le_fold_preserves ctx bb.bb_instructions k ==>
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (le_solver_process ctx fn lbl st) bb.bb_label)) k = NONE
Proof
  strip_tac >> Cases_on `lbl = bb.bb_label`
  >- (gvs[] >> drule_all le_process_boundary_block >>
      disch_then (qspecl_then [`st`, `bb.bb_label`, `ctx`] mp_tac) >> simp[] >>
      disch_then SUBST1_TAC >> irule le_join_lookup_missing >>
      conj_tac >- metis_tac[le_wf_block_fold_some] >>
      drule le_joined_entry_missing >>
      simp[] >> strip_tac >> gvs[le_fold_preserves_def]) >>
  gvs[le_process_boundary] >> metis_tac[le_boundary_provenance_def]
QED

Theorem le_process_preserving_pred:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  le_boundary_provenance ctx fn st /\
  fn_entry_label fn <> SOME bb.bb_label /\
  cfg_preds_of (cfg_analyze fn) bb.bb_label = [p] /\
  le_fold_preserves ctx bb.bb_instructions k ==>
  le_pred_lookup_rel k
    (df_boundary NONE (le_solver_process ctx fn lbl st) p)
    (df_boundary NONE (le_solver_process ctx fn lbl st) bb.bb_label)
Proof
  strip_tac >> Cases_on `p = bb.bb_label`
  >- simp[le_pred_lookup_rel_refl] >>
  `le_pred_lookup_rel k (df_boundary NONE st p)
      (df_boundary NONE st bb.bb_label)` by
    metis_tac[le_boundary_provenance_def] >>
  Cases_on `lbl = bb.bb_label`
  >- (gvs[] >> drule_all le_process_boundary_block >>
      disch_then (qspecl_then [`st`, `bb.bb_label`, `ctx`] mp_tac) >> simp[] >>
      disch_then SUBST1_TAC >>
      simp[le_process_boundary] >>
      irule le_pred_lookup_rel_join_preserving >>
      simp[] >> conj_tac >- metis_tac[le_wf_block_fold_some] >>
      drule_all le_joined_sole_pred >>
      disch_then (qspecl_then [`st`, `ctx`] mp_tac) >>
      gvs[le_fold_preserves_def]) >>
  simp[le_process_boundary] >> Cases_on `p = lbl` >>
  gvs[le_pred_lookup_rel_join_left]
QED

Theorem le_boundary_provenance_process:
  wf_function fn /\ le_boundary_provenance ctx fn st ==>
  le_boundary_provenance ctx fn (le_solver_process ctx fn lbl st)
Proof
  strip_tac >> simp[le_boundary_provenance_def] >>
  map_every qx_gen_tac [`bb`, `k`] >> strip_tac >>
  rpt conj_tac
  >- metis_tac[le_process_constant_bound]
  >- metis_tac[le_process_deleted_missing]
  >- metis_tac[le_process_preserving_pred] >>
  metis_tac[le_process_entry_missing]
QED

Theorem le_bounded_measure_conj[local]:
  bounded_measure P leq m b ==>
  bounded_measure (\x. P x /\ Q x) leq m b
Proof
  simp[latticeDefsTheory.bounded_measure_def] >> metis_tac[]
QED

Theorem le_solver_iterate_provenance:
  wf_function fn ==>
  (\st. le_solver_inv (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
           (le_generated_operands (fn_insts fn)) st /\
         le_boundary_provenance ctx fn st)
    (SND (wl_iterate
      (\lbl old new. df_boundary NONE new lbl <> df_boundary NONE old lbl)
      (le_solver_process ctx fn) (cfg_succs_of (cfg_analyze fn))
      (cfg_analyze fn).cfg_dfs_pre
      (case fn_entry_label fn of
         NONE => init_df_state NONE (fn_labels fn)
       | SOME lbl => (init_df_state NONE (fn_labels fn)) with
           ds_boundary := (init_df_state NONE (fn_labels fn)).ds_boundary |+
             (lbl, SOME FEMPTY))))
Proof
  strip_tac >> irule wl_iterate_invariant >>
  simp[le_boundary_provenance_init, le_solver_entry_init, le_process_changed] >>
  conj_tac >- metis_tac[le_solver_process_closed, le_boundary_provenance_process] >>
  qexistsl [
    `CARD (set (fn_labels fn)) *
      (1 + CARD (le_generated_keys ctx (fn_insts fn)) *
        (CARD (le_generated_operands (fn_insts fn)) + 1))`,
    `le_solver_leq`,
    `le_solver_rank (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
      (le_generated_operands (fn_insts fn))`] >>
  conj_tac >- simp[le_solver_process_inflationary] >>
  irule le_bounded_measure_conj >> irule le_solver_bounded_measure >> simp[]
QED

Theorem le_boundary_provenance_ext:
  (!lbl. df_boundary NONE st1 lbl = df_boundary NONE st2 lbl) ==>
  (le_boundary_provenance ctx fn st1 <=> le_boundary_provenance ctx fn st2)
Proof
  simp[le_boundary_provenance_def]
QED

Theorem le_boundary_provenance_populate:
  le_boundary_provenance ctx fn
    (df_populate_inst dir bottom join transfer edge ctx0 entry cfg bbs lbls st) <=>
  le_boundary_provenance ctx fn st
Proof
  irule le_boundary_provenance_ext >>
  simp[df_boundary_def, le_populate_boundary]
QED

Theorem le_analyze_boundary_provenance:
  wf_function fn ==> le_boundary_provenance ctx fn (load_analyze ctx fn)
Proof
  strip_tac >> drule le_solver_iterate_provenance >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `le_boundary_provenance _ _ _` mp_tac >>
  simp[load_analyze_def, df_analyze_def, le_solver_process_def] >>
  Cases_on `fn_entry_label fn` >>
  simp[fn_labels_def, le_boundary_provenance_populate]
QED

Theorem le_boundary_provenance_constant:
  le_boundary_provenance ctx fn st /\ MEM bb fn.fn_blocks /\
  le_fold_constant ctx bb.bb_instructions k v /\
  FLOOKUP (unwrap_load_lattice (df_boundary NONE st bb.bb_label)) k = SOME xs ==>
  set xs SUBSET {v}
Proof
  metis_tac[le_boundary_provenance_def]
QED

Theorem le_boundary_provenance_deleted:
  le_boundary_provenance ctx fn st /\ MEM bb fn.fn_blocks /\
  le_fold_deletes ctx bb.bb_instructions k ==>
  FLOOKUP (unwrap_load_lattice (df_boundary NONE st bb.bb_label)) k = NONE
Proof
  metis_tac[le_boundary_provenance_def]
QED

Theorem le_boundary_provenance_pred:
  le_boundary_provenance ctx fn st /\ MEM bb fn.fn_blocks /\
  fn_entry_label fn <> SOME bb.bb_label /\
  cfg_preds_of (cfg_analyze fn) bb.bb_label = [p] /\
  le_fold_preserves ctx bb.bb_instructions k ==>
  le_pred_lookup_rel k (df_boundary NONE st p) (df_boundary NONE st bb.bb_label)
Proof
  metis_tac[le_boundary_provenance_def]
QED

Theorem le_boundary_provenance_entry:
  le_boundary_provenance ctx fn st /\ MEM bb fn.fn_blocks /\
  fn_entry_label fn = SOME bb.bb_label /\
  le_fold_preserves ctx bb.bb_instructions k ==>
  FLOOKUP (unwrap_load_lattice (df_boundary NONE st bb.bb_label)) k = NONE
Proof
  metis_tac[le_boundary_provenance_def]
QED

Theorem le_boundary_preserving_reverse:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  le_boundary_provenance ctx fn st /\
  fn_entry_label fn <> SOME bb.bb_label /\
  cfg_preds_of (cfg_analyze fn) bb.bb_label = [p] /\
  le_fold_preserves ctx bb.bb_instructions k /\
  df_boundary NONE (le_solver_process ctx fn bb.bb_label st) bb.bb_label =
    df_boundary NONE st bb.bb_label /\
  FLOOKUP (unwrap_load_lattice (df_boundary NONE st bb.bb_label)) k = SOME xs ==>
  ?ys. FLOOKUP (unwrap_load_lattice (df_boundary NONE st p)) k = SOME ys /\
       set xs SUBSET set ys
Proof
  strip_tac >>
  `le_pred_lookup_rel k (df_boundary NONE st p) (df_boundary NONE st bb.bb_label)` by
    metis_tac[le_boundary_provenance_pred] >>
  `df_boundary NONE st p <> NONE` by
    (gvs[le_pred_lookup_rel_def] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  Cases_on `FLOOKUP (unwrap_load_lattice (df_boundary NONE st p)) k`
  >- (drule_all le_process_boundary_block >>
      disch_then (qspecl_then [`st`, `bb.bb_label`, `ctx`] mp_tac) >> simp[] >>
      strip_tac >>
      `FLOOKUP (unwrap_load_lattice
        (FOLDL (\a i. load_transfer ctx i a)
          (df_joined_val Forward NONE load_join load_edge_transfer ctx
            (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
            (cfg_analyze fn) st bb.bb_label) bb.bb_instructions)) k = NONE` by
        (drule_all le_joined_sole_pred >>
         disch_then (qspecl_then [`st`, `ctx`] mp_tac) >>
         gvs[le_fold_preserves_def]) >>
      `FLOOKUP (unwrap_load_lattice (df_boundary NONE st bb.bb_label)) k = NONE` by
        metis_tac[le_join_lookup_missing, le_wf_block_fold_some] >> gvs[]) >>
  gvs[le_pred_lookup_rel_def]
QED
