Theory loadElimActionJoinInput
Ancestors
  loadElimDefs loadElimJoinInputProvenance loadElimBoundaryProvenance
  loadElimPhiCapture loadElimInitialEntryActions loadElimOrderHelpers
  loadElimOriginHelpers dfAnalyzeDefs cfgDefs finite_map pred_set list

Theorem le_join_key_present:
  FLOOKUP (unwrap_load_lattice a) k = SOME xs /\
  FLOOKUP (unwrap_load_lattice b) k = SOME ys ==>
  ?zs. FLOOKUP (unwrap_load_lattice (load_join a b)) k = SOME zs
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[unwrap_load_lattice_def, load_join_def, le_join_raw_lookup_eq]
QED

Theorem le_join_fold_key_present:
  !ls acc. (?xs. FLOOKUP (unwrap_load_lattice acc) k = SOME xs) /\
    EVERY (\a. ?xs. FLOOKUP (unwrap_load_lattice a) k = SOME xs) ls ==>
    ?xs. FLOOKUP (unwrap_load_lattice (FOLDL load_join acc ls)) k = SOME xs
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[] >> metis_tac[le_join_key_present]
QED

Theorem le_compute_action_join_input:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  le_fold_preserves ctx bb.bb_instructions k /\
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) bb.bb_label)) k = SOME xs /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) k lbl inst = SOME pa /\
  pa.pa_join_lbl = bb.bb_label ==>
  ?ys. FLOOKUP (unwrap_load_lattice
    (df_joined_val Forward NONE load_join load_edge_transfer ctx
      (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) (load_analyze ctx fn) bb.bb_label)) k = SOME ys /\
    set xs SUBSET set ys
Proof
  strip_tac >> drule_all le_analyze_preserving_join_input >> strip_tac >>
  `fn_entry_label fn <> SOME bb.bb_label` by
    (strip_tac >> drule le_analyze_boundary_provenance >>
     disch_then (qspec_then `ctx` assume_tac) >>
     drule_all le_boundary_provenance_entry >> simp[]) >>
  `!p. MEM p (cfg_preds_of (cfg_analyze fn) bb.bb_label) ==>
    ?v. FLOOKUP (unwrap_load_lattice
      (df_boundary NONE (load_analyze ctx fn) p)) k = SOME [Var v]` by
    (metis_tac[le_compute_phi_action_selected]) >>
  `cfg_preds_of (cfg_analyze fn) bb.bb_label <> []` by
    (strip_tac >>
     qpat_x_assum `le_pred_lookup_rel _ _ _` mp_tac >>
     simp[df_joined_val_def, load_edge_transfer_def] >>
     Cases_on `fn_entry_label fn` >>
     gvs[le_pred_lookup_rel_def]) >>
  `?ys. FLOOKUP (unwrap_load_lattice
    (df_joined_val Forward NONE load_join load_edge_transfer ctx
      (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) (load_analyze ctx fn) bb.bb_label)) k = SOME ys` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) bb.bb_label` >> gvs[] >>
     simp[df_joined_val_def, load_edge_transfer_def, load_join_def] >>
     Cases_on `fn_entry_label fn` >> gvs[] >>
     irule le_join_fold_key_present >> simp[EVERY_MAP, EVERY_MEM] >>
     metis_tac[]) >>
  gvs[le_pred_lookup_rel_def] >> metis_tac[]
QED
