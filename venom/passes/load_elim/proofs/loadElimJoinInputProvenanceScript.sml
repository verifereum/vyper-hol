Theory loadElimJoinInputProvenance
Ancestors
  loadElimDefs loadElimBoundaryProvenance loadElimJoinInputContext
  loadElimSolverHelpers loadElimOrderHelpers loadElimConvergence
  loadElimTransferProvenance loadElimPopulation
  dfAnalyzeDefs dfAnalyzeProofs worklistDefs worklistProofs latticeDefs
  cfgAnalysisProps venomWf venomInst finite_map pred_set list

Definition le_join_input_provenance_def:
  le_join_input_provenance ctx fn st <=>
    !bb k. MEM bb fn.fn_blocks /\
      le_fold_preserves ctx bb.bb_instructions k ==>
      le_pred_lookup_rel k
        (df_joined_val Forward NONE load_join load_edge_transfer ctx
          (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
          (cfg_analyze fn) st bb.bb_label)
        (df_boundary NONE st bb.bb_label)
End

Theorem le_join_input_provenance_empty:
  (!lbl k. FLOOKUP (unwrap_load_lattice (df_boundary NONE st lbl)) k = NONE) ==>
  le_join_input_provenance ctx fn st
Proof
  simp[le_join_input_provenance_def, le_pred_lookup_rel_empty]
QED

Theorem le_join_input_provenance_init:
  le_join_input_provenance ctx fn
    (case fn_entry_label fn of
       NONE => init_df_state NONE (fn_labels fn)
     | SOME lbl => (init_df_state NONE (fn_labels fn)) with
         ds_boundary := (init_df_state NONE (fn_labels fn)).ds_boundary |+
           (lbl, SOME FEMPTY))
Proof
  irule le_join_input_provenance_empty >>
  Cases_on `fn_entry_label fn` >>
  simp[le_init_boundary_none, unwrap_load_lattice_def] >>
  map_every qx_gen_tac [`lbl`, `k`] >> Cases_on `lbl = x` >>
  simp[le_boundary_update, le_init_boundary_none, unwrap_load_lattice_def]
QED

(* First change the output, holding the old input fixed. The next theorem
   transports that relation to the new input, including simultaneous self edges. *)
Theorem le_process_preserving_old_input:
  wf_function fn /\ le_join_input_provenance ctx fn st /\
  MEM bb fn.fn_blocks /\ le_fold_preserves ctx bb.bb_instructions k ==>
  le_pred_lookup_rel k
    (df_joined_val Forward NONE load_join load_edge_transfer ctx
      (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) st bb.bb_label)
    (df_boundary NONE (le_solver_process ctx fn lbl st) bb.bb_label)
Proof
  strip_tac >>
  `le_pred_lookup_rel k
    (df_joined_val Forward NONE load_join load_edge_transfer ctx
      (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) st bb.bb_label)
    (df_boundary NONE st bb.bb_label)` by
      metis_tac[le_join_input_provenance_def] >>
  Cases_on `lbl = bb.bb_label`
  >- (gvs[] >> drule_all le_process_boundary_block >>
      disch_then (qspecl_then [`st`, `bb.bb_label`, `ctx`] mp_tac) >> simp[] >>
      disch_then SUBST1_TAC >>
      irule le_pred_lookup_rel_join_preserving >>
      simp[] >> conj_tac >- metis_tac[le_wf_block_fold_some] >>
      gvs[le_fold_preserves_def]) >>
  simp[le_process_boundary]
QED

Theorem le_join_input_provenance_process:
  wf_function fn /\ le_join_input_provenance ctx fn st ==>
  le_join_input_provenance ctx fn (le_solver_process ctx fn lbl st)
Proof
  strip_tac >> simp[le_join_input_provenance_def] >>
  map_every qx_gen_tac [`bb`, `k`] >> strip_tac >>
  irule le_joined_input_boundary_accumulate >>
  qexistsl [
    `FOLDL (\a i. load_transfer ctx i a)
      (df_joined_val Forward NONE load_join load_edge_transfer ctx
        (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
        (cfg_analyze fn) st lbl)
      (case lookup_block lbl fn.fn_blocks of
         NONE => [] | SOME bb => bb.bb_instructions)`, `lbl`, `st`] >>
  conj_tac >- simp[le_process_boundary] >>
  irule le_process_preserving_old_input >> simp[]
QED

Theorem le_join_input_provenance_ext:
  (!lbl. df_boundary NONE st1 lbl = df_boundary NONE st2 lbl) ==>
  (le_join_input_provenance ctx fn st1 <=> le_join_input_provenance ctx fn st2)
Proof
  strip_tac >> simp[le_join_input_provenance_def, df_joined_val_def]
QED

Theorem le_join_input_provenance_populate:
  le_join_input_provenance ctx fn
    (df_populate_inst dir bottom join transfer edge ctx0 entry cfg bbs lbls st) <=>
  le_join_input_provenance ctx fn st
Proof
  irule le_join_input_provenance_ext >>
  simp[df_boundary_def, le_populate_boundary]
QED

Theorem le_join_input_bounded_measure_conj[local]:
  bounded_measure P leq m b ==>
  bounded_measure (\x. P x /\ Q x) leq m b
Proof
  simp[bounded_measure_def] >> metis_tac[]
QED

Theorem le_solver_iterate_join_input:
  wf_function fn ==>
  (\st. le_solver_inv (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
           (le_generated_operands (fn_insts fn)) st /\
         le_join_input_provenance ctx fn st)
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
  strip_tac >> irule wl_iterate_invariant_proof >>
  simp[le_join_input_provenance_init, le_solver_entry_init, le_process_changed] >>
  conj_tac >- metis_tac[le_solver_process_closed, le_join_input_provenance_process] >>
  qexistsl [
    `CARD (set (fn_labels fn)) *
      (1 + CARD (le_generated_keys ctx (fn_insts fn)) *
        (CARD (le_generated_operands (fn_insts fn)) + 1))`,
    `le_solver_leq`,
    `le_solver_rank (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
      (le_generated_operands (fn_insts fn))`] >>
  conj_tac >- simp[le_solver_process_inflationary] >>
  irule le_join_input_bounded_measure_conj >>
  irule le_solver_bounded_measure >> simp[]
QED

Theorem le_analyze_join_input_provenance:
  wf_function fn ==> le_join_input_provenance ctx fn (load_analyze ctx fn)
Proof
  strip_tac >> drule le_solver_iterate_join_input >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `le_join_input_provenance _ _ _` mp_tac >>
  simp[load_analyze_def, df_analyze_def, le_solver_process_def] >>
  Cases_on `fn_entry_label fn` >>
  simp[fn_labels_def, le_join_input_provenance_populate]
QED

Theorem le_analyze_preserving_join_input:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  le_fold_preserves ctx bb.bb_instructions k ==>
  le_pred_lookup_rel k
    (df_joined_val Forward NONE load_join load_edge_transfer ctx
      (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) (load_analyze ctx fn) bb.bb_label)
    (df_boundary NONE (load_analyze ctx fn) bb.bb_label)
Proof
  metis_tac[le_analyze_join_input_provenance, le_join_input_provenance_def]
QED
