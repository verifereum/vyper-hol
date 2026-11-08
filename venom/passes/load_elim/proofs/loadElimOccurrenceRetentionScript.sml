Theory loadElimOccurrenceRetention
Ancestors
  loadElimSuffixRetention loadElimActionJoinInput loadElimAllBlockPopulation
  loadElimTransferProvenance loadElimJoinPlacement venomExecProps venomWf venomInst
  loadElimDefs list rich_list finite_map pred_set

Theorem le_distinct_members_length:
  MEM a xs /\ MEM b xs /\ a <> b ==> 1 < LENGTH xs
Proof
  Cases_on `xs` >> simp[] >> Cases_on `t` >> simp[] >> metis_tac[]
QED

Theorem le_preserving_block_input_retention:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  le_fold_preserves ctx bb.bb_instructions k /\
  FLOOKUP (unwrap_load_lattice
    (df_joined_val Forward NONE load_join load_edge_transfer ctx
      (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) (load_analyze ctx fn) bb.bb_label)) k = SOME ys /\
  1 < LENGTH ys ==>
  !n. n <= LENGTH bb.bb_instructions ==>
    FLOOKUP (unwrap_load_lattice
      (df_at NONE (load_analyze ctx fn) bb.bb_label n)) k = SOME ys
Proof
  rpt strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def] >>
  drule_all le_analyze_all_block_prefix >>
  disch_then (qspec_then `ctx` SUBST1_TAC) >>
  irule le_transfer_fold_multivalue_prefix >>
  conj_tac >- simp[] >>
  qexists_tac `DROP n bb.bb_instructions` >>
  simp[TAKE_DROP, le_fold_preserves_lookup]
QED

(* A full capture block: its accumulated boundary supplies alternatives,
   and actual action selection turns conditional provenance into presence. *)
Theorem le_action_capture_block_retention:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) bb.bb_label)) k = SOME xs /\
  MEM a xs /\ MEM b xs /\ a <> b /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) k lbl inst = SOME pa /\
  pa.pa_join_lbl = bb.bb_label ==>
  ?ys. 1 < LENGTH ys /\
    !n. n <= LENGTH bb.bb_instructions ==>
      FLOOKUP (unwrap_load_lattice
        (df_at NONE (load_analyze ctx fn) bb.bb_label n)) k = SOME ys
Proof
  strip_tac >>
  `le_fold_preserves ctx bb.bb_instructions k` by
    metis_tac[le_two_distinct_boundary_preserves] >>
  drule_all le_compute_action_join_input >> strip_tac >>
  `MEM a ys /\ MEM b ys` by (fs[SUBSET_DEF] >> metis_tac[]) >>
  `1 < LENGTH ys` by metis_tac[le_distinct_members_length] >>
  qexists_tac `ys` >> simp[] >>
  metis_tac[le_preserving_block_input_retention]
QED

Theorem le_find_join_suffix_predecessor:
  !post visited. le_pred_path cfg (j::post) /\ ~MEM j post /\
    find_join_block cfg visited (LAST (j::post)) = j ==>
    !l. MEM l post ==> ?q. MEM q (j::post) /\ cfg_preds_of cfg l = [q]
Proof
  Induct using SNOC_INDUCT >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `j::SNOC x post = SNOC x (j::post)` by simp[] >>
  `le_pred_path cfg (j::post) /\
   MEM (LAST (j::post)) (cfg_preds_of cfg x)` by
    metis_tac[le_pred_path_snoc, NOT_CONS_NIL] >>
  `LAST (j::SNOC x post) = x` by metis_tac[LAST_SNOC] >>
  qpat_x_assum `j::SNOC x post = _` kall_tac >>
  fs[MEM_SNOC] >>
  `x NOTIN visited` by
    (strip_tac >> qpat_x_assum `find_join_block _ visited _ = j` mp_tac >>
     simp[Once find_join_block_def]) >>
  `cfg_preds_of cfg x = [LAST (j::post)]` by
    (qpat_x_assum `find_join_block _ visited _ = j` mp_tac >>
     simp[Once find_join_block_def] >>
     Cases_on `cfg_preds_of cfg x` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  `find_join_block cfg (x INSERT visited) (LAST (j::post)) = j` by
    (qpat_x_assum `find_join_block _ visited _ = j` mp_tac >>
     simp[Once find_join_block_def]) >>
  first_x_assum (qspec_then `x INSERT visited` mp_tac) >>
  simp[] >> strip_tac >> qx_gen_tac `l` >> strip_tac
  >- (qexists_tac `LAST (j::post)` >> simp[] >>
      qspec_then `j::post` mp_tac LAST_MEM >> simp[] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >> qexists_tac `q` >> simp[]
QED

Theorem le_action_full_suffix_retention:
  wf_function fn /\
  le_pred_path (cfg_analyze fn) (j::post) /\
  EVERY (\l. ?bb. MEM bb fn.fn_blocks /\ bb.bb_label = l) (j::post) /\
  ~MEM j post /\
  find_join_block (cfg_analyze fn) visited (LAST (j::post)) = j /\
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) (LAST (j::post)))) k = SOME ops /\
  MEM a ops /\ MEM b ops /\ a <> b /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) k lbl inst = SOME pa /\
  pa.pa_join_lbl = j /\ MEM bb fn.fn_blocks /\ MEM bb.bb_label (j::post) ==>
  ?ys. 1 < LENGTH ys /\
    !n. n <= LENGTH bb.bb_instructions ==>
      FLOOKUP (unwrap_load_lattice
        (df_at NONE (load_analyze ctx fn) bb.bb_label n)) k = SOME ys
Proof
  strip_tac >>
  `?vs. FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) bb.bb_label)) k = SOME vs /\
    MEM a vs /\ MEM b vs` by metis_tac[le_find_join_suffix_boundaries] >>
  Cases_on `bb.bb_label = j`
  >- (irule le_action_capture_block_retention >> metis_tac[]) >>
  `MEM bb.bb_label post` by fs[] >>
  drule_all le_find_join_suffix_predecessor >> disch_then assume_tac >>
  `?q. MEM q (j::post) /\ cfg_preds_of (cfg_analyze fn) bb.bb_label = [q]` by
    metis_tac[] >>
  `?ys. FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) q)) k = SOME ys /\
    MEM a ys /\ MEM b ys` by metis_tac[le_find_join_suffix_boundaries] >>
  `le_fold_preserves ctx bb.bb_instructions k` by
    metis_tac[le_two_distinct_boundary_preserves] >>
  `fn_entry_label fn <> SOME bb.bb_label` by
    metis_tac[le_two_distinct_boundary_nonentry] >>
  qexists_tac `ys` >>
  conj_tac >- metis_tac[le_distinct_members_length] >>
  rpt strip_tac >> irule le_preserving_block_input_retention >>
  conj_tac >- metis_tac[le_distinct_members_length] >>
  drule_all loadElimBoundaryProvenanceTheory.le_joined_sole_pred >>
  disch_then (qspecl_then [`load_analyze ctx fn`, `ctx`] SUBST1_TAC) >>
  simp[] >> metis_tac[le_distinct_members_length]
QED
