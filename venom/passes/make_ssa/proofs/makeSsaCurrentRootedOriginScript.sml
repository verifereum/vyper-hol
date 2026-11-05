Theory makeSsaCurrentRootedOrigin
Ancestors makeSsaCurrentRootedTokens makeSsaCurrentChronologicalOrigin
  makeSsaCurrentLastSite makeSsaCurrentExitTokens makeSsaCurrentTokens
  makeSsaCurrentDefs makeSsaCurrentAnalysis venomWf venomExecProps venomInst
  cfgAnalysisProps cfgWf livenessDefs list rich_list

Theorem current_cfg_route_lookups:
  !route a p. wf_function fn /\ LRC (fn_cfg_edge fn) route a p /\
  (?bb. lookup_block p fn.fn_blocks = SOME bb) ==>
  EVERY (\l. ?bb. lookup_block l fn.fn_blocks = SOME bb) (route ++ [p])
Proof
  Induct >> simp[LRC_def] >> rpt strip_tac >> gvs[]
  >- (`MEM h (fn_labels fn)` by
        (gvs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
      gvs[fn_labels_def, MEM_MAP] >>
      metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem current_certificate_rooted_inserted_origin:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\
  first_block_no_preds fn /\ entry_block fn = SOME eb /\
  LRC (fn_cfg_edge fn) route eb.bb_label p /\
  MEM ep events /\ current_event_label ep = p /\
  lookup_block p fn.fn_blocks = SOME pb /\
  MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions)) /\
  (!b phi. MEM b fn.fn_blocks /\ MEM phi (collect_phis b.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) /\
  current_event_exit_env ep v = CurrentInserted v h ==>
  ?pre post hb. route ++ [p] = pre ++ h::post /\
    current_actual_inserted fn v h /\ lookup_block h fn.fn_blocks = SOME hb /\
    EVERY (\i. ~MEM v i.inst_outputs) hb.bb_instructions /\
    EVERY (\l. ~current_changing_site fn (current_actual_inserted fn) v l) post
Proof
  strip_tac >>
  `current_chain_token fn (current_actual_inserted fn) v (route ++ [p])
     (CurrentDefault v) = CurrentInserted v h` by
    metis_tac[current_certificate_rooted_live_exit] >>
  `EVERY (\l. ?bb. lookup_block l fn.fn_blocks = SOME bb) (route ++ [p])` by
    metis_tac[current_cfg_route_lookups] >>
  metis_tac[current_chronological_inserted_inverse]
QED

Theorem current_certificate_rooted_default_origin:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\
  first_block_no_preds fn /\ entry_block fn = SOME eb /\
  LRC (fn_cfg_edge fn) route eb.bb_label p /\
  MEM ep events /\ current_event_label ep = p /\
  lookup_block p fn.fn_blocks = SOME pb /\
  MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions)) /\
  (!b phi. MEM b fn.fn_blocks /\ MEM phi (collect_phis b.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) /\
  current_event_exit_env ep v = CurrentDefault w ==>
  w = v /\ EVERY (\l. ~current_changing_site fn (current_actual_inserted fn) v l)
    (route ++ [p])
Proof
  strip_tac >>
  `current_chain_token fn (current_actual_inserted fn) v (route ++ [p])
     (CurrentDefault v) = CurrentDefault w` by
    metis_tac[current_certificate_rooted_live_exit] >>
  `EVERY (\l. ?bb. lookup_block l fn.fn_blocks = SOME bb) (route ++ [p])` by
    metis_tac[current_cfg_route_lookups] >>
  metis_tac[current_chronological_default_inverse]
QED

Theorem current_certificate_rooted_definition_nondefault:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\
  first_block_no_preds fn /\ entry_block fn = SOME eb /\
  LRC (fn_cfg_edge fn) route eb.bb_label p /\
  MEM ep events /\ current_event_label ep = p /\
  lookup_block p fn.fn_blocks = SOME pb /\
  MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions)) /\
  (!b phi. MEM b fn.fn_blocks /\ MEM phi (collect_phis b.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) /\
  (?l bb i. MEM l (route ++ [p]) /\ lookup_block l fn.fn_blocks = SOME bb /\
    MEM i bb.bb_instructions /\ MEM v i.inst_outputs) ==>
  !w. current_event_exit_env ep v <> CurrentDefault w
Proof
  strip_tac >>
  `current_event_exit_env ep v =
    current_chain_token fn (current_actual_inserted fn) v (route ++ [p]) (CurrentDefault v)` by
    metis_tac[current_certificate_rooted_live_exit] >>
  metis_tac[current_chain_token_definition_nondefault]
QED

(* The suffix exclusion is generic, so later consumers need not unfold the
   member-based changing-site predicate again. *)
Theorem current_non_changing_suffix_excludes_writers:
  EVERY (\l. ~current_changing_site fn ins v l) post ==>
  EVERY (\l. ~ins v l /\
    !bb i. lookup_block l fn.fn_blocks = SOME bb /\ MEM i bb.bb_instructions ==>
      ~MEM v i.inst_outputs) post
Proof
  simp[EVERY_MEM, current_changing_site_def] >>
  metis_tac[lookup_block_MEM, lookup_block_label]
QED
