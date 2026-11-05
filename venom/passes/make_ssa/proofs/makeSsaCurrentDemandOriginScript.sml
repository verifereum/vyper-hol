Theory makeSsaCurrentDemandOrigin
Ancestors makeSsaCurrentRootedOrigin makeSsaCurrentAvailability
  makeSsaCurrentDominanceBridge makeSsaCurrentFirstArrival
  makeSsaCurrentDemand makeSsaCurrentDefs venomWf venomInst venomExecProps
  livenessDefs list rich_list

Theorem current_demand_route_definition:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  entry_block fn = SOME eb /\ LRC (fn_cfg_edge fn) route eb.bb_label p /\
  lookup_block p fn.fn_blocks = SOME pb /\
  current_demand fn v p (LENGTH pb.bb_instructions) ==>
  ?l bb i. MEM l (route ++ [p]) /\ lookup_block l fn.fn_blocks = SOME bb /\
    MEM i bb.bb_instructions /\ MEM v i.inst_outputs
Proof
  strip_tac >>
  `current_available fn v p (LENGTH pb.bb_instructions)` by
    metis_tac[current_demand_available] >>
  drule current_lrc_fn_path >> strip_tac >>
  gvs[current_available_def] >>
  first_x_assum (qspec_then `route ++ [p]` mp_tac) >>
  simp[fn_entry_label_def] >> strip_tac
  >- (`lookup_block db.bb_label fn.fn_blocks = SOME db` by
        (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
      `k < LENGTH (route ++ [p])` by simp[] >>
      qexistsl_tac [`db.bb_label`, `db`, `di`] >> simp[] >>
      `MEM db.bb_label (route ++ [p])` by metis_tac[EL_MEM] >> gvs[]) >>
  qexistsl_tac [`p`, `pb`, `EL j pb.bb_instructions`] >>
  simp[EL_MEM]
QED

Theorem current_certificate_rooted_demand_nondefault:
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
  current_demand fn v p (LENGTH pb.bb_instructions) ==>
  !w. current_event_exit_env ep v <> CurrentDefault w
Proof
  strip_tac >>
  `?l bb i. MEM l (route ++ [p]) /\ lookup_block l fn.fn_blocks = SOME bb /\
    MEM i bb.bb_instructions /\ MEM v i.inst_outputs` by
    (irule current_demand_route_definition >> metis_tac[]) >>
  metis_tac[current_certificate_rooted_definition_nondefault]
QED

Theorem current_first_arrival_demand_exit_name_separate:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ first_block_no_preds fn /\
  current_actual_inserted fn v h /\
  current_token_name H (CurrentInserted v h) = SOME x /\
  fn_entry_state fn seed /\
  current_actual_prefix fn ctx (CurrentEntry fuel) seed phases
    (SOME (CurrentEntry remaining)) (OK before) before /\
  before.vs_prev_bb = SOME p /\ fn_cfg_edge fn p h /\
  MEM ev events /\ current_event_label ev = p /\
  (!phis. ~MEM (CurrentBatch h phis) phases) /\
  fn_inst_wf fn /\ fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  lookup_block p fn.fn_blocks = SOME pb /\
  current_demand fn v p (LENGTH pb.bb_instructions) /\
  MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions)) /\
  (!b phi. MEM b fn.fn_blocks /\ MEM phi (collect_phis b.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) ==>
  latest_current_name (current_event_exit_rs ev) v <> x
Proof
  strip_tac >>
  `?route. LRC (fn_cfg_edge fn) route eb.bb_label p` by
    metis_tac[current_actual_dispatched_route] >>
  `!w. current_event_exit_env ev v <> CurrentDefault w` by
    metis_tac[current_certificate_rooted_demand_nondefault] >>
  metis_tac[current_first_arrival_exit_name_residual]
QED
