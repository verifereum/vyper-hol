Theory makeSsaCurrentActualSurvivorDemand
Ancestors makeSsaCurrentSurvivorDemand makeSsaCurrentSurvivorNoOutput
  makeSsaCurrentPlacementCut makeSsaCurrentPlacement makeSsaCurrentLiveTransport
  venomExecProps venomWf venomInst list

Theorem current_certificate_survivor_exit_demand:
  current_structural_certificate s fn fn' s' A H events /\
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  fn_phis_cover_preds fn /\ fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ entry_block fn = SOME eb /\
  lookup_block p fn.fn_blocks = SOME pred /\ fn_cfg_edge fn p h /\
  lookup_block h fn'.fn_blocks = SOME out /\
  current_actual_inserted fn v h /\ current_token_name H (CurrentInserted v h) = SOME n /\
  MEM n (FLAT (MAP (\j. j.inst_outputs) (collect_phis out.bb_instructions))) ==>
  current_demand fn v p (LENGTH pred.bb_instructions)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?old. lookup_block h fn.fn_blocks = SOME old` by
    (fs[fn_cfg_edge_def, wf_function_def, fn_succs_closed_def, fn_labels_def, MEM_MAP] >>
     metis_tac[MEM_lookup_block]) >>
  `!i. i < LENGTH (collect_phis old.bb_instructions) ==>
      ~MEM v (inst_defs (EL i old.bb_instructions))` by
    (gen_tac >> disch_tac >> irule current_certificate_survivor_no_phi_output >>
     metis_tac[]) >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) h = SOME vs /\ MEM v vs` by
    (qpat_x_assum `current_actual_inserted fn v h` mp_tac >>
     simp[current_actual_inserted_def] >> strip_tac >>
     drule current_pruned_reach_live >> simp[current_placement_live_def]) >>
  `MEM v (live_vars_at (liveness_analyze fn) h
      (LENGTH (collect_phis old.bb_instructions)))` by
    metis_tac[current_selected_live_iff] >>
  irule current_live_post_phi_unwritten_edge_demand >>
  simp[] >> qexistsl_tac [`old`, `h`] >> simp[]
QED
