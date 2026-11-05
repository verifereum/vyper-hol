Theory makeSsaCurrentInsertionDemand
Ancestors makeSsaCurrentSurvivorDemand makeSsaCurrentPlacementCut
  makeSsaCurrentPlacement makeSsaCurrentLiveTransport
  venomExecProps venomWf venomInst list

Theorem current_actual_insertion_post_phi_live:
  wf_function fn /\ current_actual_inserted fn v h /\ lookup_block h fn.fn_blocks = SOME bb ==>
  MEM v (live_vars_at (liveness_analyze fn) h
    (LENGTH (collect_phis bb.bb_instructions)))
Proof
  strip_tac >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) h = SOME vs /\ MEM v vs` by
    (qpat_x_assum `current_actual_inserted fn v h` mp_tac >>
     simp[current_actual_inserted_def] >> strip_tac >>
     drule current_pruned_reach_live >> simp[current_placement_live_def]) >>
  metis_tac[current_selected_live_iff]
QED

Theorem current_actual_insertion_exit_demand:
  wf_function fn /\ fn_inst_wf fn /\ current_actual_inserted fn v h /\
  lookup_block h fn.fn_blocks = SOME bb /\ lookup_block p fn.fn_blocks = SOME pb /\
  fn_cfg_edge fn p h /\
  (!i. i < LENGTH (collect_phis bb.bb_instructions) ==>
    ~MEM v (inst_defs (EL i bb.bb_instructions))) ==>
  current_demand fn v p (LENGTH pb.bb_instructions)
Proof
  strip_tac >>
  `MEM v (live_vars_at (liveness_analyze fn) h
    (LENGTH (collect_phis bb.bb_instructions)))` by
    metis_tac[current_actual_insertion_post_phi_live] >>
  irule current_live_post_phi_unwritten_edge_demand >>
  simp[] >> qexistsl_tac [`bb`, `h`] >> simp[]
QED

Theorem current_actual_insertion_exit_live:
  wf_function fn /\ all_reachable fn /\ current_actual_inserted fn v h /\
  lookup_block h fn.fn_blocks = SOME bb /\ lookup_block p fn.fn_blocks = SOME pb /\
  fn_cfg_edge fn p h /\
  (!i. i < LENGTH (collect_phis bb.bb_instructions) ==>
    ~MEM v (inst_defs (EL i bb.bb_instructions))) /\
  (!inst. MEM inst (collect_phis bb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs inst.inst_operands))) ==>
  MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions))
Proof
  strip_tac >>
  `MEM v (live_vars_at (liveness_analyze fn) h
    (LENGTH (collect_phis bb.bb_instructions)))` by
    metis_tac[current_actual_insertion_post_phi_live] >>
  metis_tac[current_live_cut_to_pred_exit]
QED
