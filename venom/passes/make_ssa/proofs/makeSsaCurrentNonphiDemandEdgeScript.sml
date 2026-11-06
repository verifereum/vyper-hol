Theory makeSsaCurrentNonphiDemandEdge
Ancestors
  makeSsaCurrentEdgeTransport makeSsaCurrentLiveTransport
  makeSsaCurrentWfSsa makeSsaCurrentDemand livenessDefs
  venomInst venomExecSemantics list alist

Theorem current_nonphi_demand_selected_live:
  wf_function fn /\ all_reachable fn /\
  lookup_block h fn.fn_blocks = SOME old /\
  current_demand fn v h (LENGTH (collect_phis old.bb_instructions)) /\
  (!pb phi. MEM pb fn.fn_blocks /\ MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) ==>
  ?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) h = SOME vs /\ MEM v vs
Proof
  strip_tac >> drule_all current_selected_live_iff >>
  disch_then (rewrite_tac o single) >>
  irule current_wf_demand_live >> metis_tac[]
QED

Theorem current_nonphi_demand_edge_env:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  MEM pev events /\ current_event_label pev = p /\
  MEM hev events /\ current_event_label hev = h /\
  ~current_actual_inserted fn v h /\ current_phi_cut_clear fn v h /\
  lookup_block h fn.fn_blocks = SOME old /\
  current_demand fn v h (LENGTH (collect_phis old.bb_instructions)) /\
  (!pb phi. MEM pb fn.fn_blocks /\ MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) ==>
  current_event_exit_env pev v = current_event_entry_env hev v
Proof
  strip_tac >>
  `wf_function fn /\ all_reachable fn` by fs[current_wf_phi_context_def] >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) h = SOME vs /\ MEM v vs` by
    (irule current_nonphi_demand_selected_live >> metis_tac[]) >>
  irule current_edge_unaffected_env >> metis_tac[]
QED
