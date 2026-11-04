Theory fnPlanLineageJoinEntry
Ancestors
  fnPlanLineagePhiRealization fnPlanLineagePhiActivation fnPlanLineageEdge
  fnPlanLineagePhiMaps codegenReadyCompute stackPlanGen venomWf venomExecProps
  livenessTransferProofs list finite_map

Theorem analyzed_edge_phi_matching_total:
  codegen_ready_fn fn /\ lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_succs_of (cfg_analyze fn) pred) ==>
  !v i. FLOOKUP (FST (build_phi_maps pred (collect_phis sb.bb_instructions))) v = SOME i ==>
    IS_SOME (FLOOKUP (SND (build_phi_maps pred (collect_phis sb.bb_instructions))) i)
Proof
  rpt strip_tac >> irule build_phi_maps_matching_total >>
  conj_tac >- (qexists_tac `v` >> simp[]) >>
  `MEM sb fn.fn_blocks /\ sb.bb_label = succ` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `wf_function fn /\ def_dominates_uses fn` by gvs[codegen_ready_fn_def] >>
  `fn_cfg_edge fn pred sb.bb_label` by metis_tac[fn_cfg_edge_cfg_analyze] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule collect_phis_mem >> strip_tac >>
  `phi_edge_uses_wf fn sb phi` by
    (gvs[def_dominates_uses_def] >>
     first_x_assum (qspecl_then [`sb`, `phi`] mp_tac) >> simp[]) >>
  gvs[phi_edge_uses_wf_def] >>
  first_x_assum (qspec_then `pred` mp_tac) >> simp[] >>
  strip_tac >> PairCases_on `p` >> gvs[] >> metis_tac[]
QED
