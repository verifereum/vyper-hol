Theory concretizeAnalysisOriginCoverage
Ancestors
  concretizeAnalysisOriginReach concretizeAnalysisOriginFlow
  concretizeAnalysisCoverage concretizeAnalysisBaseModel singleWriterScan
  concretizeAnalysisBoundary basePtrDefs concretizeMemLocDefs
  frameOriginReachable frameOriginUpdates ptrDiscipline venomWf venomInst
  relation list pred_set

Theorem bp_descriptor_stream_subset:
  set is SUBSET set js ==>
  set (bp_descriptor_stream is) SUBSET set (bp_descriptor_stream js)
Proof
  simp[SUBSET_DEF, bp_descriptor_stream_member] >> metis_tac[]
QED

Theorem sw_seed_mono:
  set ds SUBSET set es /\ sw_seed ds a x ==> sw_seed es a x
Proof
  simp[sw_seed_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem sw_edge_mono:
  set ds SUBSET set es /\ sw_edge ds x y ==> sw_edge es x y
Proof
  simp[sw_edge_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem sw_path_mono:
  !x y. RTC (sw_edge ds) x y ==>
  set ds SUBSET set es ==> RTC (sw_edge es) x y
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- simp[] >>
  metis_tac[sw_edge_mono, RTC_RULES]
QED

Theorem bp_flow_scan:
  (!i. MEM i (fn_insts fn) ==> MEM i (bp_scan_insts fn order)) /\
  bp_flow fn aid v ==>
  ?x. sw_seed (bp_descriptor_stream (bp_scan_insts fn order)) (Allocation aid) x /\
      RTC (sw_edge (bp_descriptor_stream (bp_scan_insts fn order))) x v
Proof
  simp[bp_flow_def] >> rpt strip_tac >>
  `set (bp_descriptor_stream (fn_insts fn)) SUBSET
   set (bp_descriptor_stream (bp_scan_insts fn order))` by
    (irule bp_descriptor_stream_subset >> simp[SUBSET_DEF]) >>
  metis_tac[sw_seed_mono, sw_path_mono]
QED

Theorem bp_flow_production_coverage:
  fn_ptr_ok P fn /\ ssa_form fn /\
  (!i. MEM i (fn_insts fn) ==> MEM i (bp_scan_insts fn cfg.cfg_dfs_pre)) /\
  bp_flow fn aid v ==>
  Allocation aid IN bp_bases (bp_analyze_fuel (concretize_memloc_fuel fn) cfg fn) v
Proof
  rpt strip_tac >> drule_all bp_flow_scan >> strip_tac >>
  irule bp_analyze_production_local_base_coverage >> metis_tac[]
QED

Theorem origin_frame_current_base_coverage:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY wf_function ctx.ctx_functions /\
  ssa_form fn /\
  (!i. MEM i (fn_insts fn) ==> MEM i (bp_scan_insts fn cfg.cfg_dfs_pre)) /\
  FLOOKUP om v = SOME (OriginLocal aid,site) ==>
  Allocation aid IN bp_bases (bp_analyze_fuel (concretize_memloc_fuel fn) cfg fn) v
Proof
  rpt strip_tac >>
  `bp_flow fn aid v` by metis_tac[origin_frame_current_local_path] >>
  drule origin_frame_flow_invariant >> disch_then (qspec_then `P` mp_tac) >>
  simp[] >> simp[EVERY_MEM] >> rpt strip_tac >>
  irule bp_flow_production_coverage >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem origin_frame_saved_base_coverage:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY wf_function ctx.ctx_functions /\
  n < LENGTH stk /\ ssa_form (EL n stk).cf_fn /\
  (!i. MEM i (fn_insts (EL n stk).cf_fn) ==>
       MEM i (bp_scan_insts (EL n stk).cf_fn cfg.cfg_dfs_pre)) /\
  FLOOKUP (EL n oms) v = SOME (OriginLocal aid,site) ==>
  Allocation aid IN bp_bases
    (bp_analyze_fuel (concretize_memloc_fuel (EL n stk).cf_fn) cfg (EL n stk).cf_fn) v
Proof
  rpt strip_tac >>
  `bp_flow (EL n stk).cf_fn aid v` by metis_tac[origin_frame_saved_local_path] >>
  drule origin_frame_flow_invariant >> disch_then (qspec_then `P` mp_tac) >>
  simp[] >> simp[EVERY_MEM, LIST_REL_EL_EQN] >>
  rpt strip_tac >> irule bp_flow_production_coverage >> fs[EVERY_MEM] >> metis_tac[]
QED
