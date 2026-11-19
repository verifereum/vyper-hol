Theory gasFocusLowerDloadCut
Ancestors
  gasFocusLowerDloadFrameSafety gasFocusLowerDloadRawSafety

Theorem lower_dload_stage_focus_safety:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  callee_first names C.ctx_functions /\ o1_safe_upto D lo n C vs ==>
  ptr_discipline_upto lo n C' vs /\ taint_within_upto D n C' vs /\
  alloca_frontier_upto n C' vs /\
  (!fn inst s. raw_reachable vs C' fn inst s /\ gas_cut n vs s ==>
    raw_mem_ok C' fn inst s /\ dload_offset_ok C' fn inst s /\
    dload_headroom_ok C' fn inst s)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac ld_focus_actual_frame_safety >>
  metis_tac[ld_focus_actual_raw_safety]
QED
