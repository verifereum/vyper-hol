Theory gasFocusConcretizeCutTaintWithin
Ancestors
  unitMemInv contextRawReachable
  o1PassContract o1PassLift o1SafeUpto unitTransformDefs
  venomPassSchedule ptrDiscipline venomWf lowerDloadDefs stackPlanGen
  venomState words list

(* Scratch statement for elaboration and independent review.
   The available shapes are the C2/C3 o1_ctx_shape facts. Both cuts use
   the same root, horizon and dead mask. *)
Theorem focus_concretize_cut_taint_within:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_ptr_safe_upto D lo n C vs /\
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> dload_headroom_ok ctx fn inst s) C vs /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
    raw_mem_ok C fn inst s /\ dload_offset_ok C fn inst s) /\
  alloca_frontier_upto n C vs /\
  EVERY ssa_form C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\ dead_wf D ==>
  taint_within_upto D n C' vs
Proof
  cheat
QED
