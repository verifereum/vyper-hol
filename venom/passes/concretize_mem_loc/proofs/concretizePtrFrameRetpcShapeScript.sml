(*
 * The frame-relation return-PC shape (every RET and PHI of every input
 * function) under the stage contract's hypotheses. The paired-prefix
 * producers take it as a premise; ptr_stage_paired_bridge supplies only
 * the reachable-code form unitShapeDefs$retpc_shape_ok.
 *)
Theory concretizePtrFrameRetpcShape
Ancestors
  o1PassContract ptrDiscipline unitMemInv stackPlanGen concretizeMemLocDefs
  venomPassDispatcher cfgWf unitShapeDefs frameRel

Theorem ptr_stage_frame_retpc_shape:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom ==>
  EVERY frameRel$retpc_shape_ok C.ctx_functions
Proof
  cheat
QED
