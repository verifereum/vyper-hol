(*
 * ConcretizeMemLoc's request companion: an aborting run of the input
 * context is matched by an aborting run of the output whose requests are a
 * prefix of the input's up to the dead bytes (ctx_abort_rq), under
 * concretize_stage_sim's premises.
 *)
Theory concretizeStageRequests
Ancestors
  concretizeStageSim o1RequestContract o1PassContract ptrDiscipline
  unitMemInv concretizeMemLocDefs venomPassDispatcher cfgWf
  concretizeLayoutStageSimulation concretizeLayoutCorridorRequests
  concretizeLayoutRequestRelations concretizeLayoutRequestRun
  concretizeLayoutRequestBase concretizeLayoutRequestBlock
  concretizeLayoutRequestControl

Theorem concretize_stage_abort_rq:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions ==>
  ctx_abort_rq D C C' vs vs
Proof
  cheat
QED
