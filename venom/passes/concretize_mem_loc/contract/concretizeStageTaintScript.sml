(*
 * ConcretizeMemLoc's stage contract, row 3's taint containment with
 * DALLOCA: the output's taint at call requests and halts stays within
 * the dead bytes, as the input's does.
 *
 * TOP-LEVEL:
 *   concretize_stage_taint_within
 *)
Theory concretizeStageTaint
Ancestors
  concretizeStageStatic
  o1PassContract ptrDiscipline unitMemInv stackPlanGen concretizeMemLocDefs
  venomPassDispatcher cfgWf
  concretizePtrStagePairedBridge concretizePtrHistoryCoverage
  concretizePtrUniversalExtension concretizePtrCoverageStaticMem
  concretizePtrFrameRetpcShape
  concretizeAllocationFree ptrStaticDiscipline pointerConfinedDefs
  pointerConfinedProps pointerClosure lowerDloadPtrClosure passSharedDefs
  passSharedProps passTransform venomInst list pred_set

(* ADMITTED until proved: an alan target of P5a, proved before the
   piece merges.
   Why it holds (intuition): at each call request and halt of C', the
   paired run of C has at least the taint of C', relocated; a reused
   layout position's stale taint corresponds to the fresh ALLOCA site's
   new_site_bytes taint in C, and the storages agree outside D. *)
Theorem concretize_stage_taint_within:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  (!eom. max_live_eom C' = SOME eom ==> eom <= w2n vs.vs_initial_fmp) ==>
  taint_within D C' vs
Proof
  cheat
QED
