(*
 * ConcretizeMemLoc's stage contract, row 3's run-time pointer conjunct
 * with DALLOCA: every reachable access of the output is in a site of its
 * provenance, or below the layout end, and its taint use is allowed.
 *
 * TOP-LEVEL:
 *   concretize_stage_frame_ptr_ok
 *)
Theory concretizeStageFramePtr
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
   Why it holds (intuition): DALLOCA outputs keep their site (b, fmp' - b)
   in both runs, since the pass leaves DALLOCA and the free-memory pointer
   alone; ALLOCA-derived variables of C' are ASSIGNs of literals, with no
   provenance, and static_mem puts their accesses at or below eom.  So an
   access ending above eom, or through a variable with provenance, is a
   DALLOCA or PARAM-chain access whose site C's access_ok gives; C''s
   taint is inside the relocation of C's. *)
Theorem concretize_stage_frame_ptr_ok:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  (!eom. max_live_eom C' = SOME eom ==> eom <= w2n vs.vs_initial_fmp) /\
  max_live_eom C' = SOME eom ==>
  !stk PG G tn fn inst s.
    frame_reachable vs C' stk PG G tn fn inst s ==>
    access_ok eom G fn inst s /\ taint_ok fn tn inst s
Proof
  cheat
QED
