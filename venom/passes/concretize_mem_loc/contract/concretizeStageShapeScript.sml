(*
 * ConcretizeMemLoc's stage contract, the structural part of row 3: the
 * facts of the output context the later runs need that are not about
 * memory.
 *
 * TOP-LEVEL:
 *   concretize_stage_shape
 *)
Theory concretizeStageShape
Ancestors
  o1PassContract stackPlanGen concretizeMemLocDefs venomPassDispatcher

(* Why it holds (intuition, not a prescribed proof).

   Every input function has fn_eom = NONE, so the pass computes a layout
   for each and sets fn_eom to SOME; the global reservations are C's and
   well formed, so max_live_eom C' is SOME.  The rewrite only turns
   ALLOCA into ASSIGN, so the CFG, the PHIs, the definitions and uses,
   the INVOKE targets and the FMP signature are the input's. *)
Theorem concretize_stage_shape:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\
  reserved_intervals_wf C.ctx_global_reserved /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  fmp_free_ctx C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  callee_first names C.ctx_functions ==>
  fmp_free_ctx C' /\ EVERY make_ssa_input_ok C'.ctx_functions /\
  callee_first names C'.ctx_functions /\
  ?eom. max_live_eom C' = SOME eom
Proof
  cheat
QED
