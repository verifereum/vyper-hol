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
   the INVOKE targets and the FMP signature are the input's.

   Facts worth knowing (checked against the definitions, not proved):
   - fn_pass_step gives fn_pass_effects_hold for the ConcretizeMemLoc tag:
     IS_SOME out.fn_eom (FSLE_Concretize) and an equal fn_fmp_signature
     (FAE_PreserveFmpConvention); it also gives introduces_no_invoke_edges
     and the unchanged fn_name, which is all callee_first needs.
   - With fn_eom = NONE the pass's layout comes from mk_concretize_layout,
     whose allocation_eom_fold succeeded, so every ALLOCA has a position
     (allocation_eom_fold_success): concretize_inst_with_positions never
     turns an ALLOCA into a NOP.
   - clear_nops_function then drops only NOPs, which have no outputs by
     inst_wf (o1_ctx_shape); terminators are not NOPs, so bb_succs, the
     CFG edges, the entry and the PHIs are unchanged, and the dropped
     instructions only remove uses.
   - global_reserved_end r 0 is SOME when every interval of r is
     reserved_interval_wf, which reserved_intervals_wf implies. *)
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
