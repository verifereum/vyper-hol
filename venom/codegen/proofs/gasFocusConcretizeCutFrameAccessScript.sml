Theory gasFocusConcretizeCutFrameAccess
Ancestors
  o1PassContract o1PassLift o1SafeUpto unitTransformDefs
  venomPassSchedule ptrDiscipline venomWf lowerDloadDefs stackPlanGen
  venomState words list

(* Scratch statement for elaboration and independent review.
   The unchanged root and stage inputs are those of focus_concretize_cut_fields.
   The available C3 shape is o1_ctx_shape C'. *)
Theorem focus_concretize_cut_frame_access:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_safe_upto D lo n C vs /\ alloca_frontier_upto n C vs /\
  EVERY ssa_form C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) ==>
  !stk PG G tn fn inst s. frame_reachable vs C' stk PG G tn fn inst s /\
    gas_cut n vs s ==> access_ok eom G fn inst s /\ taint_ok fn tn inst s
Proof
  cheat
QED
