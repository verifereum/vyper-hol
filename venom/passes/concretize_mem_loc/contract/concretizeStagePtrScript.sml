(*
 * ConcretizeMemLoc's stage contract, the output's invariants: the pointer
 * discipline FmpLowering needs, with the static layout end as its bound,
 * and every static access below that end.
 *
 * TOP-LEVEL:
 *   concretize_stage_ptr         - C' keeps the pointer discipline above
 *                                  eom
 *   concretize_stage_static_mem  - C' accesses memory below the layout end
 *)

Theory concretizeStagePtr
Ancestors
  o1PassContract ptrDiscipline unitMemInv concretizeMemLocDefs
  venomPassDispatcher cfgWf o1ScheduleDecomp

(* Why it holds (intuition, not a prescribed proof).

   The pass replaces every ALLOCA with an ASSIGN of a literal position from
   the static layout, whose end is fn_eom <= eom; so C' has no ALLOCA
   sites, its static accesses are at those literal positions plus the
   in-site offsets ptr_discipline lo C allows, and its DALLOCA, PARAM and
   pointer-compare uses are the input's.  Without DALLOCA, every access of
   C' is below eom. *)

Theorem concretize_stage_ptr:
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
  ctx_eom_bounded eom C' ==>
  ptr_discipline eom C' vs
Proof
  cheat
QED

Theorem concretize_stage_static_mem:
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
  ctx_eom_bounded eom C' ==>
  mem_inv (static_mem_ok eom) C' vs
Proof
  cheat
QED
