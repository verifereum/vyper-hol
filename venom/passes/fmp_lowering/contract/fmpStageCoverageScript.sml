(*
 * FmpLowering's lowered memory phase: every reachable instruction of the
 * lowered context C', run from the real state, accesses memory below the
 * static layout's end eom or at or above the real initial fmp.  Static
 * accesses of the raw input are unchanged; its dynamic ones lie in a live
 * DALLOCA site (row 3's access_ok) and are relocated to at or above the
 * real initial fmp; the inserted instructions access no memory.
 *
 * TEMPORARY: admitted (cheat) while the coverage is proved as its own
 * piece; the statement is frozen.
 *
 * TOP-LEVEL:
 *   fmp_lowering_stage_lowered_mem
 *)
Theory fmpStageCoverage
Ancestors
  o1PassContract venomPassSchedule venomCompilerTypes

Theorem fmp_lowering_stage_lowered_mem:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_pre 3 C C' /\ dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs' /\
  o1_inv D 3 C (vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) /\
  fmp_variant_room (SOME fmp) C' vs' /\ max_live_eom C = SOME eom ==>
  mem_inv (lowered_mem_fact eom) C' vs'
Proof
  cheat
QED
