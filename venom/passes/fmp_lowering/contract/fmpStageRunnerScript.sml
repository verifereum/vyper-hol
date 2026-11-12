(*
 * FmpLowering's stage simulation: every terminating run of the raw input
 * context C, started at its own free-memory pointer fmp, is matched by a
 * run of the lowered context C' from the real state, up to the dead bytes
 * D.  The raw run never reclaims and places its dynamic allocations from
 * fmp up; the lowered run threads a runner through BUMP and INVOKE and
 * reclaims at the restores.  Row 3's pointer facts (o1_static_inv) keep
 * DALLOCA pointers to address uses within their site, so the relocation
 * is not observable; fmp_variant_room puts the real initial fmp between
 * the static layout's end and fmp.
 *
 * TEMPORARY: admitted (cheat) while the simulation is proved as its own
 * pieces; the statement is frozen.
 *
 * TOP-LEVEL:
 *   fmp_lowering_stage_sim
 *)
Theory fmpStageRunner
Ancestors
  o1PassContract venomPassSchedule venomCompilerTypes

Theorem fmp_lowering_stage_sim:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_pre 3 C C' /\ dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs' /\
  o1_inv D 3 C (vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) /\
  fmp_variant_room (SOME fmp) C' vs' ==>
  ctx_sim D C C' (vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) vs'
Proof
  cheat
QED
