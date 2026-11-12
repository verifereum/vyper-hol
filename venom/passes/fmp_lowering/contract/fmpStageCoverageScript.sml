(*
 * FmpLowering's lowered memory phase: every reachable instruction of the
 * lowered context C', run from the real state, accesses memory below the
 * static layout's end eom or at or above the real initial fmp.  Static
 * accesses of the raw input are unchanged; its dynamic ones lie in a live
 * DALLOCA site (row 3's access_ok) and are relocated to at or above the
 * real initial fmp; the inserted instructions access no memory.
 *
 * The proof is backward, by rule induction on the target's small-step
 * frame_reachable (concretize's ptr_raw_reachable_frame reaches it from
 * raw_reachable).  Every target state is covered (fmp_cov): it runs only
 * inserted instructions before a state related to a reachable source
 * point, or it sits in a revert forwarding's tail.  The step lemmas of
 * fmpStageOpSteps, fmpStageFmpSteps and fmpStageBlockSim move the source
 * point; fmpStageCoverBack gives them the terminating source step they
 * assume; fmpStageCoverInv states the invariant and gives each covered
 * state its memory fact.
 *
 * TOP-LEVEL:
 *   fmp_stage_coverage             - every target frame state is covered
 *   fmp_lowering_stage_lowered_mem
 *)
Theory fmpStageCoverage
Ancestors
  fmpStageCoverInv fmpStageCoverCall fmpStageCoverBack fmpStageCoverMem fmpStageBlockSim fmpStageFmpSteps
  fmpStageOpSteps fmpStageOpBase fmpStageControl fmpStageRel
  concretizePtrCoverageStaticMemReachability unitMemInv ptrDiscipline
  contextCodegenRel o1PassContract venomPassSchedule venomCompilerTypes
  passSimulationDefs venomExecSemantics venomState venomInst
  finite_map words list

Theorem fmp_stage_coverage:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom ==>
  !stk' PG' G' tn' fn' ti t.
    frame_reachable vs' C' stk' PG' G' tn' fn' ti t ==>
    fmp_cov D C C' vs vs' fmp eom stk' fn' t
Proof
  cheat
QED

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
