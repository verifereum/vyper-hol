(*
 * Seam of external_entry_reaches_body_ptr (loweringPtrCorrect): the dead
 * bytes the entry's run is checked against are the ones the body's run is.
 *
 * The entry's pointer-safe run uses external_call_dead of the source call's
 * result, the body's (body_stmts_sim_ptr, ghost_inv) cx_dead of the call's
 * initial evaluation context.  A runtime call leaves the abstract machine's
 * sources and layouts as they were (call_external_function takes them from
 * am when cx.in_deploy is F, and finalize_pending_deletions keeps them), so
 * the two coincide.
 *)
Theory entryPtrSeamDead
Ancestors
  bodyPtrDefs vyperLoweringCorrect vyperInterpreter vyperCallMetadata
  sourceUnitExecution

Theorem external_call_dead_initial_cx:
  !H orc am tx.
    external_call_dead H tx (call_external orc [] am tx) =
    cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE)
Proof
  rpt gen_tac >>
  Cases_on `call_external orc [] am tx` >>
  PairCases_on `r` >>
  drule call_external_metadata >> strip_tac >>
  simp[external_call_dead_def, cx_dead_def, initial_evaluation_context_def]
QED
