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
  bodyPtrDefs vyperLoweringCorrect vyperInterpreter

(* SEAM (cheated; proved by its own alan run).
   Hint: unfold call_external, call_external_function and
   finalize_pending_deletions; every branch returns am itself or
   abstract_machine_from_state am.sources _ am.layouts _ (the
   evaluate_all_constants branch needs cx.in_deploy, which
   initial_evaluation_context sets to F).  Then unfold external_call_dead
   and cx_dead. *)
Theorem external_call_dead_initial_cx:
  !orc am tx.
    external_call_dead tx (call_external orc [] am tx) =
    cx_dead (initial_evaluation_context am.sources am.layouts tx NONE)
Proof
  cheat
QED
