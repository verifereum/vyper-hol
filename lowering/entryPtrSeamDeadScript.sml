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

(* Runtime calls reconstruct machine metadata from the original machine,
   independently of the evaluation result and its requests. *)
Theorem call_external_function_runtime_metadata:
  !orc gobs am cx nr mut ts all_mods args dflts vals body ret res am' rqs.
    ~cx.in_deploy /\
    call_external_function orc gobs am cx nr mut ts all_mods
      args dflts vals body ret = (res, am', rqs) ==>
    am'.sources = am.sources /\ am'.layouts = am.layouts
Proof
  rpt gen_tac >> strip_tac >>
  gvs[call_external_function_def, AllCaseEqs(),
      abstract_machine_from_state_def] >>
  pairarg_tac >> gvs[] >>
  gvs[AllCaseEqs(), abstract_machine_from_state_def]
QED

Theorem call_external_metadata:
  !orc gobs am tx res am' rqs.
    call_external orc gobs am tx = (res, am', rqs) ==>
    am'.sources = am.sources /\ am'.layouts = am.layouts
Proof
  rpt gen_tac >> strip_tac >>
  gvs[call_external_def, AllCaseEqs()] >>
  drule_at Any call_external_function_runtime_metadata >>
  simp[initial_evaluation_context_def]
QED

Theorem external_call_dead_initial_cx:
  !orc am tx.
    external_call_dead tx (call_external orc [] am tx) =
    cx_dead (initial_evaluation_context am.sources am.layouts tx NONE)
Proof
  rpt gen_tac >>
  Cases_on `call_external orc [] am tx` >>
  PairCases_on `r` >>
  drule call_external_metadata >> strip_tac >>
  simp[external_call_dead_def, cx_dead_def, initial_evaluation_context_def]
QED
