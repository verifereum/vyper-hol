(*
 * Variable Range Analysis — Properties (public API)
 *
 * Re-exports consumer-facing properties from proofs/ via ACCEPT_TAC.
 * Consumers: just `Ancestors variableRangeAnalysisProps` to get defs + properties.
 *
 * TOP-LEVEL PROPERTIES:
 *   range_evaluate_inst_sound — single instruction soundness wrt step_inst
 *   range_run_block_sound     — block execution soundness wrt run_block
 *
 * Internal helpers (in proofs/, not re-exported here):
 *   range_join_two_sound, range_widen_states_sound — needed by fixpoint proof
 *   range_apply_{iszero,eq,compare}_sound — needed by edge_state proof
 *
 * TODO: range_analyze_sound — whole-analysis soundness (the ideal
 *   consumer-facing theorem, connecting range_get_range to concrete
 *   execution). Not yet proven — requires fixpoint iteration correctness.
 *)

Theory variableRangeAnalysisProps
Ancestors
  rangeEvalDefs rangeAnalysisDefs rangeAnalysisProofs

(* ===== Transfer Function Soundness ===== *)

(* If the abstract range state is sound w.r.t. the variable environment
   before executing an instruction, it remains sound after execution. *)
Theorem range_evaluate_inst_sound:
  ∀dfg inst rs s s'.
    in_range_state rs s.vs_vars ∧
    step_inst inst s = OK s' ⇒
    in_range_state (range_evaluate_inst dfg inst rs) s'.vs_vars
Proof ACCEPT_TAC rangeAnalysisProofsTheory.range_evaluate_inst_sound
QED

(* Same, lifted to an entire basic block: if ranges are sound at block
   entry, they are sound at block exit. *)
Theorem range_run_block_sound:
  ∀dfg bb rs imap rs' imap' s s'.
    range_run_block dfg bb.bb_instructions rs imap = (rs', imap') ∧
    in_range_state rs s.vs_vars ∧
    run_block bb s = OK s' ⇒
    in_range_state rs' s'.vs_vars
Proof ACCEPT_TAC rangeAnalysisProofsTheory.range_run_block_sound
QED
