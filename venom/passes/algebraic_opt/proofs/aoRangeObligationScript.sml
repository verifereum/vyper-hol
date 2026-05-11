(* Obligation: range analysis produces sound bounds.
 *
 * range_analyze computes a dataflow fixpoint (via df_analyze_widen)
 * that associates each program point with an abstract range state.
 * Soundness means: if an operand evaluates to v at a given program
 * point, then v is contained in the computed range.
 *
 * To prove this, the agent should:
 *   1. Prove per-opcode transfer function soundness for each handler
 *      in rangeEvalDefsScript.sml (~20 opcodes): if input ranges
 *      contain actual values, output range contains the result.
 *   2. Prove block transfer function soundness (composition).
 *   3. Prove fixpoint soundness: df_analyze_widen produces ranges
 *      that hold at each program point.
 *   4. Connect to the in_range predicate.
 *
 * Existing infrastructure:
 *   - rangeAnalysisProofsScript.sml has lattice proofs
 *     (range_join_two_sound, range_widen_states_sound, etc.)
 *   - Per-opcode range evaluation in rangeEvalDefsScript.sml
 *)
Theory aoRangeObligation
Ancestors
  algebraicOptDefs rangeAnalysisDefs valueRangeDefs venomExecSemantics

Theorem range_analyze_sound:
  !fn0 bb inst idx s op v.
    MEM bb fn0.fn_blocks /\ MEM inst bb.bb_instructions /\
    eval_operand op s = SOME v /\
    MEM op (ao_resolve_iszero_inst
      (ao_compute_fn_iszero_targets fn0) inst).inst_operands ==>
    in_range (range_get_range (range_analyze fn0)
      bb.bb_label idx op) v
Proof
  cheat
QED
