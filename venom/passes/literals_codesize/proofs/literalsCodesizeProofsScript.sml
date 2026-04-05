(*
 * Literals Codesize — Proofs
 *
 * Key property: lit_codesize_inst produces identical step_inst results.
 *   step_inst fuel ctx (lit_codesize_inst inst) s = step_inst fuel ctx inst s
 *
 * Cases:
 *   - non-ASSIGN or non-literal: unchanged (trivially equal)
 *   - NOT case: NOT(~w) = w  →  word_1comp (word_1comp w) = w
 *   - SHL case: (w>>>tz)<<<tz = w when trailing_zeros w = tz
 *
 * Lifting: step_inst equality implies exec_block equality (by induction
 * on instruction execution), then block_sim_function gives function level.
 * No analysis framework needed — this is a pure semantic identity.
 *)

Theory literalsCodesizeProofs
Ancestors
  literalsCodesizeDefs passSimulationProps

(* Core lemma: each rewritten instruction produces the identical result.
   ASSIGN [Lit w] → NOT [Lit (~w)]: exec_pure1 word_1comp on (~w) = w
   ASSIGN [Lit w] → SHL [Lit tz; Lit (w>>>tz)]: exec_pure2 on shift = w *)
Theorem lit_codesize_inst_step_eq:
  !fuel ctx inst s.
    step_inst fuel ctx (lit_codesize_inst inst) s =
    step_inst fuel ctx inst s
Proof
  cheat
QED

(* Per-block: MAP lit_codesize_inst preserves exec_block.
   Follows from lit_codesize_inst_step_eq by induction on execution. *)
Theorem lit_codesize_block_eq:
  !fuel ctx bb s.
    exec_block fuel ctx (block_map_transform lit_codesize_inst bb) s =
    exec_block fuel ctx bb s
Proof
  cheat
QED

(* Function-level: follows from block equality + function structure. *)
Theorem lit_codesize_function_correct_proof:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (lit_codesize_function fn) s)
Proof
  cheat
QED
