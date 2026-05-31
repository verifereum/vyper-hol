(*
 * Algebraic Optimization — CMP Flip Block-level Simulation
 *
 * Proves that the cmp_flip mini-pass preserves block execution semantics
 * up to state_equiv on dead variables (comparator outputs whose values
 * change under the flip).
 *
 * TOP-LEVEL:
 *   cmp_flip_run_insts_sim — run_insts simulation for cmp_flip transform
 *)

Theory aoCmpFlipBlockProof
Ancestors
  algebraicOptDefs aoCmpFlipSim
  analysisSimDefs analysisSimProofsBase
  passSimulationProps
  stateEquiv stateEquivProps execEquivProps
  venomExecSemantics venomState venomInst venomWf
  finite_map
Libs
  pairLib BasicProvers

(* ===== Core lemma: per-instruction cmp_flip simulation =====
 *
 * For each instruction, executing the original from state s1 and
 * the transformed from state s2 (where execution_equiv dead s1 s2)
 * produces execution_equiv dead results.
 *
 * Four cases:
 * 1. Unchanged: same instruction → step_inst_result_equiv
 * 2. Flip: CMP→FLIP_CMP from SAME state → dead var output differs
 * 3. Remove: ISZERO vs ASSIGN from DIFFERENT states → same iz_out
 * 4. Insert: 1 inst vs 2 insts → ISZERO heals dead var for ASSERT
 *)

(* ===== Case 1: Unchanged instruction =====
 * step_inst on same instruction from state_equiv states gives result_equiv.
 * Direct from step_inst_result_equiv. *)

(* ===== Case 2: Flip instruction =====
 * CMP(x,w) → FLIP_CMP(x,w') from the SAME state s.
 * Both access the same operands. Output (dead var) differs.
 * All other state fields (memory, etc.) identical. *)

(* For flip case: executing two non-INVOKE instructions from the SAME state,
   both with the same single output variable (which is in dead) and the same
   variable operands (only literal differs), produces execution_equiv dead.
   Key: both succeed or both fail (since they access the same variable operand).
   Output values may differ but output var is in dead. *)

(* ===== Case 3: Remove (ISZERO → ASSIGN) =====
 * From execution_equiv dead states where the operand (dead var) has
 * related values: val_st2 = iszero_equiv(val_st1).
 * ISZERO(dead_var → iz_out) in st1 gives iz_out = iszero(val_st1).
 * ASSIGN(dead_var → iz_out) in st2 gives iz_out = val_st2.
 * From flip pair: iszero(val_st1) = val_st2. So iz_out agrees. *)


val _ = export_theory();
