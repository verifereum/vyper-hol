(*
 * State Equivalence Definitions
 *
 * Definitions only — properties/theorems are in props/stateEquivPropsScript.sml
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * Semantic Equivalence Hierarchy (weakest to strongest):
 *
 *   1. observable_equiv         : Only externally visible effects
 *   2. execution_equiv vars     : All state except control flow, modulo vars
 *   3. state_equiv vars         : Full state comparison, modulo vars
 *
 * Satisfies: state_equiv ⊆ execution_equiv ⊆ observable_equiv
 *
 * For full equivalence (no variable exceptions), use state_equiv {}.
 *
 * TOP-LEVEL DEFINITIONS:
 *   - state_equiv      : Full state equivalence with variable exceptions
 *   - execution_equiv   : State equiv ignoring control flow fields
 *   - observable_equiv  : Only externally visible effects
 *   - result_equiv      : Equivalence for exec_result
 *   - terminates        : Predicate for successful termination (not Error)
 *   - pass_correct      : Combined termination + result equivalence predicate
 *)

Theory stateEquiv
Ancestors
  finite_map pred_set
  venomState venomExecSemantics

(* ==========================================================================
   Level 1: Observable Equivalence (Weakest)
   ========================================================================== *)

(*
 * PURPOSE: Capture only what the external world can observe after execution.
 * This is the weakest equivalence - everything else is internal detail.
 *
 * FIELDS COMPARED:
 *   - vs_storage   : Persistent storage (survives transaction)
 *   - vs_accounts  : Account balances/state
 *   - vs_returndata: Return value or revert reason
 *   - vs_halted    : Whether execution halted
 *   - vs_reverted  : Whether execution reverted
 *
 * USE FOR: Proving that two executions have the same external effect,
 * regardless of how they got there.
 *)
Definition observable_equiv_def:
  observable_equiv s1 s2 <=>
    s1.vs_storage = s2.vs_storage /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_reverted = s2.vs_reverted
End

(* ==========================================================================
   Level 2: Execution Equivalence (Intermediate)
   ========================================================================== *)

(*
 * PURPOSE: State equivalence ignoring control flow fields. Appropriate
 * for terminal states (Halt/Revert) where control flow is irrelevant.
 *
 * FIELDS COMPARED: All except control flow (vs_current_bb, vs_inst_idx, vs_prev_bb)
 *
 * USE FOR: Comparing terminal states, proving control-flow optimizations correct
 *)
Definition execution_equiv_def:
  execution_equiv vars s1 s2 <=>
    (!v. v NOTIN vars ==> lookup_var v s1 = lookup_var v s2) /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_storage = s2.vs_storage /\
    s1.vs_transient = s2.vs_transient /\
    (* OMIT: vs_current_bb, vs_inst_idx, vs_prev_bb *)
    s1.vs_halted = s2.vs_halted /\
    s1.vs_reverted = s2.vs_reverted /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx
End

(* ==========================================================================
   Level 3: Full State Equivalence (Strongest)
   ========================================================================== *)

(*
 * PURPOSE: Full state equivalence ignoring only the specified variables.
 * This is the strongest equivalence, requiring all fields to match.
 *
 * For full equivalence with no exceptions, use state_equiv {}.
 *
 * USE FOR: Step-by-step simulation, same-path optimizations, PHI-related proofs
 *)
Definition state_equiv_def:
  state_equiv vars s1 s2 <=>
    execution_equiv vars s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb
End

(* ==========================================================================
   Result Equivalence
   ========================================================================== *)

(*
 * PURPOSE: Extend equivalence to exec_result, using the appropriate level
 * of equivalence for each result type.
 *
 * KEY DESIGN DECISION:
 *   - OK: Uses state_equiv (full state comparison)
 *     Reason: Execution continues, so control flow matters for next step
 *
 *   - Halt/Revert: Uses execution_equiv (ignores control flow)
 *     Reason: Execution has terminated, control flow is irrelevant
 *     This enables proving control-flow optimizations correct
 *
 *   - Error: Always equivalent (error messages may differ)
 *)
Definition result_equiv_def:
  result_equiv vars (OK s1) (OK s2) = state_equiv vars s1 s2 /\
  result_equiv vars (Halt s1) (Halt s2) = execution_equiv vars s1 s2 /\
  result_equiv vars (Revert s1) (Revert s2) = execution_equiv vars s1 s2 /\
  result_equiv vars (Error e1) (Error e2) = T /\
  result_equiv vars _ _ = F
End

(* ==========================================================================
   Termination Predicate
   ========================================================================== *)

(*
 * Predicate: execution terminates (not Error).
 * Used for bidirectional correctness proofs where we need to express
 * "termination equivalence and result equivalence assuming termination".
 *)
Definition terminates_def:
  terminates r <=> case r of Error _ => F | _ => T
End

(* ==========================================================================
   Pass Correctness Predicate
   ========================================================================== *)

(*
 * Predicate: Two executions (parameterized by fuel) are pass-correct.
 * This captures the pattern used in compiler pass correctness proofs:
 *   1. Termination equivalence: original terminates iff transformed terminates
 *   2. Result equivalence: when both terminate, results are equivalent
 *      (modulo fresh variables introduced by the transformation)
 *
 * Usage: pass_correct fresh (\fuel. run_function fuel fn s)
 *                           (\fuel. run_function fuel fn' s)
 *)
Definition pass_correct_def:
  pass_correct fresh exec1 exec2 <=>
    (* Termination equivalence *)
    ((?fuel. terminates (exec1 fuel)) <=> (?fuel'. terminates (exec2 fuel'))) /\
    (* Result equivalence when both terminate *)
    (!fuel fuel'.
       terminates (exec1 fuel) /\ terminates (exec2 fuel') ==>
       result_equiv fresh (exec1 fuel) (exec2 fuel'))
End
