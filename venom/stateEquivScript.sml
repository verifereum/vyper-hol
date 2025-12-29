(*
 * State Equivalence Definitions
 *
 * This theory defines state equivalence and basic properties.
 * State equivalence is used to prove that transformations preserve semantics.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - state_equiv           : Main state equivalence predicate
 *   - result_equiv          : Equivalence for exec_result
 *   - var_equiv             : Variable-only equivalence
 *
 * TOP-LEVEL THEOREMS:
 *   - state_equiv_refl/sym/trans : Equivalence relation properties
 *   - result_equiv_refl          : Reflexivity for results
 *   - eval_operand_state_equiv   : Operand evaluation under equiv
 *
 * HELPER THEOREMS:
 *   - update_var_state_equiv     : Variable update preserves equiv
 *   - mload/mstore/sload/sstore/tload/tstore_state_equiv : Memory ops
 *   - jump_to/halt_state/revert_state_state_equiv : Control flow
 *
 * ============================================================================
 *)

Theory stateEquiv
Ancestors
  finite_map pred_set
  venomState venomInst venomSem

(* ==========================================================================
   State Equivalence Definition
   ========================================================================== *)

(* Helper: Variable equivalence - same values for all variables *)
Definition var_equiv_def:
  var_equiv s1 s2 <=>
    !v. lookup_var v s1 = lookup_var v s2
End

(* TOP-LEVEL: Full state equivalence - all state components match *)
Definition state_equiv_def:
  state_equiv s1 s2 <=>
    var_equiv s1 s2 /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_storage = s2.vs_storage /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_reverted = s2.vs_reverted /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx
End

(* ==========================================================================
   Equivalence Relation Properties
   ========================================================================== *)

(* TOP-LEVEL: Reflexivity *)
Theorem state_equiv_refl:
  !s. state_equiv s s
Proof
  rw[state_equiv_def, var_equiv_def]
QED

(* TOP-LEVEL: Symmetry *)
Theorem state_equiv_sym:
  !s1 s2. state_equiv s1 s2 ==> state_equiv s2 s1
Proof
  rw[state_equiv_def, var_equiv_def]
QED

(* TOP-LEVEL: Transitivity *)
Theorem state_equiv_trans:
  !s1 s2 s3. state_equiv s1 s2 /\ state_equiv s2 s3 ==> state_equiv s1 s3
Proof
  rw[state_equiv_def, var_equiv_def]
QED

(* ==========================================================================
   Result Equivalence
   ========================================================================== *)

(* TOP-LEVEL: Equivalence for exec_result values *)
Definition result_equiv_def:
  result_equiv (OK s1) (OK s2) = state_equiv s1 s2 /\
  result_equiv (Halt s1) (Halt s2) = state_equiv s1 s2 /\
  result_equiv (Revert s1) (Revert s2) = state_equiv s1 s2 /\
  result_equiv (Error e1) (Error e2) = T /\  (* Any error equiv to any error *)
  result_equiv _ _ = F
End

(* TOP-LEVEL: Reflexivity for result_equiv *)
Theorem result_equiv_refl:
  !r. result_equiv r r
Proof
  Cases >> rw[result_equiv_def, state_equiv_refl]
QED

(* Helper simp theorems: These are [simp] rules for automatic rewriting *)
Theorem result_equiv_error[simp]:
  result_equiv (Error e) (Error e) = T
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_ok[simp]:
  result_equiv (OK s1) (OK s2) = state_equiv s1 s2
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_halt[simp]:
  result_equiv (Halt s1) (Halt s2) = state_equiv s1 s2
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_revert[simp]:
  result_equiv (Revert s1) (Revert s2) = state_equiv s1 s2
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_error_any[simp]:
  result_equiv (Error e1) (Error e2) = T
Proof
  rw[result_equiv_def]
QED

(* Mismatch cases are all false - consolidated theorem *)
Theorem result_equiv_mismatch[simp]:
  result_equiv (OK s) (Halt s') = F /\
  result_equiv (OK s) (Revert s') = F /\
  result_equiv (OK s) (Error e) = F /\
  result_equiv (Halt s) (OK s') = F /\
  result_equiv (Halt s) (Revert s') = F /\
  result_equiv (Halt s) (Error e) = F /\
  result_equiv (Revert s) (OK s') = F /\
  result_equiv (Revert s) (Halt s') = F /\
  result_equiv (Revert s) (Error e) = F /\
  result_equiv (Error e) (OK s) = F /\
  result_equiv (Error e) (Halt s) = F /\
  result_equiv (Error e) (Revert s) = F
Proof
  rw[result_equiv_def]
QED

(* ==========================================================================
   Operand Evaluation Preserves Equivalence
   ========================================================================== *)

(* Helper: Evaluating an operand gives same result under state_equiv *)
Theorem eval_operand_state_equiv:
  !op s1 s2.
    state_equiv s1 s2 ==>
    eval_operand op s1 = eval_operand op s2
Proof
  Cases_on `op` >>
  rw[eval_operand_def, state_equiv_def, var_equiv_def]
QED

(* ==========================================================================
   State Mutation Operations Preserve Equivalence
   ========================================================================== *)

(* Helper: Variable update preserves state_equiv *)
Theorem update_var_state_equiv:
  !x v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (update_var x v s1) (update_var x v s2)
Proof
  rw[state_equiv_def, var_equiv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem mload_state_equiv:
  !offset s1 s2.
    state_equiv s1 s2 ==>
    mload offset s1 = mload offset s2
Proof
  rw[mload_def, state_equiv_def]
QED

Theorem mstore_state_equiv:
  !offset v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (mstore offset v s1) (mstore offset v s2)
Proof
  rw[state_equiv_def, var_equiv_def, mstore_def, lookup_var_def]
QED

Theorem write_memory_with_expansion_state_equiv:
  !offset bytes s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (write_memory_with_expansion offset bytes s1)
                (write_memory_with_expansion offset bytes s2)
Proof
  rw[state_equiv_def, var_equiv_def, write_memory_with_expansion_def, lookup_var_def]
QED

Theorem sload_state_equiv:
  !key s1 s2.
    state_equiv s1 s2 ==>
    sload key s1 = sload key s2
Proof
  rw[sload_def, state_equiv_def]
QED

Theorem sstore_state_equiv:
  !key v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (sstore key v s1) (sstore key v s2)
Proof
  rw[state_equiv_def, var_equiv_def, sstore_def, lookup_var_def]
QED

Theorem tload_state_equiv:
  !key s1 s2.
    state_equiv s1 s2 ==>
    tload key s1 = tload key s2
Proof
  rw[tload_def, state_equiv_def]
QED

Theorem tstore_state_equiv:
  !key v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (tstore key v s1) (tstore key v s2)
Proof
  rw[state_equiv_def, var_equiv_def, tstore_def, lookup_var_def]
QED

Theorem jump_to_state_equiv:
  !lbl s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (jump_to lbl s1) (jump_to lbl s2)
Proof
  rw[state_equiv_def, var_equiv_def, jump_to_def, lookup_var_def]
QED

Theorem halt_state_state_equiv:
  !s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (halt_state s1) (halt_state s2)
Proof
  rw[state_equiv_def, var_equiv_def, halt_state_def, lookup_var_def]
QED

Theorem revert_state_state_equiv:
  !s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (revert_state s1) (revert_state s2)
Proof
  rw[state_equiv_def, var_equiv_def, revert_state_def, lookup_var_def]
QED

(* ==========================================================================
   Semantic Equivalence Hierarchy
   ==========================================================================
 *
 * Different compiler optimizations require different levels of equivalence.
 * We define a hierarchy from weakest to strongest:
 *
 * 1. observable_equiv - Only externally visible effects
 *    Use for: Final transaction results, cross-contract equivalence
 *
 * 2. execution_equiv_except - All state except control flow fields
 *    Use for: Terminal states (Halt/Revert), control-flow optimizations
 *
 * 3. state_equiv_except - Full state comparison
 *    Use for: Same-path execution, step-by-step simulation
 *
 * The hierarchy satisfies: state_equiv_except ⊆ execution_equiv_except ⊆ observable_equiv
 *)

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
 * PURPOSE: State equivalence ignoring control flow fields. This is appropriate
 * for terminal states (Halt/Revert) where control flow is irrelevant.
 *
 * FIELDS COMPARED: All except control flow (vs_current_bb, vs_inst_idx, vs_prev_bb)
 *
 * WHY IGNORE CONTROL FLOW:
 *   - Once execution terminates (Halt/Revert), control flow is meaningless
 *   - Different code paths may reach the same result via different routes
 *   - Control-flow optimizations (like revert-to-assert) change paths
 *
 * USE FOR: Comparing terminal states, proving control-flow optimizations correct
 *)
Definition execution_equiv_except_def:
  execution_equiv_except vars s1 s2 <=>
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
 * FIELDS COMPARED: All fields (including control flow)
 *
 * WHY INCLUDE CONTROL FLOW:
 *   - For OK results that continue execution, control flow determines next step
 *   - PHI nodes depend on vs_prev_bb to resolve values
 *   - Same-path proofs (CSE, dead code elim) need full state matching
 *
 * USE FOR: Step-by-step simulation, same-path optimizations, PHI-related proofs
 *)
Definition state_equiv_except_def:
  state_equiv_except vars s1 s2 <=>
    execution_equiv_except vars s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb
End

(* ==========================================================================
   Equivalence Relation Properties for observable_equiv
   ========================================================================== *)

Theorem observable_equiv_refl:
  !s. observable_equiv s s
Proof
  rw[observable_equiv_def]
QED

Theorem observable_equiv_sym:
  !s1 s2. observable_equiv s1 s2 ==> observable_equiv s2 s1
Proof
  rw[observable_equiv_def]
QED

Theorem observable_equiv_trans:
  !s1 s2 s3.
    observable_equiv s1 s2 /\ observable_equiv s2 s3 ==>
    observable_equiv s1 s3
Proof
  rw[observable_equiv_def]
QED

(* ==========================================================================
   Equivalence Relation Properties for execution_equiv_except
   ========================================================================== *)

Theorem execution_equiv_except_refl:
  !vars s. execution_equiv_except vars s s
Proof
  rw[execution_equiv_except_def]
QED

Theorem execution_equiv_except_sym:
  !vars s1 s2.
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars s2 s1
Proof
  rw[execution_equiv_except_def]
QED

Theorem execution_equiv_except_trans:
  !vars s1 s2 s3.
    execution_equiv_except vars s1 s2 /\
    execution_equiv_except vars s2 s3 ==>
    execution_equiv_except vars s1 s3
Proof
  rw[execution_equiv_except_def]
QED

Theorem execution_equiv_except_subset:
  !vars1 vars2 s1 s2.
    execution_equiv_except vars1 s1 s2 /\
    vars1 SUBSET vars2 ==>
    execution_equiv_except vars2 s1 s2
Proof
  rw[execution_equiv_except_def, SUBSET_DEF] >> metis_tac[]
QED

(* ==========================================================================
   Equivalence Relation Properties for state_equiv_except
   ========================================================================== *)

Theorem state_equiv_except_refl:
  !vars s. state_equiv_except vars s s
Proof
  rw[state_equiv_except_def, execution_equiv_except_def]
QED

Theorem state_equiv_except_sym:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars s2 s1
Proof
  rw[state_equiv_except_def, execution_equiv_except_def]
QED

Theorem state_equiv_except_trans:
  !vars s1 s2 s3.
    state_equiv_except vars s1 s2 /\
    state_equiv_except vars s2 s3 ==>
    state_equiv_except vars s1 s3
Proof
  rw[state_equiv_except_def, execution_equiv_except_def]
QED

Theorem state_equiv_implies_except:
  !vars s1 s2.
    state_equiv s1 s2 ==>
    state_equiv_except vars s1 s2
Proof
  rw[state_equiv_def, var_equiv_def, state_equiv_except_def, execution_equiv_except_def]
QED

Theorem state_equiv_except_empty:
  !s1 s2.
    state_equiv_except {} s1 s2 <=>
    (!v. lookup_var v s1 = lookup_var v s2) /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_storage = s2.vs_storage /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_reverted = s2.vs_reverted /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx
Proof
  rw[state_equiv_except_def, execution_equiv_except_def, EQ_IMP_THM]
QED

(* ==========================================================================
   Lifting Lemmas: Stronger Equivalence Implies Weaker
   ========================================================================== *)

Theorem state_equiv_except_implies_execution:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    execution_equiv_except vars s1 s2
Proof
  rw[state_equiv_except_def]
QED

Theorem execution_equiv_except_implies_observable:
  !vars s1 s2.
    execution_equiv_except vars s1 s2 ==>
    observable_equiv s1 s2
Proof
  rw[execution_equiv_except_def, observable_equiv_def]
QED

Theorem state_equiv_except_implies_observable:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    observable_equiv s1 s2
Proof
  metis_tac[state_equiv_except_implies_execution, execution_equiv_except_implies_observable]
QED

(* ==========================================================================
   Result Equivalence with Variable Exceptions
   ========================================================================== *)

(*
 * PURPOSE: Extend equivalence to exec_result, using the appropriate level
 * of equivalence for each result type.
 *
 * KEY DESIGN DECISION:
 *   - OK: Uses state_equiv_except (full state comparison)
 *     Reason: Execution continues, so control flow matters for next step
 *
 *   - Halt/Revert: Uses execution_equiv_except (ignores control flow)
 *     Reason: Execution has terminated, control flow is irrelevant
 *     This enables proving control-flow optimizations correct
 *
 *   - Error: Always equivalent (error messages may differ)
 *)
Definition result_equiv_except_def:
  result_equiv_except vars (OK s1) (OK s2) = state_equiv_except vars s1 s2 /\
  result_equiv_except vars (Halt s1) (Halt s2) = execution_equiv_except vars s1 s2 /\
  result_equiv_except vars (Revert s1) (Revert s2) = execution_equiv_except vars s1 s2 /\
  result_equiv_except vars (Error e1) (Error e2) = T /\
  result_equiv_except vars _ _ = F
End

Theorem result_equiv_except_refl:
  !vars r. result_equiv_except vars r r
Proof
  gen_tac >> Cases >>
  rw[result_equiv_except_def, state_equiv_except_refl, execution_equiv_except_refl]
QED

Theorem result_equiv_except_ok[simp]:
  result_equiv_except vars (OK s1) (OK s2) = state_equiv_except vars s1 s2
Proof
  rw[result_equiv_except_def]
QED

Theorem result_equiv_except_halt[simp]:
  result_equiv_except vars (Halt s1) (Halt s2) = execution_equiv_except vars s1 s2
Proof
  rw[result_equiv_except_def]
QED

Theorem result_equiv_except_revert[simp]:
  result_equiv_except vars (Revert s1) (Revert s2) = execution_equiv_except vars s1 s2
Proof
  rw[result_equiv_except_def]
QED

Theorem result_equiv_except_error[simp]:
  result_equiv_except vars (Error e1) (Error e2) = T
Proof
  rw[result_equiv_except_def]
QED

Theorem result_equiv_except_mismatch[simp]:
  result_equiv_except vars (OK s) (Halt s') = F /\
  result_equiv_except vars (OK s) (Revert s') = F /\
  result_equiv_except vars (OK s) (Error e) = F /\
  result_equiv_except vars (Halt s) (OK s') = F /\
  result_equiv_except vars (Halt s) (Revert s') = F /\
  result_equiv_except vars (Halt s) (Error e) = F /\
  result_equiv_except vars (Revert s) (OK s') = F /\
  result_equiv_except vars (Revert s) (Halt s') = F /\
  result_equiv_except vars (Revert s) (Error e) = F /\
  result_equiv_except vars (Error e) (OK s) = F /\
  result_equiv_except vars (Error e) (Halt s) = F /\
  result_equiv_except vars (Error e) (Revert s) = F
Proof
  rw[result_equiv_except_def]
QED

(* ==========================================================================
   Update Preserves execution_equiv_except
   ========================================================================== *)

Theorem update_var_in_execution_equiv_preserves:
  !vars x v1 v2 s1 s2.
    x IN vars /\
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (update_var x v1 s1) (update_var x v2 s2)
Proof
  rw[execution_equiv_except_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `x = v` >> gvs[]
QED

Theorem update_var_same_execution_equiv_preserves:
  !vars x v s1 s2.
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (update_var x v s1) (update_var x v s2)
Proof
  rw[execution_equiv_except_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem update_var_execution_equiv_one_side:
  !vars x v s1 s2.
    x IN vars /\
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (update_var x v s1) s2
Proof
  rw[execution_equiv_except_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `v' = x` >> gvs[]
QED

(* ==========================================================================
   Update Preserves state_equiv_except
   ========================================================================== *)

Theorem update_var_in_except_preserves:
  !vars x v1 v2 s1 s2.
    x IN vars /\
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (update_var x v1 s1) (update_var x v2 s2)
Proof
  rw[state_equiv_except_def, execution_equiv_except_def,
     update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `x = v` >> gvs[]
QED

Theorem update_var_same_preserves:
  !vars x v s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (update_var x v s1) (update_var x v s2)
Proof
  rw[state_equiv_except_def, execution_equiv_except_def,
     update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem update_var_except_one_side:
  !vars x v s1 s2.
    x IN vars /\
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (update_var x v s1) s2
Proof
  rw[state_equiv_except_def, execution_equiv_except_def,
     update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `v' = x` >> gvs[]
QED

(* ==========================================================================
   Operand Evaluation under equivalence
   ========================================================================== *)

Theorem eval_operand_execution_equiv:
  !vars op s1 s2.
    execution_equiv_except vars s1 s2 /\
    (!x. op = Var x ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  Cases_on `op` >>
  rw[eval_operand_def, execution_equiv_except_def, lookup_var_def]
QED

Theorem eval_operand_except:
  !vars op s1 s2.
    state_equiv_except vars s1 s2 /\
    (!x. op = Var x ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  rw[] >> irule eval_operand_execution_equiv >>
  metis_tac[state_equiv_except_implies_execution]
QED

(* ==========================================================================
   Control Flow Preserves execution_equiv_except
   ========================================================================== *)

Theorem halt_state_execution_equiv_preserves:
  !vars s1 s2.
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (halt_state s1) (halt_state s2)
Proof
  rw[execution_equiv_except_def, halt_state_def, lookup_var_def]
QED

Theorem revert_state_execution_equiv_preserves:
  !vars s1 s2.
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (revert_state s1) (revert_state s2)
Proof
  rw[execution_equiv_except_def, revert_state_def, lookup_var_def]
QED

Theorem halt_state_from_state_except:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (halt_state s1) (halt_state s2)
Proof
  metis_tac[state_equiv_except_implies_execution, halt_state_execution_equiv_preserves]
QED

Theorem revert_state_from_state_except:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (revert_state s1) (revert_state s2)
Proof
  metis_tac[state_equiv_except_implies_execution, revert_state_execution_equiv_preserves]
QED

(* ==========================================================================
   Control Flow Preserves state_equiv_except
   ========================================================================== *)

Theorem jump_to_except_preserves:
  !vars lbl s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (jump_to lbl s1) (jump_to lbl s2)
Proof
  rw[state_equiv_except_def, execution_equiv_except_def,
     jump_to_def, lookup_var_def]
QED

Theorem halt_state_except_preserves:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (halt_state s1) (halt_state s2)
Proof
  rw[state_equiv_except_def, execution_equiv_except_def,
     halt_state_def, lookup_var_def]
QED

Theorem revert_state_except_preserves:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (revert_state s1) (revert_state s2)
Proof
  rw[state_equiv_except_def, execution_equiv_except_def,
     revert_state_def, lookup_var_def]
QED

(* ==========================================================================
   Widening the Exception Set
   ========================================================================== *)

Theorem state_equiv_except_subset:
  !vars1 vars2 s1 s2.
    state_equiv_except vars1 s1 s2 /\
    vars1 SUBSET vars2 ==>
    state_equiv_except vars2 s1 s2
Proof
  rw[state_equiv_except_def, execution_equiv_except_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem result_equiv_except_subset:
  !vars1 vars2 r1 r2.
    result_equiv_except vars1 r1 r2 /\
    vars1 SUBSET vars2 ==>
    result_equiv_except vars2 r1 r2
Proof
  rpt gen_tac >> Cases_on `r1` >> Cases_on `r2` >>
  rw[result_equiv_except_def] >| [
    irule state_equiv_except_subset >> metis_tac[],
    irule execution_equiv_except_subset >> metis_tac[],
    irule execution_equiv_except_subset >> metis_tac[]
  ]
QED

(* ==========================================================================
   Memory/Storage Operations Preserve execution_equiv_except
   ========================================================================== *)

Theorem mstore_execution_equiv_preserves:
  !vars addr val s1 s2.
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (mstore addr val s1) (mstore addr val s2)
Proof
  rw[execution_equiv_except_def, mstore_def, lookup_var_def]
QED

Theorem mload_execution_equiv_same:
  !vars addr s1 s2.
    execution_equiv_except vars s1 s2 ==>
    mload addr s1 = mload addr s2
Proof
  rw[execution_equiv_except_def, mload_def]
QED

Theorem sstore_execution_equiv_preserves:
  !vars key val s1 s2.
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (sstore key val s1) (sstore key val s2)
Proof
  rw[execution_equiv_except_def, sstore_def, lookup_var_def]
QED

Theorem sload_execution_equiv_same:
  !vars key s1 s2.
    execution_equiv_except vars s1 s2 ==>
    sload key s1 = sload key s2
Proof
  rw[execution_equiv_except_def, sload_def]
QED

Theorem tstore_execution_equiv_preserves:
  !vars key val s1 s2.
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (tstore key val s1) (tstore key val s2)
Proof
  rw[execution_equiv_except_def, tstore_def, lookup_var_def]
QED

Theorem tload_execution_equiv_same:
  !vars key s1 s2.
    execution_equiv_except vars s1 s2 ==>
    tload key s1 = tload key s2
Proof
  rw[execution_equiv_except_def, tload_def]
QED

(* ==========================================================================
   Memory/Storage Operations Preserve state_equiv_except
   ========================================================================== *)

Theorem mstore_except_preserves:
  !vars addr val s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (mstore addr val s1) (mstore addr val s2)
Proof
  rw[state_equiv_except_def, execution_equiv_except_def,
     mstore_def, lookup_var_def]
QED

Theorem mload_except_same:
  !vars addr s1 s2.
    state_equiv_except vars s1 s2 ==>
    mload addr s1 = mload addr s2
Proof
  rw[state_equiv_except_def, execution_equiv_except_def, mload_def]
QED

Theorem sstore_except_preserves:
  !vars key val s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (sstore key val s1) (sstore key val s2)
Proof
  rw[state_equiv_except_def, execution_equiv_except_def,
     sstore_def, lookup_var_def]
QED

Theorem sload_except_same:
  !vars key s1 s2.
    state_equiv_except vars s1 s2 ==>
    sload key s1 = sload key s2
Proof
  rw[state_equiv_except_def, execution_equiv_except_def, sload_def]
QED

Theorem tstore_except_preserves:
  !vars key val s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (tstore key val s1) (tstore key val s2)
Proof
  rw[state_equiv_except_def, execution_equiv_except_def,
     tstore_def, lookup_var_def]
QED

Theorem tload_except_same:
  !vars key s1 s2.
    state_equiv_except vars s1 s2 ==>
    tload key s1 = tload key s2
Proof
  rw[state_equiv_except_def, execution_equiv_except_def, tload_def]
QED

Theorem write_memory_with_expansion_except_preserves:
  !vars offset bytes s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars
      (write_memory_with_expansion offset bytes s1)
      (write_memory_with_expansion offset bytes s2)
Proof
  rw[state_equiv_except_def, execution_equiv_except_def,
     write_memory_with_expansion_def, lookup_var_def]
QED
