(*
 * State Equivalence Properties (Statements Only)
 *
 * Re-exports all theorems from stateEquivProofs via ACCEPT_TAC.
 * Proofs live in proofs/stateEquivProofsScript.sml.
 *)

Theory stateEquivProps
Ancestors
  stateEquivProofs

(* ==========================================================================
   Equivalence Relation Properties
   ========================================================================== *)

Theorem state_equiv_refl:
  !s. state_equiv s s
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_refl
QED

Theorem state_equiv_sym:
  !s1 s2. state_equiv s1 s2 ==> state_equiv s2 s1
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_sym
QED

Theorem state_equiv_trans:
  !s1 s2 s3. state_equiv s1 s2 /\ state_equiv s2 s3 ==> state_equiv s1 s3
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_trans
QED

(* ==========================================================================
   Result Equivalence Properties
   ========================================================================== *)

Theorem result_equiv_refl:
  !r. result_equiv r r
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_refl
QED

Theorem result_equiv_error[simp]:
  result_equiv (Error e) (Error e) = T
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_error
QED

Theorem result_equiv_ok[simp]:
  result_equiv (OK s1) (OK s2) = state_equiv s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_ok
QED

Theorem result_equiv_halt[simp]:
  result_equiv (Halt s1) (Halt s2) = state_equiv s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_halt
QED

Theorem result_equiv_revert[simp]:
  result_equiv (Revert s1) (Revert s2) = state_equiv s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_revert
QED

Theorem result_equiv_error_any[simp]:
  result_equiv (Error e1) (Error e2) = T
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_error_any
QED

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
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_mismatch
QED

(* ==========================================================================
   Operand Evaluation Preserves Equivalence
   ========================================================================== *)

Theorem eval_operand_state_equiv:
  !op s1 s2.
    state_equiv s1 s2 ==>
    eval_operand op s1 = eval_operand op s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.eval_operand_state_equiv
QED

(* ==========================================================================
   State Mutation Operations Preserve Equivalence
   ========================================================================== *)

Theorem update_var_state_equiv:
  !x v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (update_var x v s1) (update_var x v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.update_var_state_equiv
QED

Theorem mload_state_equiv:
  !offset s1 s2.
    state_equiv s1 s2 ==>
    mload offset s1 = mload offset s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.mload_state_equiv
QED

Theorem mstore_state_equiv:
  !offset v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (mstore offset v s1) (mstore offset v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.mstore_state_equiv
QED

Theorem write_memory_with_expansion_state_equiv:
  !offset bytes s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (write_memory_with_expansion offset bytes s1)
                (write_memory_with_expansion offset bytes s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.write_memory_with_expansion_state_equiv
QED

Theorem sload_state_equiv:
  !key s1 s2.
    state_equiv s1 s2 ==>
    sload key s1 = sload key s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.sload_state_equiv
QED

Theorem sstore_state_equiv:
  !key v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (sstore key v s1) (sstore key v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.sstore_state_equiv
QED

Theorem tload_state_equiv:
  !key s1 s2.
    state_equiv s1 s2 ==>
    tload key s1 = tload key s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.tload_state_equiv
QED

Theorem tstore_state_equiv:
  !key v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (tstore key v s1) (tstore key v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.tstore_state_equiv
QED

Theorem jump_to_state_equiv:
  !lbl s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (jump_to lbl s1) (jump_to lbl s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.jump_to_state_equiv
QED

Theorem halt_state_state_equiv:
  !s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (halt_state s1) (halt_state s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.halt_state_state_equiv
QED

Theorem revert_state_state_equiv:
  !s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (revert_state s1) (revert_state s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.revert_state_state_equiv
QED

(* ==========================================================================
   Equivalence Relation Properties for observable_equiv
   ========================================================================== *)

Theorem observable_equiv_refl:
  !s. observable_equiv s s
Proof
  ACCEPT_TAC stateEquivProofsTheory.observable_equiv_refl
QED

Theorem observable_equiv_sym:
  !s1 s2. observable_equiv s1 s2 ==> observable_equiv s2 s1
Proof
  ACCEPT_TAC stateEquivProofsTheory.observable_equiv_sym
QED

Theorem observable_equiv_trans:
  !s1 s2 s3.
    observable_equiv s1 s2 /\ observable_equiv s2 s3 ==>
    observable_equiv s1 s3
Proof
  ACCEPT_TAC stateEquivProofsTheory.observable_equiv_trans
QED

(* ==========================================================================
   Equivalence Relation Properties for execution_equiv_except
   ========================================================================== *)

Theorem execution_equiv_except_refl:
  !vars s. execution_equiv_except vars s s
Proof
  ACCEPT_TAC stateEquivProofsTheory.execution_equiv_except_refl
QED

Theorem execution_equiv_except_sym:
  !vars s1 s2.
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars s2 s1
Proof
  ACCEPT_TAC stateEquivProofsTheory.execution_equiv_except_sym
QED

Theorem execution_equiv_except_trans:
  !vars s1 s2 s3.
    execution_equiv_except vars s1 s2 /\
    execution_equiv_except vars s2 s3 ==>
    execution_equiv_except vars s1 s3
Proof
  ACCEPT_TAC stateEquivProofsTheory.execution_equiv_except_trans
QED

Theorem execution_equiv_except_subset:
  !vars1 vars2 s1 s2.
    execution_equiv_except vars1 s1 s2 /\
    vars1 SUBSET vars2 ==>
    execution_equiv_except vars2 s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.execution_equiv_except_subset
QED

(* ==========================================================================
   Equivalence Relation Properties for state_equiv_except
   ========================================================================== *)

Theorem state_equiv_except_refl:
  !vars s. state_equiv_except vars s s
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_except_refl
QED

Theorem state_equiv_except_sym:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars s2 s1
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_except_sym
QED

Theorem state_equiv_except_trans:
  !vars s1 s2 s3.
    state_equiv_except vars s1 s2 /\
    state_equiv_except vars s2 s3 ==>
    state_equiv_except vars s1 s3
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_except_trans
QED

Theorem state_equiv_implies_except:
  !vars s1 s2.
    state_equiv s1 s2 ==>
    state_equiv_except vars s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_implies_except
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
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_except_empty
QED

(* ==========================================================================
   Lifting Lemmas: Stronger Equivalence Implies Weaker
   ========================================================================== *)

Theorem state_equiv_except_implies_execution:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    execution_equiv_except vars s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_except_implies_execution
QED

Theorem execution_equiv_except_implies_observable:
  !vars s1 s2.
    execution_equiv_except vars s1 s2 ==>
    observable_equiv s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.execution_equiv_except_implies_observable
QED

Theorem state_equiv_except_implies_observable:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    observable_equiv s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_except_implies_observable
QED

(* ==========================================================================
   Result Equivalence with Variable Exceptions - Properties
   ========================================================================== *)

Theorem result_equiv_except_refl:
  !vars r. result_equiv_except vars r r
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_except_refl
QED

Theorem result_equiv_except_ok[simp]:
  result_equiv_except vars (OK s1) (OK s2) = state_equiv_except vars s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_except_ok
QED

Theorem result_equiv_except_halt[simp]:
  result_equiv_except vars (Halt s1) (Halt s2) = execution_equiv_except vars s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_except_halt
QED

Theorem result_equiv_except_revert[simp]:
  result_equiv_except vars (Revert s1) (Revert s2) = execution_equiv_except vars s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_except_revert
QED

Theorem result_equiv_except_error[simp]:
  result_equiv_except vars (Error e1) (Error e2) = T
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_except_error
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
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_except_mismatch
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
  ACCEPT_TAC stateEquivProofsTheory.update_var_in_execution_equiv_preserves
QED

Theorem update_var_same_execution_equiv_preserves:
  !vars x v s1 s2.
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (update_var x v s1) (update_var x v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.update_var_same_execution_equiv_preserves
QED

Theorem update_var_execution_equiv_one_side:
  !vars x v s1 s2.
    x IN vars /\
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (update_var x v s1) s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.update_var_execution_equiv_one_side
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
  ACCEPT_TAC stateEquivProofsTheory.update_var_in_except_preserves
QED

Theorem update_var_same_preserves:
  !vars x v s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (update_var x v s1) (update_var x v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.update_var_same_preserves
QED

Theorem update_var_except_one_side:
  !vars x v s1 s2.
    x IN vars /\
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (update_var x v s1) s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.update_var_except_one_side
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
  ACCEPT_TAC stateEquivProofsTheory.eval_operand_execution_equiv
QED

Theorem eval_operand_except:
  !vars op s1 s2.
    state_equiv_except vars s1 s2 /\
    (!x. op = Var x ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.eval_operand_except
QED

(* ==========================================================================
   Control Flow Preserves execution_equiv_except
   ========================================================================== *)

Theorem halt_state_execution_equiv_preserves:
  !vars s1 s2.
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (halt_state s1) (halt_state s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.halt_state_execution_equiv_preserves
QED

Theorem revert_state_execution_equiv_preserves:
  !vars s1 s2.
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (revert_state s1) (revert_state s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.revert_state_execution_equiv_preserves
QED

Theorem halt_state_from_state_except:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (halt_state s1) (halt_state s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.halt_state_from_state_except
QED

Theorem revert_state_from_state_except:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (revert_state s1) (revert_state s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.revert_state_from_state_except
QED

(* ==========================================================================
   Control Flow Preserves state_equiv_except
   ========================================================================== *)

Theorem jump_to_except_preserves:
  !vars lbl s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (jump_to lbl s1) (jump_to lbl s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.jump_to_except_preserves
QED

Theorem halt_state_except_preserves:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (halt_state s1) (halt_state s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.halt_state_except_preserves
QED

Theorem revert_state_except_preserves:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (revert_state s1) (revert_state s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.revert_state_except_preserves
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
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_except_subset
QED

Theorem result_equiv_except_subset:
  !vars1 vars2 r1 r2.
    result_equiv_except vars1 r1 r2 /\
    vars1 SUBSET vars2 ==>
    result_equiv_except vars2 r1 r2
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_except_subset
QED

(* ==========================================================================
   Memory/Storage Operations Preserve execution_equiv_except
   ========================================================================== *)

Theorem mstore_execution_equiv_preserves:
  !vars addr val s1 s2.
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (mstore addr val s1) (mstore addr val s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.mstore_execution_equiv_preserves
QED

Theorem mload_execution_equiv_same:
  !vars addr s1 s2.
    execution_equiv_except vars s1 s2 ==>
    mload addr s1 = mload addr s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.mload_execution_equiv_same
QED

Theorem sstore_execution_equiv_preserves:
  !vars key val s1 s2.
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (sstore key val s1) (sstore key val s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.sstore_execution_equiv_preserves
QED

Theorem sload_execution_equiv_same:
  !vars key s1 s2.
    execution_equiv_except vars s1 s2 ==>
    sload key s1 = sload key s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.sload_execution_equiv_same
QED

Theorem tstore_execution_equiv_preserves:
  !vars key val s1 s2.
    execution_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (tstore key val s1) (tstore key val s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.tstore_execution_equiv_preserves
QED

Theorem tload_execution_equiv_same:
  !vars key s1 s2.
    execution_equiv_except vars s1 s2 ==>
    tload key s1 = tload key s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.tload_execution_equiv_same
QED

(* ==========================================================================
   Memory/Storage Operations Preserve state_equiv_except
   ========================================================================== *)

Theorem mstore_except_preserves:
  !vars addr val s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (mstore addr val s1) (mstore addr val s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.mstore_except_preserves
QED

Theorem mload_except_same:
  !vars addr s1 s2.
    state_equiv_except vars s1 s2 ==>
    mload addr s1 = mload addr s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.mload_except_same
QED

Theorem sstore_except_preserves:
  !vars key val s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (sstore key val s1) (sstore key val s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.sstore_except_preserves
QED

Theorem sload_except_same:
  !vars key s1 s2.
    state_equiv_except vars s1 s2 ==>
    sload key s1 = sload key s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.sload_except_same
QED

Theorem tstore_except_preserves:
  !vars key val s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (tstore key val s1) (tstore key val s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.tstore_except_preserves
QED

Theorem tload_except_same:
  !vars key s1 s2.
    state_equiv_except vars s1 s2 ==>
    tload key s1 = tload key s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.tload_except_same
QED

Theorem write_memory_with_expansion_except_preserves:
  !vars offset bytes s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars
      (write_memory_with_expansion offset bytes s1)
      (write_memory_with_expansion offset bytes s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.write_memory_with_expansion_except_preserves
QED
