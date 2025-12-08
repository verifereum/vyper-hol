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
  finite_map
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
    s1.vs_reverted = s2.vs_reverted
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

