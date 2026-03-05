(*
 * State Equivalence Properties (API)
 *
 * Re-exports theorems from stateEquivProofs via ACCEPT_TAC.
 * All predicates are parameterized by a variable exception set.
 * For full equivalence, use {} as the exception set.
 *
 * TOP-LEVEL THEOREMS (21):
 *   Relation properties:
 *     state_equiv_{refl,sym,trans,subset}
 *     execution_equiv_{refl,trans,subset}
 *     result_equiv_{subset,trans}
 *   Operand evaluation:
 *     eval_operand_equiv
 *   Mutations preserve state_equiv:
 *     update_var_preserves, mstore_preserves, sstore_preserves,
 *     tstore_preserves, write_memory_with_expansion_preserves,
 *     jump_to_preserves, halt_state_preserves, revert_state_preserves
 *   Reads give same result:
 *     mload_same, sload_same, tload_same
 *)

Theory stateEquivProps
Ancestors
  stateEquivProofs

(* ==========================================================================
   Relation Properties
   ========================================================================== *)

(* state_equiv is reflexive *)
Theorem state_equiv_refl:
  !vars s. state_equiv vars s s
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_refl
QED

(* state_equiv is symmetric *)
Theorem state_equiv_sym:
  !vars s1 s2. state_equiv vars s1 s2 ==> state_equiv vars s2 s1
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_sym
QED

(* state_equiv is transitive *)
Theorem state_equiv_trans:
  !vars s1 s2 s3.
    state_equiv vars s1 s2 /\ state_equiv vars s2 s3 ==>
    state_equiv vars s1 s3
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_trans
QED

(* Widening the exception set preserves state_equiv *)
Theorem state_equiv_subset:
  !vars1 vars2 s1 s2.
    state_equiv vars1 s1 s2 /\ vars1 SUBSET vars2 ==>
    state_equiv vars2 s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_subset
QED

(* execution_equiv is reflexive *)
Theorem execution_equiv_refl:
  !vars s. execution_equiv vars s s
Proof
  ACCEPT_TAC stateEquivProofsTheory.execution_equiv_refl
QED

(* execution_equiv is transitive *)
Theorem execution_equiv_trans:
  !vars s1 s2 s3.
    execution_equiv vars s1 s2 /\ execution_equiv vars s2 s3 ==>
    execution_equiv vars s1 s3
Proof
  ACCEPT_TAC stateEquivProofsTheory.execution_equiv_trans
QED

(* Widening the exception set preserves execution_equiv *)
Theorem execution_equiv_subset:
  !vars1 vars2 s1 s2.
    execution_equiv vars1 s1 s2 /\ vars1 SUBSET vars2 ==>
    execution_equiv vars2 s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.execution_equiv_subset
QED

(* Widening the exception set preserves result_equiv *)
Theorem result_equiv_subset:
  !vars1 vars2 r1 r2.
    result_equiv vars1 r1 r2 /\ vars1 SUBSET vars2 ==>
    result_equiv vars2 r1 r2
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_subset
QED

(* result_equiv is transitive *)
Theorem result_equiv_trans:
  !vars r1 r2 r3.
    result_equiv vars r1 r2 /\ result_equiv vars r2 r3 ==>
    result_equiv vars r1 r3
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_trans
QED

(* result_equiv is the canonical instantiation of lift_result *)
Theorem result_equiv_is_lift_result:
  !vars. result_equiv vars = lift_result (state_equiv vars) (execution_equiv vars)
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_is_lift_result
QED

(* ==========================================================================
   Operand Evaluation
   ========================================================================== *)

(* Operand evaluation gives same result when variable is not in exception set *)
Theorem eval_operand_equiv:
  !vars op s1 s2.
    state_equiv vars s1 s2 /\
    (!x. op = Var x ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.eval_operand_equiv
QED

(* ==========================================================================
   Mutations Preserve state_equiv
   ========================================================================== *)

(* Updating same variable with same value preserves state_equiv *)
Theorem update_var_preserves:
  !vars x v s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (update_var x v s1) (update_var x v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.update_var_preserves
QED

(* Memory store preserves state_equiv *)
Theorem mstore_preserves:
  !vars offset v s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (mstore offset v s1) (mstore offset v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.mstore_preserves
QED

(* Storage store preserves state_equiv *)
Theorem sstore_preserves:
  !vars key v s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (sstore key v s1) (sstore key v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.sstore_preserves
QED

(* Transient store preserves state_equiv *)
Theorem tstore_preserves:
  !vars key v s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (tstore key v s1) (tstore key v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.tstore_preserves
QED

(* Memory write with expansion preserves state_equiv *)
Theorem write_memory_with_expansion_preserves:
  !vars offset bytes s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars
      (write_memory_with_expansion offset bytes s1)
      (write_memory_with_expansion offset bytes s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.write_memory_with_expansion_preserves
QED

(* Jump preserves state_equiv *)
Theorem jump_to_preserves:
  !vars lbl s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (jump_to lbl s1) (jump_to lbl s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.jump_to_preserves
QED

(* Halt preserves state_equiv *)
Theorem halt_state_preserves:
  !vars s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (halt_state s1) (halt_state s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.halt_state_preserves
QED

(* Revert preserves state_equiv *)
Theorem revert_state_preserves:
  !vars s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (revert_state s1) (revert_state s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.revert_state_preserves
QED

(* ==========================================================================
   Reads Give Same Result
   ========================================================================== *)

(* Memory load gives same result under state_equiv *)
Theorem mload_same:
  !vars addr s1 s2.
    state_equiv vars s1 s2 ==>
    mload addr s1 = mload addr s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.mload_same
QED

(* Storage load gives same result under state_equiv *)
Theorem sload_same:
  !vars key s1 s2.
    state_equiv vars s1 s2 ==>
    sload key s1 = sload key s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.sload_same
QED

(* Transient load gives same result under state_equiv *)
Theorem tload_same:
  !vars key s1 s2.
    state_equiv vars s1 s2 ==>
    tload key s1 = tload key s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.tload_same
QED
