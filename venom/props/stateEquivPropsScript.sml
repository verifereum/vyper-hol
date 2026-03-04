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

(* state_equiv is reflexive *)
Theorem state_equiv_refl:
  !s. state_equiv s s
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_refl
QED

(* state_equiv is symmetric *)
Theorem state_equiv_sym:
  !s1 s2. state_equiv s1 s2 ==> state_equiv s2 s1
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_sym
QED

(* state_equiv is transitive *)
Theorem state_equiv_trans:
  !s1 s2 s3. state_equiv s1 s2 /\ state_equiv s2 s3 ==> state_equiv s1 s3
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_trans
QED

(* ==========================================================================
   Operand Evaluation Preserves Equivalence
   ========================================================================== *)

(* Operand evaluation gives same result on equivalent states *)
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

(* Updating same variable with same value preserves state equivalence *)
Theorem update_var_state_equiv:
  !x v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (update_var x v s1) (update_var x v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.update_var_state_equiv
QED

(* Memory store preserves state equivalence *)
Theorem mstore_state_equiv:
  !offset v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (mstore offset v s1) (mstore offset v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.mstore_state_equiv
QED

(* Memory write with expansion preserves state equivalence *)
Theorem write_memory_with_expansion_state_equiv:
  !offset bytes s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (write_memory_with_expansion offset bytes s1)
                (write_memory_with_expansion offset bytes s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.write_memory_with_expansion_state_equiv
QED

(* Storage store preserves state equivalence *)
Theorem sstore_state_equiv:
  !key v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (sstore key v s1) (sstore key v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.sstore_state_equiv
QED

(* Transient store preserves state equivalence *)
Theorem tstore_state_equiv:
  !key v s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (tstore key v s1) (tstore key v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.tstore_state_equiv
QED

(* Jump preserves state equivalence *)
Theorem jump_to_state_equiv:
  !lbl s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (jump_to lbl s1) (jump_to lbl s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.jump_to_state_equiv
QED

(* Halt preserves state equivalence *)
Theorem halt_state_state_equiv:
  !s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (halt_state s1) (halt_state s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.halt_state_state_equiv
QED

(* Revert preserves state equivalence *)
Theorem revert_state_state_equiv:
  !s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (revert_state s1) (revert_state s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.revert_state_state_equiv
QED

(* ==========================================================================
   Equivalence Relation Properties for execution_equiv_except
   ========================================================================== *)

(* execution_equiv_except is reflexive *)
Theorem execution_equiv_except_refl:
  !vars s. execution_equiv_except vars s s
Proof
  ACCEPT_TAC stateEquivProofsTheory.execution_equiv_except_refl
QED

(* execution_equiv_except is transitive *)
Theorem execution_equiv_except_trans:
  !vars s1 s2 s3.
    execution_equiv_except vars s1 s2 /\
    execution_equiv_except vars s2 s3 ==>
    execution_equiv_except vars s1 s3
Proof
  ACCEPT_TAC stateEquivProofsTheory.execution_equiv_except_trans
QED

(* Widening the exception set preserves execution_equiv_except *)
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

(* state_equiv_except is reflexive *)
Theorem state_equiv_except_refl:
  !vars s. state_equiv_except vars s s
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_except_refl
QED

(* state_equiv_except is transitive *)
Theorem state_equiv_except_trans:
  !vars s1 s2 s3.
    state_equiv_except vars s1 s2 /\
    state_equiv_except vars s2 s3 ==>
    state_equiv_except vars s1 s3
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_except_trans
QED

(* Full state equivalence implies state_equiv_except for any variable set *)
Theorem state_equiv_implies_except:
  !vars s1 s2.
    state_equiv s1 s2 ==>
    state_equiv_except vars s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_implies_except
QED

(* ==========================================================================
   Update Preserves state_equiv_except
   ========================================================================== *)

(* Updating same variable with same value preserves state_equiv_except *)
Theorem update_var_same_preserves:
  !vars x v s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (update_var x v s1) (update_var x v s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.update_var_same_preserves
QED

(* ==========================================================================
   Operand Evaluation under state_equiv_except
   ========================================================================== *)

(* Operand evaluation gives same result when operand's variable is not in exception set *)
Theorem eval_operand_except:
  !vars op s1 s2.
    state_equiv_except vars s1 s2 /\
    (!x. op = Var x ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.eval_operand_except
QED

(* ==========================================================================
   Control Flow Preserves execution_equiv_except (from state_equiv_except)
   ========================================================================== *)

(* halt_state on state_equiv_except states gives execution_equiv_except *)
Theorem halt_state_from_state_except:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    execution_equiv_except vars (halt_state s1) (halt_state s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.halt_state_from_state_except
QED

(* revert_state on state_equiv_except states gives execution_equiv_except *)
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

(* Jump preserves state_equiv_except *)
Theorem jump_to_except_preserves:
  !vars lbl s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (jump_to lbl s1) (jump_to lbl s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.jump_to_except_preserves
QED

(* Revert preserves state_equiv_except *)
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

(* Widening exception set preserves state_equiv_except *)
Theorem state_equiv_except_subset:
  !vars1 vars2 s1 s2.
    state_equiv_except vars1 s1 s2 /\
    vars1 SUBSET vars2 ==>
    state_equiv_except vars2 s1 s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.state_equiv_except_subset
QED

(* Widening exception set preserves result_equiv_except *)
Theorem result_equiv_except_subset:
  !vars1 vars2 r1 r2.
    result_equiv_except vars1 r1 r2 /\
    vars1 SUBSET vars2 ==>
    result_equiv_except vars2 r1 r2
Proof
  ACCEPT_TAC stateEquivProofsTheory.result_equiv_except_subset
QED

(* ==========================================================================
   Memory/Storage Operations Preserve state_equiv_except
   ========================================================================== *)

(* Memory store preserves state_equiv_except *)
Theorem mstore_except_preserves:
  !vars addr val s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (mstore addr val s1) (mstore addr val s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.mstore_except_preserves
QED

(* Memory load gives same result under state_equiv_except *)
Theorem mload_except_same:
  !vars addr s1 s2.
    state_equiv_except vars s1 s2 ==>
    mload addr s1 = mload addr s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.mload_except_same
QED

(* Storage store preserves state_equiv_except *)
Theorem sstore_except_preserves:
  !vars key val s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (sstore key val s1) (sstore key val s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.sstore_except_preserves
QED

(* Storage load gives same result under state_equiv_except *)
Theorem sload_except_same:
  !vars key s1 s2.
    state_equiv_except vars s1 s2 ==>
    sload key s1 = sload key s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.sload_except_same
QED

(* Transient store preserves state_equiv_except *)
Theorem tstore_except_preserves:
  !vars key val s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (tstore key val s1) (tstore key val s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.tstore_except_preserves
QED

(* Transient load gives same result under state_equiv_except *)
Theorem tload_except_same:
  !vars key s1 s2.
    state_equiv_except vars s1 s2 ==>
    tload key s1 = tload key s2
Proof
  ACCEPT_TAC stateEquivProofsTheory.tload_except_same
QED

(* Memory write with expansion preserves state_equiv_except *)
Theorem write_memory_with_expansion_except_preserves:
  !vars offset bytes s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars
      (write_memory_with_expansion offset bytes s1)
      (write_memory_with_expansion offset bytes s2)
Proof
  ACCEPT_TAC stateEquivProofsTheory.write_memory_with_expansion_except_preserves
QED
