(*
 * State Equivalence Proofs
 *
 * Internal proofs — consumers use props/stateEquivPropsScript.sml
 *
 * All predicates are parameterized by a variable exception set (vars).
 * For full equivalence, use {} as the exception set.
 *)

Theory stateEquivProofs
Ancestors
  stateEquiv venomState finite_map pred_set

(* ==========================================================================
   state_equiv: Relation Properties
   ========================================================================== *)

Theorem state_equiv_refl:
  !vars s. state_equiv vars s s
Proof
  rw[state_equiv_def, execution_equiv_def]
QED

Theorem state_equiv_sym:
  !vars s1 s2. state_equiv vars s1 s2 ==> state_equiv vars s2 s1
Proof
  rw[state_equiv_def, execution_equiv_def]
QED

Theorem state_equiv_trans:
  !vars s1 s2 s3.
    state_equiv vars s1 s2 /\ state_equiv vars s2 s3 ==>
    state_equiv vars s1 s3
Proof
  rw[state_equiv_def, execution_equiv_def]
QED

Theorem state_equiv_subset:
  !vars1 vars2 s1 s2.
    state_equiv vars1 s1 s2 /\ vars1 SUBSET vars2 ==>
    state_equiv vars2 s1 s2
Proof
  rw[state_equiv_def, execution_equiv_def, SUBSET_DEF] >> metis_tac[]
QED

(* ==========================================================================
   execution_equiv: Relation Properties
   ========================================================================== *)

Theorem execution_equiv_refl:
  !vars s. execution_equiv vars s s
Proof
  rw[execution_equiv_def]
QED

Theorem execution_equiv_trans:
  !vars s1 s2 s3.
    execution_equiv vars s1 s2 /\ execution_equiv vars s2 s3 ==>
    execution_equiv vars s1 s3
Proof
  rw[execution_equiv_def]
QED

Theorem execution_equiv_subset:
  !vars1 vars2 s1 s2.
    execution_equiv vars1 s1 s2 /\ vars1 SUBSET vars2 ==>
    execution_equiv vars2 s1 s2
Proof
  rw[execution_equiv_def, SUBSET_DEF] >> metis_tac[]
QED

(* ==========================================================================
   result_equiv: Properties
   ========================================================================== *)

Theorem result_equiv_subset:
  !vars1 vars2 r1 r2.
    result_equiv vars1 r1 r2 /\ vars1 SUBSET vars2 ==>
    result_equiv vars2 r1 r2
Proof
  rpt gen_tac >> Cases_on `r1` >> Cases_on `r2` >>
  rw[result_equiv_def] >>
  TRY (irule state_equiv_subset >> metis_tac[]) >>
  TRY (irule execution_equiv_subset >> metis_tac[])
QED

(* result_equiv simp rules for automatic rewriting *)
Theorem result_equiv_ok[local,simp]:
  result_equiv vars (OK s1) (OK s2) = state_equiv vars s1 s2
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_halt[local,simp]:
  result_equiv vars (Halt s1) (Halt s2) = execution_equiv vars s1 s2
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_abort[local,simp]:
  result_equiv vars (Abort a1 s1) (Abort a2 s2) =
    ((a1 = a2) /\ execution_equiv vars s1 s2)
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_error[local,simp]:
  result_equiv vars (Error e1) (Error e2) = T
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_intret[local,simp]:
  result_equiv vars (IntRet v1 s1) (IntRet v2 s2) =
    (execution_equiv vars s1 s2 /\ (v1 = v2))
Proof
  rw[result_equiv_def]
QED

Theorem result_equiv_mismatch[local,simp]:
  result_equiv vars (OK s) (Halt s') = F /\
  result_equiv vars (OK s) (Abort a s') = F /\
  result_equiv vars (OK s) (IntRet v s') = F /\
  result_equiv vars (OK s) (Error e) = F /\
  result_equiv vars (Halt s) (OK s') = F /\
  result_equiv vars (Halt s) (Abort a s') = F /\
  result_equiv vars (Halt s) (IntRet v s') = F /\
  result_equiv vars (Halt s) (Error e) = F /\
  result_equiv vars (Abort a s) (OK s') = F /\
  result_equiv vars (Abort a s) (Halt s') = F /\
  result_equiv vars (Abort a s) (IntRet v s') = F /\
  result_equiv vars (Abort a s) (Error e) = F /\
  result_equiv vars (IntRet v s) (OK s') = F /\
  result_equiv vars (IntRet v s) (Halt s') = F /\
  result_equiv vars (IntRet v s) (Abort a s') = F /\
  result_equiv vars (IntRet v s) (Error e) = F /\
  result_equiv vars (Error e) (OK s) = F /\
  result_equiv vars (Error e) (Halt s) = F /\
  result_equiv vars (Error e) (Abort a s) = F /\
  result_equiv vars (Error e) (IntRet v s) = F
Proof
  rw[result_equiv_def]
QED

(* result_equiv is transitive *)
Theorem result_equiv_trans:
  !vars r1 r2 r3.
    result_equiv vars r1 r2 /\ result_equiv vars r2 r3 ==>
    result_equiv vars r1 r3
Proof
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  gvs[result_equiv_def] >>
  metis_tac[state_equiv_trans, execution_equiv_trans]
QED

(* Note: result_equiv_is_lift_result relies on matching patterns
   between result_equiv and lift_result. Both now include IntRet. *)

(* result_equiv is the canonical instantiation of lift_result *)
Theorem result_equiv_is_lift_result:
  !vars. result_equiv vars = lift_result (state_equiv vars) (execution_equiv vars)
Proof
  rw[FUN_EQ_THM] >> Cases_on `x` >> Cases_on `x'` >>
  simp[result_equiv_def, lift_result_def]
QED

(* ==========================================================================
   Operand Evaluation
   ========================================================================== *)

Theorem eval_operand_equiv:
  !vars op s1 s2.
    state_equiv vars s1 s2 /\
    (!x. op = Var x ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  Cases_on `op` >>
  rw[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* ==========================================================================
   Mutations Preserve state_equiv
   ========================================================================== *)

Theorem update_var_preserves:
  !vars x v s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (update_var x v s1) (update_var x v s2)
Proof
  rw[state_equiv_def, execution_equiv_def,
     update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem mstore_preserves:
  !vars offset v s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (mstore offset v s1) (mstore offset v s2)
Proof
  rw[state_equiv_def, execution_equiv_def, mstore_def, lookup_var_def]
QED

Theorem sstore_preserves:
  !vars key v s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (sstore key v s1) (sstore key v s2)
Proof
  rw[state_equiv_def, execution_equiv_def, sstore_def, lookup_var_def]
QED

Theorem tstore_preserves:
  !vars key v s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (tstore key v s1) (tstore key v s2)
Proof
  rw[state_equiv_def, execution_equiv_def, tstore_def, lookup_var_def]
QED

Theorem write_memory_with_expansion_preserves:
  !vars offset bytes s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars
      (write_memory_with_expansion offset bytes s1)
      (write_memory_with_expansion offset bytes s2)
Proof
  rw[state_equiv_def, execution_equiv_def,
     write_memory_with_expansion_def, lookup_var_def]
QED

Theorem jump_to_preserves:
  !vars lbl s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (jump_to lbl s1) (jump_to lbl s2)
Proof
  rw[state_equiv_def, execution_equiv_def, jump_to_def, lookup_var_def]
QED

Theorem halt_state_preserves:
  !vars s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (halt_state s1) (halt_state s2)
Proof
  rw[state_equiv_def, execution_equiv_def, halt_state_def, lookup_var_def]
QED

Theorem revert_state_preserves:
  !vars s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (revert_state s1) (revert_state s2)
Proof
  rw[state_equiv_def, execution_equiv_def, revert_state_def, lookup_var_def]
QED

(* ==========================================================================
   Reads Give Same Result
   ========================================================================== *)

Theorem mload_same:
  !vars addr s1 s2.
    state_equiv vars s1 s2 ==>
    mload addr s1 = mload addr s2
Proof
  rw[mload_def, state_equiv_def, execution_equiv_def]
QED

Theorem sload_same:
  !vars key s1 s2.
    state_equiv vars s1 s2 ==>
    sload key s1 = sload key s2
Proof
  rw[sload_def, state_equiv_def, execution_equiv_def]
QED

Theorem tload_same:
  !vars key s1 s2.
    state_equiv vars s1 s2 ==>
    tload key s1 = tload key s2
Proof
  rw[tload_def, state_equiv_def, execution_equiv_def]
QED

(* ==========================================================================
   execution_equiv variants (currently unused)
   Kept for future passes that need execution_equiv-level reasoning.
   Currently all consumers unfold execution_equiv_def directly.
   TODO: Un-local these when a downstream consumer needs them.
   ========================================================================== *)

Theorem update_var_execution_preserves[local]:
  !vars x v s1 s2.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars (update_var x v s1) (update_var x v s2)
Proof
  rw[execution_equiv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem mstore_execution_preserves[local]:
  !vars addr val s1 s2.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars (mstore addr val s1) (mstore addr val s2)
Proof
  rw[execution_equiv_def, mstore_def, lookup_var_def]
QED

Theorem sstore_execution_preserves[local]:
  !vars key val s1 s2.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars (sstore key val s1) (sstore key val s2)
Proof
  rw[execution_equiv_def, sstore_def, lookup_var_def]
QED

Theorem tstore_execution_preserves[local]:
  !vars key val s1 s2.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars (tstore key val s1) (tstore key val s2)
Proof
  rw[execution_equiv_def, tstore_def, lookup_var_def]
QED

Theorem halt_state_execution_preserves[local]:
  !vars s1 s2.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars (halt_state s1) (halt_state s2)
Proof
  rw[execution_equiv_def, halt_state_def, lookup_var_def]
QED

Theorem revert_state_execution_preserves[local]:
  !vars s1 s2.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars (revert_state s1) (revert_state s2)
Proof
  rw[execution_equiv_def, revert_state_def, lookup_var_def]
QED

Theorem write_memory_with_expansion_execution_preserves[local]:
  !vars offset bytes s1 s2.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars
      (write_memory_with_expansion offset bytes s1)
      (write_memory_with_expansion offset bytes s2)
Proof
  rw[execution_equiv_def, write_memory_with_expansion_def, lookup_var_def]
QED

Theorem mload_execution_same[local]:
  !vars addr s1 s2.
    execution_equiv vars s1 s2 ==>
    mload addr s1 = mload addr s2
Proof
  rw[execution_equiv_def, mload_def]
QED

Theorem sload_execution_same[local]:
  !vars key s1 s2.
    execution_equiv vars s1 s2 ==>
    sload key s1 = sload key s2
Proof
  rw[execution_equiv_def, sload_def]
QED

Theorem tload_execution_same[local]:
  !vars key s1 s2.
    execution_equiv vars s1 s2 ==>
    tload key s1 = tload key s2
Proof
  rw[execution_equiv_def, tload_def]
QED

Theorem eval_operand_execution_equiv[local]:
  !vars op s1 s2.
    execution_equiv vars s1 s2 /\
    (!x. op = Var x ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  Cases_on `op` >>
  rw[eval_operand_def, execution_equiv_def, lookup_var_def]
QED


