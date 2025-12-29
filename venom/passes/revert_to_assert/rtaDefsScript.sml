(*
 * Revert-to-Assert Definitions
 *
 * This theory defines the predicates and types for the revert-to-assert pass
 * correctness proof. The pass transforms conditional jumps to revert blocks
 * into assert instructions.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - is_simple_revert_block    : Predicate for blocks that just revert(0,0)
 *   - is_jnz_to_revert_pattern1 : JNZ where true branch reverts
 *   - is_jnz_to_revert_pattern2 : JNZ where false branch reverts
 *   - state_equiv_except        : State equivalence ignoring a set of variables
 *
 * TOP-LEVEL THEOREMS:
 *   - state_equiv_except_refl/sym/trans : Equivalence relation properties
 *   - state_equiv_implies_except        : Full equiv implies except-equiv
 *
 * ============================================================================
 * TRANSFORMATION PATTERNS
 * ============================================================================
 *
 * Pattern 1 (revert on true):
 *   BEFORE:
 *     jnz %cond, @revert_block, @else_block
 *     revert_block: revert 0, 0
 *   AFTER:
 *     %tmp = iszero %cond
 *     assert %tmp
 *     jmp @else_block
 *
 * Pattern 2 (revert on false):
 *   BEFORE:
 *     jnz %cond, @then_block, @revert_block
 *     revert_block: revert 0, 0
 *   AFTER:
 *     assert %cond
 *     jmp @then_block
 *
 * WHY THIS IS CORRECT:
 *   - Pattern 1: If cond is nonzero, we would jump to revert. Instead, we
 *     compute iszero(cond)=0, then assert(0) reverts. Same behavior.
 *     If cond is zero, we would jump to else. iszero(0)=1, assert(1) passes,
 *     we jump to else. Same behavior.
 *   - Pattern 2: If cond is nonzero, we would jump to then. assert(cond!=0)
 *     passes, we jump to then. Same behavior. If cond is zero, we would
 *     jump to revert. assert(0) reverts. Same behavior.
 *
 * ============================================================================
 *)

Theory rtaDefs
Ancestors
  stateEquiv venomSem venomInst venomState finite_map pred_set
Libs
  finite_mapTheory venomStateTheory

(* ==========================================================================
   Simple Revert Block Detection
   ========================================================================== *)

(*
 * PURPOSE: Detect blocks that consist solely of a revert(0, 0) instruction.
 * These blocks are candidates for elimination by the revert-to-assert pass.
 *
 * WHY THIS FORM: The Vyper compiler generates these blocks for failed
 * assertions and conditions. The (0, 0) arguments mean no error data is
 * returned (offset=0, length=0).
 *)
Definition is_simple_revert_block_def:
  is_simple_revert_block bb <=>
    LENGTH bb.bb_instructions = 1 /\
    (HD bb.bb_instructions).inst_opcode = REVERT /\
    (HD bb.bb_instructions).inst_operands = [Lit 0w; Lit 0w]
End

(* ==========================================================================
   JNZ Pattern Detection
   ========================================================================== *)

(*
 * PURPOSE: Detect Pattern 1 - JNZ where the TRUE (nonzero) branch goes to
 * a revert block.
 *
 * JNZ semantics: jnz %cond, @if_nonzero, @if_zero
 *   - If cond != 0: jump to if_nonzero
 *   - If cond == 0: jump to if_zero
 *
 * In Pattern 1, if_nonzero = revert_label, meaning "revert when true"
 *)
Definition is_jnz_to_revert_pattern1_def:
  is_jnz_to_revert_pattern1 inst revert_label <=>
    inst.inst_opcode = JNZ /\
    ?cond else_label.
      inst.inst_operands = [cond; Label revert_label; Label else_label]
End

(*
 * PURPOSE: Detect Pattern 2 - JNZ where the FALSE (zero) branch goes to
 * a revert block.
 *
 * In Pattern 2, if_zero = revert_label, meaning "revert when false"
 *)
Definition is_jnz_to_revert_pattern2_def:
  is_jnz_to_revert_pattern2 inst revert_label <=>
    inst.inst_opcode = JNZ /\
    ?cond then_label.
      inst.inst_operands = [cond; Label then_label; Label revert_label]
End

(* ==========================================================================
   Extract Labels from JNZ Patterns
   ========================================================================== *)

(*
 * PURPOSE: Extract the continuation label (where execution continues if
 * the assert passes) from a Pattern 1 JNZ.
 *)
Definition get_pattern1_else_label_def:
  get_pattern1_else_label inst =
    case inst.inst_operands of
      [cond; Label revert_lbl; Label else_lbl] => SOME else_lbl
    | _ => NONE
End

(*
 * PURPOSE: Extract the continuation label from a Pattern 2 JNZ.
 *)
Definition get_pattern2_then_label_def:
  get_pattern2_then_label inst =
    case inst.inst_operands of
      [cond; Label then_lbl; Label revert_lbl] => SOME then_lbl
    | _ => NONE
End

(*
 * PURPOSE: Extract the condition operand from a JNZ instruction.
 *)
Definition get_jnz_condition_def:
  get_jnz_condition inst =
    case inst.inst_operands of
      [cond; _; _] => SOME cond
    | _ => NONE
End

(* ==========================================================================
   State Equivalence Ignoring a Set of Variables
   ========================================================================== *)

(*
 * PURPOSE: A relaxed notion of state equivalence that ignores a specified
 * set of variables. This is needed because the transformation may introduce
 * temporary variables (e.g., %tmp for the iszero result in Pattern 1).
 *
 * WHY THIS IS NEEDED: After transformation, the state will have an extra
 * variable %tmp that wasn't in the original execution. To prove equivalence,
 * we need to say "the states are equivalent except for %tmp".
 *)
Definition state_equiv_except_def:
  state_equiv_except vars s1 s2 <=>
    (!v. v NOTIN vars ==> lookup_var v s1 = lookup_var v s2) /\
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
   Equivalence Relation Properties for state_equiv_except
   ========================================================================== *)

(* TOP-LEVEL: Reflexivity *)
Theorem state_equiv_except_refl:
  !vars s. state_equiv_except vars s s
Proof
  rw[state_equiv_except_def]
QED

(* TOP-LEVEL: Symmetry *)
Theorem state_equiv_except_sym:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars s2 s1
Proof
  rw[state_equiv_except_def]
QED

(* TOP-LEVEL: Transitivity *)
Theorem state_equiv_except_trans:
  !vars s1 s2 s3.
    state_equiv_except vars s1 s2 /\
    state_equiv_except vars s2 s3 ==>
    state_equiv_except vars s1 s3
Proof
  rw[state_equiv_except_def]
QED

(* TOP-LEVEL: Full state_equiv implies state_equiv_except for any vars *)
Theorem state_equiv_implies_except:
  !vars s1 s2.
    state_equiv s1 s2 ==>
    state_equiv_except vars s1 s2
Proof
  rw[state_equiv_def, var_equiv_def, state_equiv_except_def]
QED

(* Helper: Empty variable set gives full equivalence (for non-var fields) *)
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
  rw[state_equiv_except_def]
QED

(* ==========================================================================
   Result Equivalence with Variable Exceptions
   ========================================================================== *)

(*
 * PURPOSE: Extend state_equiv_except to exec_result.
 * This mirrors result_equiv but uses state_equiv_except.
 *)
Definition result_equiv_except_def:
  result_equiv_except vars (OK s1) (OK s2) = state_equiv_except vars s1 s2 /\
  result_equiv_except vars (Halt s1) (Halt s2) = state_equiv_except vars s1 s2 /\
  result_equiv_except vars (Revert s1) (Revert s2) = state_equiv_except vars s1 s2 /\
  result_equiv_except vars (Error e1) (Error e2) = T /\
  result_equiv_except vars _ _ = F
End

(* TOP-LEVEL: Reflexivity for result_equiv_except *)
Theorem result_equiv_except_refl:
  !vars r. result_equiv_except vars r r
Proof
  gen_tac >> Cases >> rw[result_equiv_except_def, state_equiv_except_refl]
QED

(* Helper simp theorems *)
Theorem result_equiv_except_ok[simp]:
  result_equiv_except vars (OK s1) (OK s2) = state_equiv_except vars s1 s2
Proof
  rw[result_equiv_except_def]
QED

Theorem result_equiv_except_halt[simp]:
  result_equiv_except vars (Halt s1) (Halt s2) = state_equiv_except vars s1 s2
Proof
  rw[result_equiv_except_def]
QED

Theorem result_equiv_except_revert[simp]:
  result_equiv_except vars (Revert s1) (Revert s2) = state_equiv_except vars s1 s2
Proof
  rw[result_equiv_except_def]
QED

Theorem result_equiv_except_error[simp]:
  result_equiv_except vars (Error e1) (Error e2) = T
Proof
  rw[result_equiv_except_def]
QED

(* Mismatch cases *)
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
   Update Preserves state_equiv_except
   ========================================================================== *)

(*
 * PURPOSE: If we update a variable in the exception set, equivalence is
 * preserved regardless of the value.
 *)
Theorem update_var_in_except_preserves:
  !vars x v1 v2 s1 s2.
    x IN vars /\
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (update_var x v1 s1) (update_var x v2 s2)
Proof
  rw[state_equiv_except_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `x = v` >> gvs[]
QED

(*
 * PURPOSE: If we update a variable NOT in the exception set with the SAME
 * value, equivalence is preserved.
 *)
Theorem update_var_same_preserves:
  !vars x v s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (update_var x v s1) (update_var x v s2)
Proof
  rw[state_equiv_except_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(*
 * PURPOSE: Updating a variable IN the exception set preserves equivalence
 * (one-sided update).
 *)
Theorem update_var_except_one_side:
  !vars x v s1 s2.
    x IN vars /\
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (update_var x v s1) s2
Proof
  rw[state_equiv_except_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `v' = x` >> gvs[]
QED

(* ==========================================================================
   Operand Evaluation under state_equiv_except
   ========================================================================== *)

(*
 * PURPOSE: If an operand doesn't reference any excepted variables, it
 * evaluates the same in equivalent states.
 *)
Theorem eval_operand_except:
  !vars op s1 s2.
    state_equiv_except vars s1 s2 /\
    (!x. op = Var x ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  Cases_on `op` >>
  rw[eval_operand_def, state_equiv_except_def, lookup_var_def]
QED

(* ==========================================================================
   Jump and Control Flow Preserve state_equiv_except
   ========================================================================== *)

Theorem jump_to_except_preserves:
  !vars lbl s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (jump_to lbl s1) (jump_to lbl s2)
Proof
  rw[state_equiv_except_def, jump_to_def, lookup_var_def]
QED

Theorem halt_state_except_preserves:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (halt_state s1) (halt_state s2)
Proof
  rw[state_equiv_except_def, halt_state_def, lookup_var_def]
QED

Theorem revert_state_except_preserves:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (revert_state s1) (revert_state s2)
Proof
  rw[state_equiv_except_def, revert_state_def, lookup_var_def]
QED

(* ==========================================================================
   Widening the Exception Set
   ========================================================================== *)

(*
 * PURPOSE: If states are equivalent except for vars1, and vars1 SUBSET vars2,
 * then they are also equivalent except for vars2.
 *)
Theorem state_equiv_except_subset:
  !vars1 vars2 s1 s2.
    state_equiv_except vars1 s1 s2 /\
    vars1 SUBSET vars2 ==>
    state_equiv_except vars2 s1 s2
Proof
  rw[state_equiv_except_def, SUBSET_DEF] >>
  metis_tac[]
QED

(*
 * PURPOSE: Monotonicity for result_equiv_except - widening the exception set.
 *)
Theorem result_equiv_except_subset:
  !vars1 vars2 r1 r2.
    result_equiv_except vars1 r1 r2 /\
    vars1 SUBSET vars2 ==>
    result_equiv_except vars2 r1 r2
Proof
  rpt gen_tac >> Cases_on `r1` >> Cases_on `r2` >>
  rw[result_equiv_except_def] >> irule state_equiv_except_subset >>
  metis_tac[]
QED

(* ==========================================================================
   Memory/Storage Operations Preserve state_equiv_except
   ========================================================================== *)

(*
 * PURPOSE: mstore preserves state_equiv_except because it only modifies
 * memory, and memory is already equal in equiv_except states.
 *)
Theorem mstore_except_preserves:
  !vars addr val s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (mstore addr val s1) (mstore addr val s2)
Proof
  rw[state_equiv_except_def, mstore_def, lookup_var_def]
QED

(*
 * PURPOSE: mload returns the same value from equiv_except states.
 *)
Theorem mload_except_same:
  !vars addr s1 s2.
    state_equiv_except vars s1 s2 ==>
    mload addr s1 = mload addr s2
Proof
  rw[state_equiv_except_def, mload_def]
QED

(*
 * PURPOSE: sstore preserves state_equiv_except.
 *)
Theorem sstore_except_preserves:
  !vars key val s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (sstore key val s1) (sstore key val s2)
Proof
  rw[state_equiv_except_def, sstore_def, lookup_var_def]
QED

(*
 * PURPOSE: sload returns the same value from equiv_except states.
 *)
Theorem sload_except_same:
  !vars key s1 s2.
    state_equiv_except vars s1 s2 ==>
    sload key s1 = sload key s2
Proof
  rw[state_equiv_except_def, sload_def]
QED

(*
 * PURPOSE: tstore preserves state_equiv_except.
 *)
Theorem tstore_except_preserves:
  !vars key val s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (tstore key val s1) (tstore key val s2)
Proof
  rw[state_equiv_except_def, tstore_def, lookup_var_def]
QED

(*
 * PURPOSE: tload returns the same value from equiv_except states.
 *)
Theorem tload_except_same:
  !vars key s1 s2.
    state_equiv_except vars s1 s2 ==>
    tload key s1 = tload key s2
Proof
  rw[state_equiv_except_def, tload_def]
QED

(*
 * PURPOSE: write_memory_with_expansion preserves state_equiv_except.
 *)
Theorem write_memory_with_expansion_except_preserves:
  !vars offset bytes s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars
      (write_memory_with_expansion offset bytes s1)
      (write_memory_with_expansion offset bytes s2)
Proof
  rw[state_equiv_except_def, write_memory_with_expansion_def, lookup_var_def]
QED

val _ = export_theory();

