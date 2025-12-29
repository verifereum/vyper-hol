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
 *
 * This theory imports state equivalence definitions from stateEquivTheory:
 *   - state_equiv_except        : State equivalence ignoring a set of variables
 *   - execution_equiv_except    : State equivalence ignoring control flow
 *   - observable_equiv          : External effect equivalence
 *   - result_equiv_except       : Result equivalence for exec_result
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

val _ = export_theory();
