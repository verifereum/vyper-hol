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

(* ==========================================================================
   Fresh Variable Generation
   ========================================================================== *)

(*
 * Fresh variable name for ISZERO output.
 * Simple naming scheme: "rta_tmp_<id>"
 *
 * Correctness relies on precondition that these names aren't used in the
 * original function. This is verified at the compiler level.
 *)
Definition fresh_iszero_var_def:
  fresh_iszero_var (id:num) = STRCAT "rta_tmp_" (toString id)
End

(* ==========================================================================
   Instruction Builders
   ========================================================================== *)

(* ISZERO instruction: %out = iszero %cond *)
Definition mk_iszero_inst_def:
  mk_iszero_inst id cond_op out = <|
    inst_id := id;
    inst_opcode := ISZERO;
    inst_operands := [cond_op];
    inst_outputs := [out]
  |>
End

(* ASSERT instruction: assert %cond *)
Definition mk_assert_inst_def:
  mk_assert_inst id cond_op = <|
    inst_id := id;
    inst_opcode := ASSERT;
    inst_operands := [cond_op];
    inst_outputs := []
  |>
End

(* JMP instruction: jmp @label *)
Definition mk_jmp_inst_def:
  mk_jmp_inst id label = <|
    inst_id := id;
    inst_opcode := JMP;
    inst_operands := [Label label];
    inst_outputs := []
  |>
End

(* ==========================================================================
   Revert Block Detection
   ========================================================================== *)

(* Check if a label points to a simple revert block in the function *)
Definition is_revert_label_def:
  is_revert_label fn lbl =
    case lookup_block lbl fn.fn_blocks of
      NONE => F
    | SOME bb => is_simple_revert_block bb
End

(* ==========================================================================
   Pattern Transformers
   ========================================================================== *)

(*
 * Pattern 1: jnz %cond @revert @else => iszero; assert; jmp @else
 *
 * WHY THIS IS CORRECT:
 *   - If cond != 0w: Original jumps to revert, transformed asserts 0w (reverts)
 *   - If cond = 0w: Original jumps to else, transformed asserts 1w (passes), jumps to else
 *   - Proven in pattern1_transform_correct
 *)
Definition transform_pattern1_def:
  transform_pattern1 jnz_inst cond_op else_label =
    let id = jnz_inst.inst_id in
    let tmp = fresh_iszero_var id in
    [mk_iszero_inst id cond_op tmp;
     mk_assert_inst (id + 1) (Var tmp);
     mk_jmp_inst (id + 2) else_label]
End

(*
 * Pattern 2: jnz %cond @then @revert => assert %cond; jmp @then
 *
 * WHY THIS IS CORRECT:
 *   - If cond != 0w: Original jumps to then, transformed asserts (passes), jumps to then
 *   - If cond = 0w: Original jumps to revert, transformed asserts 0w (reverts)
 *   - Proven in pattern2_transform_correct
 *)
Definition transform_pattern2_def:
  transform_pattern2 jnz_inst cond_op then_label =
    let id = jnz_inst.inst_id in
    [mk_assert_inst id cond_op;
     mk_jmp_inst (id + 1) then_label]
End

(* ==========================================================================
   Instruction Transformation
   ========================================================================== *)

(* Try to transform a JNZ instruction. Returns SOME new_insts if applicable. *)
Definition transform_jnz_def:
  transform_jnz fn inst =
    if inst.inst_opcode <> JNZ then NONE
    else case inst.inst_operands of
      [cond_op; Label if_nonzero; Label if_zero] =>
        (* Pattern 1: revert on nonzero *)
        if is_revert_label fn if_nonzero then
          SOME (transform_pattern1 inst cond_op if_zero)
        (* Pattern 2: revert on zero *)
        else if is_revert_label fn if_zero then
          SOME (transform_pattern2 inst cond_op if_nonzero)
        else NONE
    | _ => NONE
End

(* ==========================================================================
   Block Transformation
   ========================================================================== *)

(* Transform all instructions in a block *)
Definition transform_block_insts_def:
  transform_block_insts fn [] = [] /\
  transform_block_insts fn (inst::rest) =
    case transform_jnz fn inst of
      SOME new_insts => new_insts ++ transform_block_insts fn rest
    | NONE => inst :: transform_block_insts fn rest
End

(* Transform a single block *)
Definition transform_block_def:
  transform_block fn bb =
    bb with bb_instructions := transform_block_insts fn bb.bb_instructions
End

(* ==========================================================================
   Function and Context Transformation
   ========================================================================== *)

(* Transform all blocks in a function *)
Definition transform_function_def:
  transform_function fn =
    fn with fn_blocks := MAP (transform_block fn) fn.fn_blocks
End

(* Transform all functions in a context *)
Definition transform_context_def:
  transform_context ctx =
    ctx with ctx_functions := MAP transform_function ctx.ctx_functions
End

(* ==========================================================================
   Fresh Variables Tracking
   ========================================================================== *)

(*
 * All fresh variables that may be introduced by transforming a block.
 * Only pattern 1 introduces fresh vars (for ISZERO output).
 *)
Definition fresh_vars_in_block_def:
  fresh_vars_in_block fn bb =
    { fresh_iszero_var inst.inst_id |
      inst | MEM inst bb.bb_instructions /\
             transform_jnz fn inst <> NONE /\
             ?cond_op if_nonzero if_zero.
               inst.inst_operands = [cond_op; Label if_nonzero; Label if_zero] /\
               is_revert_label fn if_nonzero }
End

(*
 * All fresh variables in a function.
 *)
Definition fresh_vars_in_function_def:
  fresh_vars_in_function fn =
    BIGUNION { fresh_vars_in_block fn bb | bb | MEM bb fn.fn_blocks }
End

(*
 * All fresh variables in a context.
 *)
Definition fresh_vars_in_context_def:
  fresh_vars_in_context ctx =
    BIGUNION { fresh_vars_in_function fn | fn | MEM fn ctx.ctx_functions }
End

(* ==========================================================================
   Static Analysis: Fresh Vars Not In Original Code
   ========================================================================== *)

(*
 * Static property: No instruction in the block uses fresh vars as operands.
 * This is true for original code because fresh vars are only introduced by transform.
 *)
Definition fresh_vars_not_in_block_def:
  fresh_vars_not_in_block fn bb <=>
    !inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
      !id. x <> fresh_iszero_var id
End

(*
 * Static property for entire function.
 *)
Definition fresh_vars_not_in_function_def:
  fresh_vars_not_in_function fn <=>
    !bb. MEM bb fn.fn_blocks ==> fresh_vars_not_in_block fn bb
End

(*
 * Static property for entire context.
 *)
Definition fresh_vars_not_in_context_def:
  fresh_vars_not_in_context ctx <=>
    !fn. MEM fn ctx.ctx_functions ==> fresh_vars_not_in_function fn
End

val _ = export_theory();
