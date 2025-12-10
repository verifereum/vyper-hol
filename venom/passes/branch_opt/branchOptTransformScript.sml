(*
 * Branch Optimization Transformation Definitions
 *
 * This theory defines the branch optimization transformation.
 * The pass optimizes conditional branches (JNZ) by:
 * 1. Removing redundant ISZERO when followed by JNZ and swapping targets
 * 2. Potentially adding ISZERO and swapping targets based on heuristics
 *
 * The key insight: jnz (iszero x), A, B === jnz x, B, A
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - swap_jnz_operands     : Swap the two target labels of a JNZ
 *   - is_iszero_inst        : Check if instruction is ISZERO
 *   - transform_block       : Transform a basic block
 *   - transform_function    : Transform an entire function
 *
 * ============================================================================
 *)

Theory branchOptTransform
Ancestors
  list finite_map pred_set
  venomState venomInst venomSem

(* ==========================================================================
   Helper Definitions
   ========================================================================== *)

(* Check if an instruction is ISZERO *)
Definition is_iszero_inst_def:
  is_iszero_inst inst <=> inst.inst_opcode = ISZERO
End

(* Get the output variable of an instruction (if single output) *)
Definition get_single_output_def:
  get_single_output inst =
    case inst.inst_outputs of
      [out] => SOME out
    | _ => NONE
End

(* Swap the target labels of a JNZ instruction.
   JNZ format: [cond, label_if_nonzero, label_if_zero]
   After swap:  [cond, label_if_zero, label_if_nonzero] *)
Definition swap_jnz_operands_def:
  swap_jnz_operands inst =
    case inst.inst_operands of
      [cond; Label lbl1; Label lbl2] =>
        inst with inst_operands := [cond; Label lbl2; Label lbl1]
    | _ => inst
End

(* ==========================================================================
   Block Transformation

   The transformation looks for this pattern at the end of a block:
     %t = iszero %cond
     jnz %t, @label_a, @label_b

   And transforms it to:
     jnz %cond, @label_b, @label_a

   This removes the ISZERO and swaps the branch targets.
   ========================================================================== *)

(* Check if a JNZ uses a specific variable as its condition *)
Definition jnz_uses_var_def:
  jnz_uses_var inst var <=>
    inst.inst_opcode = JNZ /\
    case inst.inst_operands of
      [Var v; _; _] => v = var
    | _ => F
End

(* Replace the condition variable in a JNZ with a new operand *)
Definition replace_jnz_cond_def:
  replace_jnz_cond inst new_cond =
    case inst.inst_operands of
      [_; lbl1; lbl2] => inst with inst_operands := [new_cond; lbl1; lbl2]
    | _ => inst
End

(* Transform a block by looking for iszero+jnz pattern.
   If the second-to-last instruction is ISZERO producing %t,
   and the last instruction is JNZ using %t,
   then remove the ISZERO, use original operand, and swap targets. *)
Definition transform_block_def:
  transform_block bb =
    let instrs = bb.bb_instructions in
    let n = LENGTH instrs in
    if n < 2 then bb else
    let iszero_inst = EL (n - 2) instrs in
    let jnz_inst = EL (n - 1) instrs in
    case (is_iszero_inst iszero_inst,
          get_single_output iszero_inst,
          iszero_inst.inst_operands) of
      (T, SOME out_var, [orig_cond]) =>
        if jnz_uses_var jnz_inst out_var then
          (* Pattern matched: transform *)
          let new_jnz = swap_jnz_operands (replace_jnz_cond jnz_inst orig_cond) in
          (* Replace ISZERO with NOP and update JNZ *)
          let new_instrs = TAKE (n - 2) instrs ++
                           [iszero_inst with inst_opcode := NOP] ++
                           [new_jnz] in
          bb with bb_instructions := new_instrs
        else bb
    | _ => bb
End

(* Transform a function by transforming all blocks *)
Definition transform_function_def:
  transform_function fn =
    fn with fn_blocks := MAP transform_block fn.fn_blocks
End

(* Transform a context (all functions) *)
Definition transform_context_def:
  transform_context ctx =
    ctx with ctx_functions := MAP transform_function ctx.ctx_functions
End

(* ==========================================================================
   Basic Properties
   ========================================================================== *)

(* Transform preserves block label *)
Theorem transform_block_label:
  !bb. (transform_block bb).bb_label = bb.bb_label
Proof
  rw[transform_block_def] >>
  rpt (CASE_TAC >> simp[])
QED

(* Lookup commutes with transform *)
Theorem lookup_block_transform:
  !lbl blocks.
    lookup_block lbl (MAP transform_block blocks) =
    OPTION_MAP transform_block (lookup_block lbl blocks)
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> simp[lookup_block_def, transform_block_label]
QED

val _ = export_theory();
