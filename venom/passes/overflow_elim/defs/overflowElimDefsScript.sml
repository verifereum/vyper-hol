(*
 * Overflow Check Elimination — Definitions
 *
 * Ports vyper/venom/passes/overflow_elimination.py to HOL4.
 * Upstream commit: 41b8507d6
 *
 * Eliminates redundant arithmetic overflow/underflow check assertions
 * when variable range analysis proves they always pass.
 *
 * Patterns eliminated:
 *   1. Add overflow:  assert (iszero (lt (add x y) x))
 *      Eliminated when x,y non-negative and max(x)+max(y) <= 2^256-1
 *   2. Sub underflow: assert (iszero (gt (sub x y) x))
 *      Eliminated when x,y non-negative and min(x) >= max(y)
 *
 * The pass follows DFG chains from ASSERT instructions to find these
 * specific patterns, then uses range analysis to check the condition.
 *
 * Python error_msg filtering (safeadd/safesub) is not modeled since
 * error_msg is not in the HOL4 instruction record. The structural
 * pattern match is already specific enough.
 *
 * TOP-LEVEL:
 *   overflow_elim_function   — function-level transform
 *
 * Helper:
 *   range_nonneg             — range is non-empty and non-negative
 *   try_elim_add_overflow    — check add overflow pattern
 *   try_elim_sub_underflow   — check sub underflow pattern
 *   try_elim_overflow_check  — check assert for eliminable pattern
 *   overflow_elim_inst       — per-instruction transform
 *)

Theory overflowElimDefs
Ancestors
  rangeAnalysisDefs valueRangeDefs rangeEvalDefs
  dfgDefs passSharedDefs

(* ===== Range predicates ===== *)

(* Matches Python _range_is_non_negative:
     not is_top and not is_empty and lo >= 0
   VR_Range lo hi with lo > hi is treated as empty (returns F). *)
Definition range_nonneg_def:
  range_nonneg VR_Top = F /\
  range_nonneg VR_Bottom = F /\
  range_nonneg (VR_Range lo hi) = (0 <= lo /\ lo <= hi)
End

(* ===== DFG producer lookup ===== *)

(* Get the producing instruction for an operand via DFG.
   Matches Python _get_producer: only variables have producers. *)
Definition get_producer_def:
  get_producer dfg (Var v) = dfg_get_def dfg v /\
  get_producer dfg (Lit _) = NONE /\
  get_producer dfg (Label _) = NONE
End

(* ===== Add overflow check ===== *)

(* Check if a LT instruction is part of an add-overflow pattern
   and the ranges prove it safe.

   Pattern: lt (add x y) x — in HOL4 EVM order, lt_inst has
   operands [res; x] meaning res < x.

   We look up the DFG producer of res to find an ADD with
   operands [a; b]. One of a,b must match x; the other is y.

   Condition: x,y non-negative and hi(x) + hi(y) <= 2^256-1. *)
Definition try_elim_add_overflow_def:
  try_elim_add_overflow dfg ra lbl idx (lt_inst : instruction) =
    case lt_inst.inst_operands of
      [res_op; x_op] =>
        (case get_producer dfg res_op of
           SOME add_inst =>
             if add_inst.inst_opcode <> ADD then F
             else (case add_inst.inst_operands of
               [add_op0; add_op1] =>
                 let y_op =
                   if add_op0 = x_op then SOME add_op1
                   else if add_op1 = x_op then SOME add_op0
                   else NONE
                 in
                 (case y_op of
                    NONE => F
                  | SOME y =>
                      let x_range = range_get_range ra lbl idx x_op in
                      let y_range = range_get_range ra lbl idx y in
                      range_nonneg x_range /\ range_nonneg y_range /\
                      vr_hi x_range + vr_hi y_range <= UINT256_MAX_int)
             | _ => F)
         | NONE => F)
    | _ => F
End

(* ===== Sub underflow check ===== *)

(* Check if a GT instruction is part of a sub-underflow pattern
   and the ranges prove it safe.

   Pattern: gt (sub x y) x — in HOL4 EVM order, gt_inst has
   operands [res; x] meaning res > x.

   We look up the DFG producer of res to find a SUB with
   operands [sub_x; sub_y]. sub_x must match x.

   Condition: x,y non-negative and lo(x) >= hi(y). *)
Definition try_elim_sub_underflow_def:
  try_elim_sub_underflow dfg ra lbl idx (gt_inst : instruction) =
    case gt_inst.inst_operands of
      [res_op; x_op] =>
        (case get_producer dfg res_op of
           SOME sub_inst =>
             if sub_inst.inst_opcode <> SUB then F
             else (case sub_inst.inst_operands of
               [sub_x; sub_y] =>
                 if sub_x <> x_op then F
                 else
                   let x_range = range_get_range ra lbl idx x_op in
                   let y_range = range_get_range ra lbl idx sub_y in
                   range_nonneg x_range /\ range_nonneg y_range /\
                   vr_lo x_range >= vr_hi y_range
             | _ => F)
         | NONE => F)
    | _ => F
End

(* ===== Top-level pattern check ===== *)

(* Check if an ASSERT instruction can be eliminated as an overflow check.

   Pattern: assert (iszero (lt/gt ...))
   1. Assert operand → iszero instruction (via DFG)
   2. Iszero operand → lt or gt instruction (via DFG)
   3. lt → try_elim_add_overflow
      gt → try_elim_sub_underflow *)
Definition try_elim_overflow_check_def:
  try_elim_overflow_check dfg ra lbl idx (assert_inst : instruction) =
    case assert_inst.inst_operands of
      [assert_op] =>
        (case get_producer dfg assert_op of
           SOME iszero_inst =>
             if iszero_inst.inst_opcode <> ISZERO then F
             else (case iszero_inst.inst_operands of
               [cmp_op] =>
                 (case get_producer dfg cmp_op of
                    SOME cmp_inst =>
                      if cmp_inst.inst_opcode = LT then
                        try_elim_add_overflow dfg ra lbl idx cmp_inst
                      else if cmp_inst.inst_opcode = GT then
                        try_elim_sub_underflow dfg ra lbl idx cmp_inst
                      else F
                  | NONE => F)
             | _ => F)
         | NONE => F)
    | _ => F
End

(* ===== Per-instruction transform ===== *)

(* Transform a single instruction given DFG and range analysis.
   Only ASSERT instructions are candidates. *)
Definition overflow_elim_inst_def:
  overflow_elim_inst dfg ra lbl idx inst =
    if inst.inst_opcode <> ASSERT then inst
    else if try_elim_overflow_check dfg ra lbl idx inst
    then mk_nop_inst inst
    else inst
End

(* ===== Block-level transform ===== *)

(* Transform instructions in a block, threading the index.
   idx starts at 0 for the first instruction. *)
Definition overflow_elim_block_insts_def:
  overflow_elim_block_insts dfg ra lbl idx [] = [] /\
  overflow_elim_block_insts dfg ra lbl idx (inst::rest) =
    overflow_elim_inst dfg ra lbl idx inst ::
    overflow_elim_block_insts dfg ra lbl (idx + 1) rest
End

Definition overflow_elim_block_def:
  overflow_elim_block dfg ra lbl bb =
    bb with bb_instructions :=
      overflow_elim_block_insts dfg ra lbl 0 bb.bb_instructions
End

(* ===== Function-level transform ===== *)

Definition overflow_elim_function_def:
  overflow_elim_function fn =
    let dfg = dfg_build_function fn in
    let ra = range_analyze fn in
    clear_nops_function
      (fn with fn_blocks :=
        MAP (\bb. overflow_elim_block dfg ra bb.bb_label bb) fn.fn_blocks)
End
