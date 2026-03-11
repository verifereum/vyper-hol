(*
 * Lower DLOAD Pass — Definitions
 *
 * Ports vyper/venom/passes/lower_dload.py to HOL4.
 *
 * Lowers dload and dloadbytes instructions to their EVM equivalents:
 *   dload ptr        → alloca 32; add ptr code_end; codecopy dst add_out 32; mload dst
 *   dloadbytes dst src size → add src code_end; codecopy dst code_ptr size
 *
 * No analysis needed — pure per-instruction expansion (1:N).
 * Framework: function_map_transform with FLAT ∘ MAP.
 *
 * TOP-LEVEL:
 *   lower_dload_inst      — per-instruction expansion
 *   lower_dload_block     — block-level transform
 *   lower_dload_function  — function-level transform
 *   lower_dload_context   — context-level transform
 *
 * Helper:
 *   ld_alloca_var         — fresh variable name for alloca output
 *   ld_add_var            — fresh variable name for add output
 *
 * Source: vyper/venom/passes/lower_dload.py
 *)

Theory lowerDloadDefs
Ancestors
  passSimulationDefs venomExecSemantics venomInst

(* ===== Fresh Variable Names ===== *)

(* Fresh variable for alloca output.
   Naming scheme based on inst_id ensures uniqueness within a function. *)
Definition ld_alloca_var_def:
  ld_alloca_var (id:num) = STRCAT "ld_alloca_" (toString id)
End

(* Fresh variable for add output (ptr + code_end). *)
Definition ld_add_var_def:
  ld_add_var (id:num) = STRCAT "ld_add_" (toString id)
End

(* ===== Per-Instruction Expansion ===== *)

(*
 * Expand a single instruction.
 *
 * dload [ptr] with output [out]:
 *   1. alloca [Lit 32w]             → [alloca_var]    (allocate temp memory)
 *   2. add [ptr; Label "code_end"]  → [add_var]       (compute code offset)
 *   3. codecopy [Var alloca_var; Var add_var; Lit 32w] (copy code → memory)
 *   4. mload [Var alloca_var]       → [out]           (read from memory)
 *
 * dloadbytes [dst; src; size] (HOL4 semantic order: dst, src, size):
 *   1. add [src; Label "code_end"]  → [add_var]       (compute code offset)
 *   2. codecopy [dst; Var add_var; size]               (copy code → memory)
 *
 * All other instructions pass through unchanged.
 *
 * Note: ADD with Label operand requires label resolution (done by codegen).
 * The HOL4 eval_operand returns NONE for Labels. Correctness proof requires
 * a semantic extension or precondition about label resolution.
 *)
Definition lower_dload_inst_def:
  lower_dload_inst inst =
    if inst.inst_opcode = DLOAD then
      case (inst.inst_operands, inst.inst_outputs) of
        ([ptr_op], [out]) =>
          let id = inst.inst_id in
          let alloca_v = ld_alloca_var id in
          let add_v = ld_add_var id in
          [<| inst_id := id; inst_opcode := ALLOCA;
              inst_operands := [Lit 32w]; inst_outputs := [alloca_v] |>;
           <| inst_id := id + 1; inst_opcode := ADD;
              inst_operands := [ptr_op; Label "code_end"];
              inst_outputs := [add_v] |>;
           <| inst_id := id + 2; inst_opcode := CODECOPY;
              inst_operands := [Var alloca_v; Var add_v; Lit 32w];
              inst_outputs := [] |>;
           <| inst_id := id + 3; inst_opcode := MLOAD;
              inst_operands := [Var alloca_v]; inst_outputs := [out] |>]
      | _ => [inst]
    else if inst.inst_opcode = DLOADBYTES then
      case inst.inst_operands of
        [dst_op; src_op; size_op] =>
          let id = inst.inst_id in
          let add_v = ld_add_var id in
          [<| inst_id := id; inst_opcode := ADD;
              inst_operands := [src_op; Label "code_end"];
              inst_outputs := [add_v] |>;
           <| inst_id := id + 1; inst_opcode := CODECOPY;
              inst_operands := [dst_op; Var add_v; size_op];
              inst_outputs := [] |>]
      | _ => [inst]
    else [inst]
End

(* ===== Block and Function Transform ===== *)

(* Transform a block by expanding all dload/dloadbytes instructions. *)
Definition lower_dload_block_def:
  lower_dload_block bb =
    bb with bb_instructions :=
      FLAT (MAP lower_dload_inst bb.bb_instructions)
End

(* Transform a function by expanding all blocks. *)
Definition lower_dload_function_def:
  lower_dload_function fn =
    function_map_transform lower_dload_block fn
End

(* Transform all functions in a context. *)
Definition lower_dload_context_def:
  lower_dload_context ctx =
    ctx with ctx_functions := MAP lower_dload_function ctx.ctx_functions
End

(* ===== Fresh Variable Tracking ===== *)

(* Fresh variables introduced by expanding a single instruction. *)
Definition ld_fresh_vars_inst_def:
  ld_fresh_vars_inst inst =
    if inst.inst_opcode = DLOAD then
      {ld_alloca_var inst.inst_id; ld_add_var inst.inst_id}
    else if inst.inst_opcode = DLOADBYTES then
      {ld_add_var inst.inst_id}
    else {}
End

(* Fresh variables in a function. *)
Definition ld_fresh_vars_fn_def:
  ld_fresh_vars_fn fn =
    BIGUNION (set (MAP (\bb.
      BIGUNION (set (MAP ld_fresh_vars_inst bb.bb_instructions)))
      fn.fn_blocks))
End
