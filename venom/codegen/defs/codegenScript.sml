(*
 * Top-Level Venom → EVM Codegen
 *
 * Composes the three stages:
 *   1. Stack plan generation (Venom → stack_op list)
 *   2. Plan execution (stack_op list → asm_inst list)
 *   3. Assembly (asm_inst list → byte list)
 *
 * Data segment (selector tables, deploy code, CBOR metadata) is passed
 * separately and appended after the code assembly — it bypasses the
 * stack plan / plan executor stages.
 *
 * TOP-LEVEL:
 *   codegen — ir_context → data_section list → byte list option
 *)

Theory codegen
Ancestors
  symbolResolve

(* =========================================================================
   Full Pipeline
   ========================================================================= *)

Definition codegen_def:
  codegen (ctx : ir_context)
          (fn_eom_map : (string, num) fmap)
          (data_seg : data_section list) : byte list option =
    case generate_context_plan ctx fn_eom_map of
      NONE => NONE
    | SOME plan =>
        let code_asm = execute_plan plan in
        let data_asm = data_segment_asm data_seg in
        SOME (assemble (code_asm ++ data_asm))
End
