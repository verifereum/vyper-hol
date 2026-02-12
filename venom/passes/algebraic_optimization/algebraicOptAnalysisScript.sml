(*
 * Algebraic Optimization (Venom IR) - Analysis Helpers
 *)

Theory algebraicOptAnalysis
Ancestors
  algebraicOptDefs dfgAnalysis

(* ==========================================================================
   Use Classification
   ========================================================================== *)

Definition is_truthy_use_opcode_def:
  is_truthy_use_opcode ISZERO = T /\
  is_truthy_use_opcode JNZ = T /\
  is_truthy_use_opcode ASSERT = T /\
  is_truthy_use_opcode ASSERT_UNREACHABLE = T /\
  is_truthy_use_opcode _ = F
End

Definition is_prefer_iszero_opcode_def:
  is_prefer_iszero_opcode ISZERO = T /\
  is_prefer_iszero_opcode ASSERT = T /\
  is_prefer_iszero_opcode _ = F
End

Definition all_uses_truthy_ops_def:
  all_uses_truthy_ops uses =
    case uses of
      [] => T
    | inst::rest =>
        is_truthy_use_opcode inst.inst_opcode /\ all_uses_truthy_ops rest
End

Definition all_uses_prefer_iszero_ops_def:
  all_uses_prefer_iszero_ops uses =
    case uses of
      [] => T
    | inst::rest =>
        is_prefer_iszero_opcode inst.inst_opcode /\
        all_uses_prefer_iszero_ops rest
End

(* ==========================================================================
   Comparator Hinting
   ========================================================================== *)

Definition cmp_flip_hint_for_uses_dfg_def:
  cmp_flip_hint_for_uses_dfg dfg inst uses =
    if ~is_comparator inst.inst_opcode then F
    else
      case inst.inst_operands of
        [op1; op2] =>
          if ~(is_lit op1 \/ is_lit op2) then F
          else
            (case uses of
               [after] =>
                 if is_prefer_iszero_opcode after.inst_opcode then
                   if after.inst_opcode = ISZERO then
                     (case inst_output after of
                        NONE => F
                      | SOME v2 =>
                          (case dfg_get_uses dfg v2 of
                             [use2] => if use2.inst_opcode = ASSERT then F else T
                           | _ => F))
                   else T
                 else F
             | _ => F)
      | _ => F
End

(* ==========================================================================
   Iszero-chain Analysis
   ========================================================================== *)

Definition iszero_chain_aux_dfg_def:
  iszero_chain_aux_dfg dfg 0 op acc = acc /\
  iszero_chain_aux_dfg dfg (SUC n) op acc =
    case op of
      Var v =>
        (case dfg_get_def dfg v of
           NONE => acc
         | SOME inst =>
             if inst.inst_opcode = ISZERO then
               (case inst.inst_operands of
                  [op'] => iszero_chain_aux_dfg dfg n op' (inst::acc)
                | _ => acc)
             else acc)
    | _ => acc
End

val _ = export_theory();
