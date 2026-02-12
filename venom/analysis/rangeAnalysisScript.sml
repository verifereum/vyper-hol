(*
 * Range Analysis (lightweight interval analysis)
 *
 * Computes per-(inst_id, operand) interval facts used by algebraic optimization.
 * The result format matches range_lookup in algebraicOptDefs.
 *)

Theory rangeAnalysis
Ancestors
  dfgAnalysis

Datatype:
  value_range = <|
    vr_is_top: bool;
    vr_is_empty: bool;
    vr_lo: int;
    vr_hi: int
  |>
End

Definition range_top_def:
  range_top = <|
    vr_is_top := T;
    vr_is_empty := F;
    vr_lo := 0;
    vr_hi := 0
  |>
End

Definition range_lookup_def:
  range_lookup ranges inst_id op =
    case ALOOKUP ranges (inst_id, op) of
      SOME r => r
    | NONE => range_top
End

(* ==========================================================================
   Small helpers
   ========================================================================== *)

Definition rev_prepend_def:
  rev_prepend xs acc =
    case xs of
      [] => acc
    | x::rest => rev_prepend rest (x::acc)
End

Definition range_singleton_def:
  range_singleton i = <|
    vr_is_top := F;
    vr_is_empty := F;
    vr_lo := i;
    vr_hi := i
  |>
End

Definition range_interval_def:
  range_interval lo hi =
    if lo > hi then
      <| vr_is_top := F; vr_is_empty := T; vr_lo := lo; vr_hi := hi |>
    else
      <| vr_is_top := F; vr_is_empty := F; vr_lo := lo; vr_hi := hi |>
End

Definition lit_unsigned_int_def:
  lit_unsigned_int op =
    case op of
      Lit w => SOME (((& (w2n w)) : int))
    | _ => NONE
End

(* ==========================================================================
   Operand range under DFG
   ========================================================================== *)

Definition range_of_operand_dfg_def:
  range_of_operand_dfg dfg 0 op = range_top /\
  range_of_operand_dfg dfg (SUC fuel) op =
    case op of
      Lit w => range_singleton (((& (w2n w)) : int))
    | Var v =>
        (case dfg_get_def dfg v of
           NONE => range_top
         | SOME inst =>
             case inst.inst_opcode of
               ASSIGN =>
                 (case inst.inst_operands of
                    [op1] => range_of_operand_dfg dfg fuel op1
                  | _ => range_top)
             | ISZERO => range_interval 0 1
             | EQ => range_interval 0 1
             | LT => range_interval 0 1
             | GT => range_interval 0 1
             | SLT => range_interval 0 1
             | SGT => range_interval 0 1
             | AND =>
                 (case inst.inst_operands of
                    [op1; op2] =>
                      (case lit_unsigned_int op1 of
                         SOME n => range_interval 0 n
                       | NONE =>
                           (case lit_unsigned_int op2 of
                              SOME n2 => range_interval 0 n2
                            | NONE => range_top))
                  | _ => range_top)
             | Mod =>
                 (case inst.inst_operands of
                    [op1; op2] =>
                      (case lit_unsigned_int op1 of
                         SOME n =>
                           if n = 0 then range_singleton 0
                           else range_interval 0 (n - 1)
                       | NONE =>
                           (case lit_unsigned_int op2 of
                              SOME n2 =>
                                if n2 = 0 then range_singleton 0
                                else range_interval 0 (n2 - 1)
                            | NONE => range_top))
                  | _ => range_top)
             | _ => range_top)
    | _ => range_top
End

(* ==========================================================================
   Whole-function analysis
   ========================================================================== *)

Definition range_entries_for_operands_def:
  range_entries_for_operands dfg fuel inst_id ops =
    case ops of
      [] => []
    | op::rest =>
        ((inst_id, op), range_of_operand_dfg dfg fuel op) ::
        range_entries_for_operands dfg fuel inst_id rest
End

Definition range_analyze_insts_acc_def:
  range_analyze_insts_acc dfg fuel insts acc =
    case insts of
      [] => REVERSE acc
    | inst::rest =>
        let rs = range_entries_for_operands dfg fuel inst.inst_id inst.inst_operands in
          range_analyze_insts_acc dfg fuel rest (rev_prepend rs acc)
End

Definition range_analyze_def:
  range_analyze fn =
    let insts = fn_insts fn in
    let dfg = dfg_build_insts insts in
    let fuel = SUC (LENGTH insts) in
      range_analyze_insts_acc dfg fuel insts []
End

val _ = export_theory();
