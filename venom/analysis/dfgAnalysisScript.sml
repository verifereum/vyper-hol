(*
 * DFG Analysis
 *
 * Port of venom/analysis/dfg.py.
 *)

Theory dfgAnalysis
Ancestors
  list finite_map pred_set
  orderedSet
  irOps

Datatype:
  dfg_analysis = <|
    dfg_inputs : (string, num list) fmap;
    dfg_outputs : (string, num) fmap
  |>
End

Definition dfg_empty_def:
  dfg_empty = <| dfg_inputs := FEMPTY; dfg_outputs := FEMPTY |>
End

Definition dfg_get_uses_def:
  dfg_get_uses dfg v =
    case FLOOKUP dfg.dfg_inputs v of NONE => [] | SOME s => s
End

Definition dfg_get_producing_def:
  dfg_get_producing dfg v = FLOOKUP dfg.dfg_outputs v
End

Definition dfg_add_use_def:
  dfg_add_use dfg v inst_id =
    let uses = dfg_get_uses dfg v in
    dfg with dfg_inputs := dfg.dfg_inputs |+ (v, ordset_add inst_id uses)
End

Definition dfg_remove_use_def:
  dfg_remove_use dfg v inst_id =
    let uses = dfg_get_uses dfg v in
    dfg with dfg_inputs := dfg.dfg_inputs |+ (v, ordset_remove inst_id uses)
End

Definition dfg_set_producing_def:
  dfg_set_producing dfg v inst_id =
    dfg with dfg_outputs := dfg.dfg_outputs |+ (v, inst_id)
End

Definition dfg_remove_producing_def:
  dfg_remove_producing dfg v =
    dfg with dfg_outputs := FDIFF dfg.dfg_outputs {v}
End

Definition fn_instructions_list_def:
  fn_instructions_list fn = FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)
End

Definition dfg_analyze_inst_def:
  dfg_analyze_inst dfg inst =
    let dfg1 =
      FOLDL (λacc v. dfg_add_use acc v inst.inst_id) dfg (inst_input_vars inst) in
    let dfg2 =
      FOLDL (λacc v. dfg_set_producing acc v inst.inst_id) dfg1 (inst_get_outputs inst) in
    dfg2
End

Definition dfg_analyze_def:
  dfg_analyze fn =
    FOLDL dfg_analyze_inst dfg_empty (fn_instructions_list fn)
End

Definition dfg_traverse_assign_chain_aux_def:
  dfg_traverse_assign_chain_aux fn dfg v 0 = v /\
  dfg_traverse_assign_chain_aux fn dfg v (SUC fuel) =
    case dfg_get_producing dfg v of
      NONE => v
    | SOME iid =>
        (case lookup_inst_in_function iid fn of
           NONE => v
         | SOME inst =>
             if inst.inst_opcode = ASSIGN then
               case inst.inst_operands of
                 [Var v2] => dfg_traverse_assign_chain_aux fn dfg v2 fuel
               | _ => v
             else v)
End

Definition dfg_traverse_assign_chain_def:
  dfg_traverse_assign_chain fn dfg v =
    dfg_traverse_assign_chain_aux fn dfg v (LENGTH (fn_instructions_list fn) + 1)
End

Definition dfg_are_equivalent_def:
  dfg_are_equivalent fn dfg op1 op2 =
    if op1 = op2 then T
    else
      case (op1, op2) of
        (Var v1, Var v2) =>
          dfg_traverse_assign_chain fn dfg v1 = dfg_traverse_assign_chain fn dfg v2
      | _ => F
End

Definition dfg_get_transitive_uses_aux_def:
  dfg_get_transitive_uses_aux fn dfg work seen 0 = seen /\
  dfg_get_transitive_uses_aux fn dfg work seen (SUC fuel) =
    case work of
      [] => seen
    | (i::rest) =>
        if MEM i seen then dfg_get_transitive_uses_aux fn dfg rest seen fuel
        else
          let seen' = ordset_add i seen in
          let more =
            case lookup_inst_in_function i fn of
              NONE => []
            | SOME inst =>
                case inst_output inst of
                  NONE => []
                | SOME v => dfg_get_uses dfg v in
          dfg_get_transitive_uses_aux fn dfg (rest ++ more) seen' fuel
End

Definition dfg_get_transitive_uses_def:
  dfg_get_transitive_uses fn dfg inst_id =
    let n = LENGTH (fn_instructions_list fn) in
    let fuel = n * n + 1 in
    dfg_get_transitive_uses_aux fn dfg [inst_id] [] fuel
End

val _ = export_theory();
