(* Exact instruction construction from the original DFG child results. *)
Theory venomDfgEval
Ancestors dfgDefs finite_map

Theorem dfg_record_fields:
  !(dfg : dfg_analysis).
    dfg = <| dfg_uses := dfg.dfg_uses;
             dfg_defs := dfg.dfg_defs;
             dfg_ids := dfg.dfg_ids |>
Proof
  simp[dfg_analysis_component_equality]
QED

Theorem dfg_add_inst_result:
  !dfg inst uses defs.
    dfg_add_uses dfg (operand_vars inst.inst_operands) inst = uses /\
    dfg_add_defs uses inst.inst_outputs inst = defs ==>
    dfg_add_inst dfg inst =
      (defs with dfg_ids := defs.dfg_ids |+ (inst.inst_id,inst))
Proof
  rpt gen_tac >> strip_tac >> simp[dfg_add_inst_def]
QED

Theorem dfg_add_use_result:
  !dfg v inst uses.
    dfg_get_uses dfg v = uses ==>
    dfg_add_use dfg v inst =
      if MEM inst uses then dfg
      else dfg with dfg_uses := dfg.dfg_uses |+ (v,inst::uses)
Proof
  rpt gen_tac >> strip_tac >> simp[dfg_add_use_def]
QED
