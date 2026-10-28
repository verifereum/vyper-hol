(* Block observations of the existing finite dominance checker. *)
Theory codegenReadyObservations
Ancestors codegenReadyCompute passSharedDefs list

Definition block_def_uses_exec_def:
  block_def_uses_exec cfg dom func bb =
    EVERY (\inst.
      if inst.inst_opcode = PHI then phi_edge_uses_wf_exec cfg dom func bb inst
      else EVERY (\op. case op of
          Var v => def_available_at_exec cfg dom func bb (SOME inst) v
        | _ => T) inst.inst_operands) bb.bb_instructions
End

Theorem def_dominates_uses_exec_blocks[compute]:
  def_dominates_uses_exec func =
    let cfg = cfg_analyze func in
    let dom = dom_analyze cfg func in
      EVERY (block_def_uses_exec cfg dom func) func.fn_blocks
Proof
  simp[def_dominates_uses_exec_def, LET_THM] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, block_def_uses_exec_def]
QED

Definition var_single_use_def:
  var_single_use func v <=> SUM (MAP (var_use_count_block v) func.fn_blocks) <= 1
End

Theorem single_use_form_variables[compute]:
  single_use_form func = EVERY (var_single_use func) (fn_used_vars func)
Proof
  rewrite_tac[single_use_form_compute] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, var_single_use_def]
QED
