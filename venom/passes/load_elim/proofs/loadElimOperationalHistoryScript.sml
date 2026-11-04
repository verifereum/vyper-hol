Theory loadElimOperationalHistory
Ancestors
  loadElimHistoryHelpers venomInstProofs venomExecProofs

(* Caller-level events include INVOKE output binding, without flattening the
   callee execution or recording its private variable environment. *)
Theorem le_step_inst_event:
  step_inst fuel ctx inst s = OK t ==>
  le_framed_history s [(set inst.inst_outputs,t)]
Proof
  simp[le_framed_history_def] >> rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_terminator_preserves_vars] >>
  metis_tac[step_preserves_non_output_vars]
QED
