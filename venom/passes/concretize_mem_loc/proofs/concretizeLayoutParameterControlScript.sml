Theory concretizeLayoutParameterControl
Ancestors concretizeLayoutParameterSegments concretizeLayoutParameterSteps
  frameRelocationControl frameRelocationLocal frameRelocationGuardedValues
  frameBlockSegments venomState venomInst

(* PARAM's accepted segment producer relates the immediate post-states.
   This adapter relates the actual continuation endpoints, with a distinct
   observation supplied for those endpoints. *)
Theorem resolved_parameter_continuation:
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\
  parameter_roots (\i x y. clean_resolved_root L (resolved_parameter_entry rp i) x y)
    s.vs_params t.vs_params /\
  PG = MAP (OPTION_MAP SND) rp /\ resolution ct rp om rv /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  relocation_taint_le R tn un /\
  (!a b x y. Obs a b ==> Obs (update_var out x a) (update_var out y b)) /\
  control_transport Obs NextObs
    (\a. a with vs_inst_idx := SUC s.vs_inst_idx)
    (\b. b with vs_inst_idx := SUC t.vs_inst_idx) /\
  parameter_control s = parameter_control t /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb' t.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK post ==>
  ?post' rv'.
    block_segment fuel ctx bb s
      (post with vs_inst_idx := SUC s.vs_inst_idx) /\
    block_segment fuel' ctx' bb' t
      (post' with vs_inst_idx := SUC t.vs_inst_idx) /\
    parameter_control (post with vs_inst_idx := SUC s.vs_inst_idx) =
      parameter_control (post' with vs_inst_idx := SUC t.vs_inst_idx) /\
    resolution ct rp (origin_step PG om inst post) rv' /\
    local_rel (\u. F) (guarded_ptr Opaque L rv')
      (guarded_bytes Opaque rv' (step_taint inst s post tn)) R NextObs
      (post with vs_inst_idx := SUC s.vs_inst_idx)
      (post' with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> drule_all resolved_parameter_segment >>
  disch_then (qspecl_then [`fuel'`, `ctx'`] strip_assume_tac) >>
  drule local_rel_index_transport >> strip_tac >>
  qexistsl_tac [`post'`, `rv'`] >> simp[] >>
  metis_tac[control_transport_def]
QED

val _ = export_theory();
