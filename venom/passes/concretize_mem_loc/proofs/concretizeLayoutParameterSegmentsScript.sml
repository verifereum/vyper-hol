Theory concretizeLayoutParameterSegments
Ancestors concretizeLayoutParameterSteps frameBlockSegments
  venomExecSemantics venomState venomInst venomInstProofs

(* Control is separate from local_rel.  This tuple is deliberately about
   the next executable position, not about the relocated values. *)
Definition parameter_control_def:
  parameter_control s =
    (s.vs_current_bb, s.vs_prev_bb, s.vs_inst_idx, s.vs_halted)
End

Theorem parameter_step_control[local]:
  inst.inst_opcode = PARAM /\ step_inst_base inst s = OK post ==>
  parameter_control post = parameter_control s
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  simp[Once step_inst_base_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), parameter_control_def, update_var_def]
QED

(* Exercise the accepted PARAM producer through the executable wrapper and
   build actual fixed-fuel segments.  No equality of parameters is inferred
   from local_rel: the resolved parameter roots remain an explicit input. *)
Theorem resolved_parameter_segment:
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\
  parameter_roots (\i x y. clean_resolved_root L (resolved_parameter_entry rp i) x y)
    s.vs_params t.vs_params /\
  PG = MAP (OPTION_MAP SND) rp /\ resolution ct rp om rv /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  relocation_taint_le R tn un /\
  (!a b x y. Obs a b ==> Obs (update_var out x a) (update_var out y b)) /\
  parameter_control s = parameter_control t /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb' t.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK post ==>
  ?post' rv'.
    block_segment fuel ctx bb s
      (post with vs_inst_idx := SUC s.vs_inst_idx) /\
    block_segment fuel' ctx' bb' t
      (post' with vs_inst_idx := SUC t.vs_inst_idx) /\
    exec_block fuel ctx bb s =
      exec_block fuel ctx bb (post with vs_inst_idx := SUC s.vs_inst_idx) /\
    exec_block fuel' ctx' bb' t =
      exec_block fuel' ctx' bb' (post' with vs_inst_idx := SUC t.vs_inst_idx) /\
    parameter_control (post with vs_inst_idx := SUC s.vs_inst_idx) =
      parameter_control (post' with vs_inst_idx := SUC t.vs_inst_idx) /\
    resolution ct rp (origin_step PG om inst post) rv' /\
    local_rel (\u. F) (guarded_ptr Opaque L rv')
      (guarded_bytes Opaque rv' (step_taint inst s post tn)) R Obs post post' /\
    relocation_taint_le R (step_taint inst s post tn)
      (step_taint inst t post' un) /\
    parameter_roots (\i x y. clean_resolved_root L (resolved_parameter_entry rp i) x y)
      post.vs_params post'.vs_params
Proof
  strip_tac >>
  `step_inst_base inst s = OK post` by
    gvs[Once step_inst_def] >>
  drule_all resolved_parameter_step >> strip_tac >>
  `parameter_control post = parameter_control s` by
    (metis_tac[parameter_step_control]) >>
  `parameter_control post' = parameter_control t` by
    (metis_tac[parameter_step_control]) >>
  `block_segment fuel ctx bb s
     (post with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule block_segment_next >> qexistsl_tac [`inst`, `post`] >>
     simp[block_segment_rules, is_terminator_def]) >>
  `block_segment fuel' ctx' bb' t
     (post' with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule block_segment_next >> qexistsl_tac [`inst`, `post'`] >>
     simp[block_segment_rules, is_terminator_def, Once step_inst_def]) >>
  qexistsl_tac [`post'`, `rv'`] >>
  simp[block_segment_replay] >> gvs[parameter_control_def]
QED
