Theory concretizeLayoutPhaseSuccess
Ancestors concretizeLayoutPhaseBindings concretizeLayoutPhaseOrigin
  concretizeLayoutSupplement frameRelocationLocal frameRelocationGuardedValues
  frameRelocationTaintOrder frameJointDemand frameRelocationBinding
  concretizeLayoutPhaseInputs frameResolvedCoherent

Theorem layout_ordinary_success_phase:
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  inst.inst_opcode <> DALLOCA /\ g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  post.vs_inst_idx = s.vs_inst_idx /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK post /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk))
      (origin_set rv inst.inst_outputs
        (resolved_out birth post.vs_allocas rp (origin_out PG om inst post))))
    (guarded_bytes (retpc_var fn)
      (origin_set rv inst.inst_outputs
        (resolved_out birth post.vs_allocas rp (origin_out PG om inst post)))
      (step_taint inst s post tn))
    (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC g.lop_cursor))
    concretize_local_obs post tpost /\
  relocation_taint_le
    (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC g.lop_cursor))
    (step_taint inst s post tn) un /\
  concretize_supplement D (step_taint inst s post tn) post tpost /\
  relocation_env post tpost /\ relocation_reader_context post tpost /\
  post.vs_code = tpost.vs_code /\ post.vs_data_section = tpost.vs_data_section /\
  post.vs_initial_fmp = tpost.vs_initial_fmp /\
  post.vs_params = s.vs_params /\ tpost.vs_params = t.vs_params ==>
  ?k. k.lop_pending /\ k.lop_cursor = SUC g.lop_cursor /\ k.lop_target_taint = un /\
    k.lop_origin = g.lop_origin /\ k.lop_ids = g.lop_ids /\
    k.lop_config = EL (SUC g.lop_cursor) (q0::qs) /\
    resolved_annotation_update g.lop_config (EL g.lop_cursor es)
      g.lop_ids g.lop_anns k.lop_anns /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q
      (INL g) (INL k) (OK post) (OK tpost)
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   terminal_call_prefix C g.lop_origin.lbo_source g.lop_origin.lbo_entry s` by
    gvs[layout_ordinary_entry_def] >>
  drule_all layout_ordinary_bound_trace_advance >> strip_tac >>
  qexists_tac `k with lop_target_taint := un` >> simp[] >>
  conj_tac >- gvs[layout_phase_normalize_def] >>
  conj_tac >- simp[Once resolved_annotation_update_cases] >>
  irule layout_ordinary_pending_outcome >> simp[layout_phase_origin_def] >>
  conj_tac >- (drule_all layout_origin_successful_step >> simp[]) >>
  simp[] >> irule layout_ordinary_state_intro >> gvs[] >>
  goal_assum (drule_at Any o GSYM) >> simp[] >>
  gvs[layout_ordinary_entry_def, layout_ordinary_state_def]
QED

val _ = export_theory();
