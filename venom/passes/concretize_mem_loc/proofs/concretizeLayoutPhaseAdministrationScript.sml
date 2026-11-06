Theory concretizeLayoutPhaseAdministration
Ancestors concretizeLayoutPhaseSuccess concretizeLayoutPhaseOrigin
  concretizeLayoutSupplement concretizeLayoutReaderContext venomState

(* Independent gas tails are permitted: their agreement belongs to the local
   environment certificate, not to this record-preservation boundary. *)
Theorem layout_var_gas_administration:
  post = update_var v x (s with vs_gas_readings := rs) /\
  tpost = update_var w y (t with vs_gas_readings := rt) /\
  concretize_supplement D tn s t /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  relocation_reader_context s t /\ s.vs_code = t.vs_code /\
  s.vs_data_section = t.vs_data_section /\ s.vs_initial_fmp = t.vs_initial_fmp ==>
  concretize_supplement D tn' post tpost /\
  post.vs_inst_idx = s.vs_inst_idx /\ relocation_reader_context post tpost /\
  post.vs_code = tpost.vs_code /\ post.vs_data_section = tpost.vs_data_section /\
  post.vs_initial_fmp = tpost.vs_initial_fmp /\
  post.vs_params = s.vs_params /\ tpost.vs_params = t.vs_params
Proof
  strip_tac >> gvs[] >> conj_tac
  >- (irule concretize_supplement_fields >>
      goal_assum (drule_at (Pat `concretize_supplement _ _ _ _`)) >>
      simp[update_var_def]) >>
  gvs[update_var_def, relocation_reader_context_def]
QED

Theorem layout_var_gas_success_phase:
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  inst.inst_opcode <> DALLOCA /\ g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK post /\
  rv' = origin_set rv inst.inst_outputs
    (resolved_out birth post.vs_allocas rp (origin_out PG om inst post)) /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv')
    (guarded_bytes (retpc_var fn) rv' (step_taint inst s post tn))
    (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC g.lop_cursor))
    concretize_local_obs post tpost /\
  relocation_taint_le
    (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC g.lop_cursor))
    (step_taint inst s post tn) un /\
  relocation_env post tpost /\
  post = update_var v x (s with vs_gas_readings := rs) /\
  tpost = update_var w y (t with vs_gas_readings := rt) /\
  (step_taint inst s post tn).t_stor = tn.t_stor /\
  (step_taint inst s post tn).t_trans = tn.t_trans /\
  (step_taint inst s post tn).t_imm = tn.t_imm ==>
  ?k. k.lop_pending /\ k.lop_cursor = SUC g.lop_cursor /\ k.lop_target_taint = un /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q
      (INL g) (INL k) (OK post) (OK tpost)
Proof
  strip_tac >>
  `concretize_supplement D tn s t /\ relocation_reader_context s t /\
   s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section /\
   s.vs_initial_fmp = t.vs_initial_fmp` by
    gvs[layout_ordinary_entry_def, layout_ordinary_state_def] >>
  drule_all layout_var_gas_administration >> strip_tac >>
  irule layout_ordinary_success_phase >> gvs[update_var_def] >> metis_tac[]
QED
