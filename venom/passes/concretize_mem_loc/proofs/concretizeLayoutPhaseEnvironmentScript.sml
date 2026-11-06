Theory concretizeLayoutPhaseEnvironment
Ancestors concretizeLayoutPhaseOrigin concretizeLayoutPhaseAdministration
  concretizeLayoutLocalEnvironment concretizeLayoutSupplement concretizeLayoutReaderContext
  frameOriginUpdates frameResolvedTrace
  venomExecSemantics venomState venomInst ptrDiscipline list

Theorem layout_environment_trace_step:
  vs0.vs_allocas = FEMPTY /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  (inst.inst_opcode = CALLER \/ inst.inst_opcode = ADDRESS \/
   inst.inst_opcode = CALLVALUE \/ inst.inst_opcode = GAS) /\
  inst.inst_outputs = [v] /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK post ==>
  ?k tpost. step_inst_base inst t = OK tpost /\ k.lop_pending /\
    k.lop_cursor = SUC g.lop_cursor /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q
      (INL g) (INL k) (OK post) (OK tpost)
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    fs[layout_ordinary_entry_def] >>
  `joint_trace vs0 C q0 es qs q /\
   EL g.lop_cursor (q0::qs) = g.lop_config /\
   resolved_config_ok g.lop_config g.lop_ids g.lop_anns` by
    fs[layout_ordinary_trace_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >> fs[ETA_AX] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`)
    (REWRITE_RULE[GSYM concretize_local_obs_def, ETA_AX]
      (Q.INST [`D` |-> `<| d_stor := K (K UNIV); d_trans := K (K UNIV);
        d_imm := K UNIV; d_ret := K {} |>`]
        (SPEC_ALL concretize_env_reader_local_complete))) >>
  disch_then (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[] >> strip_tac >>
  `?z rs. post = update_var v z (s with vs_gas_readings := rs)` by
    (qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[opcode_case_def] >>
     simp[exec_read0_def, exec_gas_def, AllCaseEqs()] >>
     strip_tac >> gvs[] >> simp[update_var_def, venom_state_component_equality] >> metis_tac[]) >>
  `?w rt. tpost = update_var v w (t with vs_gas_readings := rt)` by
    (qpat_x_assum `step_inst_base inst t = OK tpost` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[opcode_case_def] >>
     simp[exec_read0_def, exec_gas_def, AllCaseEqs()] >>
     strip_tac >> gvs[] >> simp[update_var_def, venom_state_component_equality] >> metis_tac[]) >>
  `concretize_supplement D (step_taint inst s post tn) post tpost /\
   post.vs_inst_idx = s.vs_inst_idx /\ relocation_reader_context post tpost /\
   post.vs_code = tpost.vs_code /\ post.vs_data_section = tpost.vs_data_section /\
   post.vs_initial_fmp = tpost.vs_initial_fmp /\
   post.vs_params = s.vs_params /\ tpost.vs_params = t.vs_params` by
    (irule layout_var_gas_administration >>
     simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
     metis_tac[]) >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DALLOCA /\
   ~is_terminator inst.inst_opcode /\ origin_out PG om inst post = NONE` by
    simp[is_terminator_def, origin_out_def] >>
  `step_inst fuel C inst s = OK post` by simp[step_inst_non_invoke] >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    concretizeLayoutPhaseSuccessTheory.layout_ordinary_success_phase >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[resolved_out_def, ETA_AX] >>
  disch_then (qspec_then `tpost` mp_tac) >> gvs[] >> metis_tac[]
QED
