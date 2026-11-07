Theory concretizeLayoutPhaseParam
Ancestors concretizeLayoutPhaseOrigin concretizeLayoutPhaseAdministration
  concretizeLayoutLocalParam concretizeLayoutCalleeRoots frameOriginUpdates frameResolvedTrace
  frameResolvedOrigins venomExecSemantics venomState venomInst ptrDiscipline list

Theorem layout_param_trace_step:
  vs0.vs_allocas = FEMPTY /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = PARAM /\ inst.inst_outputs = [v] /\
  MEM inst (fn_insts fn) /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK post ==>
  ?k tpost. step_inst_base inst t = OK tpost /\ k.lop_pending /\
    k.lop_cursor = SUC g.lop_cursor /\
    k.lop_origin = g.lop_origin /\ k.lop_ids = g.lop_ids /\
    k.lop_config = EL (SUC g.lop_cursor) (q0::qs) /\
    resolved_annotation_update g.lop_config (EL g.lop_cursor es)
      g.lop_ids g.lop_anns k.lop_anns /\
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
  `PG = MAP (OPTION_MAP SND) rp /\
   resolution (resolved_cache birth s.vs_allocas) rp om rv` by
    fs[resolved_config_ok_def, resolved_frame_ok_def] >>
  rule_assum_tac (REWRITE_RULE[ETA_AX]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`)
    (REWRITE_RULE[GSYM concretizeLayoutSupplementTheory.concretize_local_obs_def, ETA_AX]
      (Q.INST [`D` |-> `<| d_stor := K (K UNIV); d_trans := K (K UNIV);
        d_imm := K UNIV; d_ret := K {} |>`]
        (SPEC_ALL concretize_param_local_complete))) >>
  disch_then (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  disch_then (drule_at (Pat `resolution _ _ _ _`)) >>
  simp[] >> strip_tac >>
  `post = update_var v (EL (w2n idx) s.vs_params) s /\
   tpost = update_var v (EL (w2n idx) t.vs_params) t` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
       [`step_inst_base inst s = OK post`, `step_inst_base inst t = OK tpost`] >>
     pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[opcode_case_def] >>
     simp[AllCaseEqs()] >> metis_tac[]) >>
  `resolved_out birth post.vs_allocas rp (origin_out PG om inst post) =
     resolved_parameter_entry rp (w2n idx)` by
    (simp[origin_out_def, resolved_out_def, resolve_tag_def,
       resolved_parameter_entry_def, EL_MAP] >>
     Cases_on `w2n idx < LENGTH rp` >> simp[] >>
     Cases_on `EL (w2n idx) rp` >> simp[] >> PairCases_on `x` >> simp[]) >>
  `step_inst fuel C inst s = OK post` by simp[step_inst_non_invoke] >>
  `?k. k.lop_pending /\ k.lop_cursor = SUC g.lop_cursor /\
    k.lop_target_taint = step_taint inst t tpost g.lop_target_taint /\
    k.lop_origin = g.lop_origin /\ k.lop_ids = g.lop_ids /\
    k.lop_config = EL (SUC g.lop_cursor) (q0::qs) /\
    resolved_annotation_update g.lop_config (EL g.lop_cursor es)
      g.lop_ids g.lop_anns k.lop_anns /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q
      (INL g) (INL k) (OK post) (OK tpost)` suffices_by
    (strip_tac >> qexistsl_tac [`k`, `tpost`] >> gvs[]) >>
  irule layout_var_gas_success_phase >> simp[] >>
  goal_assum (drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[is_terminator_def, ETA_AX] >>
  gvs[update_var_def, step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
  simp[venom_state_component_equality] >> metis_tac[]
QED
