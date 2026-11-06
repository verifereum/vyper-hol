Theory concretizeLayoutPhaseReturndataSize
Ancestors concretizeLayoutPhaseBindings concretizeLayoutPhaseOrigin
  concretizeLayoutPhaseSuccess concretizeLayoutLocalReturndataSize
  concretizeLayoutSupplement frameRelocationEnvironment frameRelocationLocal
  frameOriginUpdates frameResolvedTrace venomExecSemantics venomState venomInst
  ptrDiscipline

Theorem layout_returndatasize_trace_step:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = RETURNDATASIZE /\ inst.inst_outputs = [v] /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
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
  `?z. post = update_var v z s /\ step_inst_base inst t = OK (update_var v z t)` by
    (irule (REWRITE_RULE[GSYM concretize_local_obs_def]
      (Q.INST [`D` |-> `<| d_stor := K (K UNIV); d_trans := K (K UNIV);
        d_imm := K UNIV; d_ret := K {} |>`] (SPEC_ALL returndatasize_execution))) >>
     fs[local_rel_def]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`)
    (REWRITE_RULE[GSYM concretize_local_obs_def, ETA_AX]
      (Q.INST [`D` |-> `<| d_stor := K (K UNIV); d_trans := K (K UNIV);
        d_imm := K UNIV; d_ret := K {} |>`]
        (SPEC_ALL concretize_returndatasize_local_complete))) >>
  disch_then (drule_at (Pat `step_inst_base _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  disch_then (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok _ _`)) >>
  simp[] >> strip_tac >>
  `concretize_supplement D (step_taint inst s post tn) post (update_var v z t)` by
    (gvs[] >> simp[returndatasize_ghosts] >>
     irule concretize_supplement_fields >>
     goal_assum (drule_at Any) >> simp[update_var_def]) >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DALLOCA /\
   ~is_terminator inst.inst_opcode /\ origin_out PG om inst post = NONE` by
    simp[is_terminator_def, origin_out_def] >>
  `step_inst fuel C inst s = OK post` by simp[step_inst_non_invoke] >>
  `post.vs_inst_idx = s.vs_inst_idx /\
   post.vs_code = t.vs_code /\ post.vs_data_section = t.vs_data_section` by
    simp[update_var_def] >>
  qpat_assum `post = _` (fn th => fs[GSYM th]) >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_ordinary_success_phase >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[resolved_out_def, ETA_AX] >>
  disch_then (qspec_then `update_var v z t` mp_tac) >>
  gvs[] >> simp[update_var_def] >>
  metis_tac[ctxLookupAgreeHelpersTheory.step_inst_base_initial_fmp]
QED
