Theory concretizeLayoutPhaseNop
Ancestors concretizeLayoutPhaseOrigin concretizeLayoutPhaseSuccess
  concretizeLayoutLocalNop concretizeLayoutSupplement frameOriginUpdates
  frameResolvedTrace venomExecSemantics venomState venomInst venomWf o1PassContract

Theorem layout_nop_trace_step:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = NOP /\ o1_fn_shape C fn /\ fn_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK post ==>
  ?k. step_inst_base inst t = OK t /\ k.lop_pending /\
    k.lop_cursor = SUC g.lop_cursor /\
    k.lop_origin = g.lop_origin /\ k.lop_ids = g.lop_ids /\
    k.lop_config = EL (SUC g.lop_cursor) (q0::qs) /\
    resolved_annotation_update g.lop_config (EL g.lop_cursor es)
      g.lop_ids g.lop_anns k.lop_anns /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q
      (INL g) (INL k) (OK post) (OK t)
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    fs[layout_ordinary_entry_def] >>
  `joint_trace vs0 C q0 es qs q /\
   EL g.lop_cursor (q0::qs) = g.lop_config /\
   resolved_config_ok g.lop_config g.lop_ids g.lop_anns` by
    fs[layout_ordinary_trace_def] >>
  `inst_wf inst` by
    (fs[o1_fn_shape_def, fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf inst` mp_tac >> simp[inst_wf_def]) >>
  `post = s` by gvs[step_inst_base_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >> fs[ETA_AX] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`)
    (REWRITE_RULE[GSYM concretize_local_obs_def, ETA_AX]
      (Q.INST [`D` |-> `<| d_stor := K (K UNIV); d_trans := K (K UNIV);
        d_imm := K UNIV; d_ret := K {} |>`]
        (SPEC_ALL concretize_nop_local_complete))) >>
  disch_then (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok _ _`)) >> simp[] >> strip_tac >>
  `inst.inst_opcode <> DALLOCA /\ ~is_terminator inst.inst_opcode /\
   origin_out PG om inst post = NONE /\ step_inst fuel C inst post = OK post` by
    simp[is_terminator_def, origin_out_def, step_inst_non_invoke, step_inst_base_def] >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_ordinary_success_phase >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[origin_set_def, finite_mapTheory.DRESTRICT_UNIV, ETA_AX] >>
  disch_then (qspec_then `t` mp_tac) >> gvs[] >> metis_tac[]
QED
