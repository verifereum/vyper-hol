Theory concretizeLayoutPhaseHalt
Ancestors concretizeLayoutPhaseOrigin concretizeLayoutHaltExit
  concretizeLayoutLocalTerminals concretizeLayoutSupplement
  frameJointTrace frameJointTransition frameOriginHistory frameOriginReachable
  frameRelocationLocal ptrDiscipline venomExecSemantics venomState venomInst
  list pred_set

Theorem layout_stop_sink_halt:
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  MEM inst.inst_opcode [STOP; SINK] /\ taint_within D C vs0 /\
  active_inst fn inst s /\ step_inst fuel C inst s = Halt post ==>
  ?tpost. step_inst fuel' C' inst t = Halt tpost /\
    dead_result_rel D (Halt post) (Halt tpost)
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    fs[layout_ordinary_entry_def] >>
  `joint_config_reachable vs0 C g.lop_config` by
    (fs[layout_ordinary_trace_def] >>
     drule joint_trace_prefix_reachable >>
     pure_rewrite_tac[EVERY_EL] >>
     disch_then (qspec_then `g.lop_cursor` mp_tac) >> simp[]) >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (gvs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `concretize_local_obs s t /\ concretize_supplement D tn s t` by
    (qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[layout_ordinary_state_def, local_rel_def] >> metis_tac[]) >>
  `inst.inst_opcode <> INVOKE` by fs[] >>
  `step_inst_base inst s = Halt post` by
    fs[step_inst_non_invoke] >>
  drule_all (REWRITE_RULE[GSYM concretize_local_obs_def]
    (Q.INST [`D` |-> `<| d_stor := K (K UNIV); d_trans := K (K UNIV);
      d_imm := K UNIV; d_ret := K {} |>`]
      (SPEC_ALL concretize_stop_sink_complete))) >> strip_tac >>
  `final_taint vs0 C post (step_taint inst s post tn) (ret_taint tn inst s)` by
    (simp[final_taint_def] >> metis_tac[]) >>
  qexists_tac `post'` >> conj_tac
  >- simp[step_inst_non_invoke] >>
  `concretize_supplement D (step_taint inst s post tn) post post'` by
    (fs[MEM] >>
     qpat_x_assum `step_inst_base inst s = Halt post` mp_tac >>
     qpat_x_assum `step_inst_base inst t = Halt post'` mp_tac >>
     simp[Once step_inst_base_def] >>
     simp[Once step_inst_base_def] >>
     rpt strip_tac >> gvs[] >>
     fs[concretize_supplement_def, halt_state_def, step_taint_def,
        store_taint_def, adopt_reset_def, imm_taint_def]) >>
  irule concretize_supplement_halt_exit >>
  fs[concretize_local_obs_def, dead_result_rel_def] >>
  qexistsl_tac [`C`, `ret_taint tn inst s`, `step_taint inst s post tn`, `vs0`] >>
  simp[] >> fs[ret_taint_def, MEM]
QED
