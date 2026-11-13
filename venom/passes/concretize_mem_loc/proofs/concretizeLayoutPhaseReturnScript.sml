Theory concretizeLayoutPhaseReturn
Ancestors concretizeLayoutLocalReturn concretizeLayoutPhaseOrigin
  concretizeLayoutScopedPhase frameJointTrace frameJointTransition
  frameOriginHistory frameOriginReachable frameRelocationLocal
  concretizeLayoutReaderContext frameRelocationEnvironment
  venomExecSemantics venomInst list rich_list

Theorem layout_return_halt:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  active_inst fn inst s /\ inst.inst_opcode = RETURN /\
  taint_within D C vs0 /\ step_inst fuel C inst s = Halt post ==>
  ?post'. step_inst fuel' C' inst t = Halt post' /\
    dead_result_rel D (Halt post) (Halt post')
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    metis_tac[layout_ordinary_ready] >>
  qpat_x_assum `layout_ordinary_trace _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_trace_def, layout_ordinary_state_def] >> rpt strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  `g.lop_cursor <= LENGTH es` by fs[] >>
  `joint_config_reachable vs0 C g.lop_config` by
    (drule joint_trace_prefix_reachable >> pure_rewrite_tac[EVERY_EL] >>
     disch_then (qspec_then `g.lop_cursor` mp_tac) >> simp[]) >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (gvs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  `step_inst_base inst s = Halt post` by fs[step_inst_non_invoke] >>
  drule_all return_execution_envelope >> strip_tac >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  gvs[] >>
  `g.lop_cursor <= LENGTH es` by simp[] >>
  drule_all concretize_return_read_agreement >> strip_tac >>
  `concretize_local_obs s t` by metis_tac[local_rel_def] >>
  drule_all concretize_return_observation >> strip_tac >>
  qexists_tac `post'` >> simp[step_inst_non_invoke]
QED

val _ = export_theory();
