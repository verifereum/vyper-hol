Theory concretizeLayoutPhaseCopy
Ancestors concretizeLayoutPhaseOrigin concretizeLayoutPhaseSuccess
  concretizeLayoutLocalCopy concretizeLayoutSupplement concretizeLayoutReaderContext
  frameRelocationEnvironment frameOriginUpdates frameResolvedTrace
  venomExecSemantics venomState venomInst memSafeRun o1PassContract ptrDiscipline list

Theorem layout_mcopy_trace_step:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  ~joint_read_exempt (EL g.lop_cursor (q0::qs)) /\
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [opd;ops;opn] /\
  inst.inst_outputs = [] /\ o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
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
   resolved_config_ok g.lop_config g.lop_ids g.lop_anns /\
   lifetime_ok g.lop_bound g.lop_ids g.lop_config` by
    fs[layout_ordinary_trace_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >> fs[ETA_AX] >>
  `?dst src sz. eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
    eval_operand opn s = SOME sz` by
    (qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[opcode_case_def] >>
     simp[AllCaseEqs()] >> metis_tac[]) >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`)
    (REWRITE_RULE[GSYM concretize_local_obs_def, ETA_AX]
      (Q.INST [`D` |-> `<| d_stor := K (K UNIV); d_trans := K (K UNIV);
        d_imm := K UNIV; d_ret := K {} |>`]
        (SPEC_ALL concretize_mcopy_local_complete))) >>
  disch_then (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  disch_then (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok _ _`)) >> simp[] >> disch_then drule_all >> strip_tac >>
  `concretize_supplement D (step_taint inst s post tn) post tpost /\
   relocation_reader_context post tpost /\ relocation_env post tpost /\
   post.vs_code = tpost.vs_code /\ post.vs_data_section = tpost.vs_data_section /\
   post.vs_inst_idx = s.vs_inst_idx /\ post.vs_initial_fmp = tpost.vs_initial_fmp /\
   post.vs_params = s.vs_params /\ tpost.vs_params = t.vs_params` by
    (fs[venom_state_component_equality] >> rpt conj_tac
     >- (irule concretize_supplement_fields >>
         goal_assum (drule_at (Pat `concretize_supplement _ _ _ _`)) >>
         simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def]) >>
     fs[relocation_reader_context_def, relocation_env_def]) >>
  `step_inst fuel C inst s = OK post` by simp[step_inst_non_invoke] >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_ordinary_success_phase >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[is_terminator_def, origin_set_def, finite_mapTheory.DRESTRICT_UNIV, ETA_AX] >>
  disch_then (qspec_then `tpost` mp_tac) >> simp[] >> metis_tac[]
QED
