Theory concretizeLayoutPhaseExternal
Ancestors concretizeLayoutPhaseOrigin concretizeLayoutPhaseSuccess
  concretizeLayoutExternalCall concretizeLayoutExternalCreate concretizeLayoutDelegate
  frameRelocationLocal frameRelocationEnvironment frameOriginUpdates frameResolvedTrace
  venomExecSemantics venomState venomInst memSafeRun o1PassContract list

Theorem layout_external_trace_step:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\ taint_within D C vs0 /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  ~joint_read_exempt (EL g.lop_cursor (q0::qs)) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode [CALL; STATICCALL; CREATE; CREATE2; DELEGATECALL] /\
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
   resolved_config_ok g.lop_config g.lop_ids g.lop_anns /\
   lifetime_ok g.lop_bound g.lop_ids g.lop_config` by
    fs[layout_ordinary_trace_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >> fs[ETA_AX] >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DALLOCA /\
   ~is_terminator inst.inst_opcode /\ origin_out PG om inst post = NONE` by
    (fs[MEM] >> simp[is_terminator_def, origin_out_def]) >>
  `MEM inst.inst_opcode [CALL; STATICCALL] \/
   MEM inst.inst_opcode [CREATE; CREATE2] \/ inst.inst_opcode = DELEGATECALL` by fs[MEM] >>
  FIRST
    [drule_at (Pat `MEM _ [CALL; STATICCALL]`)
       (REWRITE_RULE[ETA_AX] concretize_ext_call_local_complete),
     drule_at (Pat `MEM _ [CREATE; CREATE2]`)
       (REWRITE_RULE[ETA_AX] concretize_create_local_complete),
     drule_at (Pat `_ .inst_opcode = DELEGATECALL`)
       (REWRITE_RULE[ETA_AX] concretize_delegate_local_complete)] >>
  disch_then (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  disch_then (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `concretize_supplement _ _ _ _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `post.vs_inst_idx = s.vs_inst_idx` by metis_tac[step_inst_base_preserves_inst_idx] >>
  `step_inst fuel C inst s = OK post /\ step_inst fuel C' inst t = OK tpost` by
    simp[step_inst_non_invoke] >>
  `post.vs_code = tpost.vs_code /\ post.vs_data_section = tpost.vs_data_section` by
    metis_tac[step_inst_ok_code_data] >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_ordinary_success_phase >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[resolved_out_def, ETA_AX] >>
  disch_then (qspec_then `tpost` mp_tac) >> gvs[] >>
  metis_tac[ctxLookupAgreeHelpersTheory.step_inst_base_initial_fmp]
QED
