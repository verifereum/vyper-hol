Theory requestCutReplayPreWalk
Ancestors
  e2eRequestCutDefs o1ContractSimplifyCfgSrcFrame o1ContractSimplifyCfg
  o1DretDesugarContract o1PipelineCompose o1ComposeSupport o1RequestContract
  o1ContractSimplifyCfgSrcStatic simplifyCfgStaticInterface simplifyCfgShapeCore
  simplifyCfgProof simplifyCfgControl o1PassContract
  concretizePtrCoverageStaticMemReachability frameRawProjection
  ptrDiscipline ptrDisciplineAgree ctxLookupAgree unitMemInv
  fcgPruning o1ContractTheorems unitShapeDefs venomCompilerTypes
  lowerDloadDefs memSafeRun unitTransformDefs stateFrame contextRawReachable
  venomMemDefs codegenRel
  contextCodegenRel venomExecSemantics venomState venomInst finite_map list

Theorem scfg_request_cut_frame_rows:
  scfg_context_trace C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  ptr_discipline_rq_upto lo k C vs /\ (ctx_has_dalloca C' ==> ctx_has_dalloca C) /\
  frame_reachable vs C' stk PG G tn g j t /\ request_cut k t ==>
  access_ok lo G g j t /\ taint_ok g tn j t /\ allocas_from lo t /\
  (ctx_has_dalloca C' ==> allocas_below_fmp t)
Proof
  strip_tac >> drule_all scfg_context_trace_live_frame_back >> strip_tac >>
  `request_cut k s` by
    fs[request_cut_def, scfg_data_agree_def, execution_frame_def,
       venom_state_component_equality] >>
  `access_ok lo G f i s /\ taint_ok f tn i s /\ allocas_from lo s /\
   (ctx_has_dalloca C ==> allocas_below_fmp s)` by
    metis_tac[ptr_discipline_rq_upto_def] >>
  metis_tac[scfg_live_position_access_ok, scfg_live_position_trace_taint,
            scfg_data_agree_allocas]
QED

Theorem scfg_request_cut_taint:
  scfg_context_trace C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  taint_within_rq_upto D k C vs ==>
  taint_within_rq_upto D k C' vs
Proof
  strip_tac >> simp[taint_within_rq_upto_def] >> conj_tac
  >- (rpt strip_tac >>
      drule_all scfg_context_trace_live_frame_back >> strip_tac >>
      drule_all scfg_live_position_request_back >>
      disch_then (qspec_then `C` strip_assume_tac) >>
      rename1 `frame_reachable vs C fs PG G tn f i src` >>
      rename1 `step_inst fuel C i src = OK out` >>
      `active_inst f i src` by metis_tac[scfg_frame_reachable_active] >>
      `request_cut k src` by
        fs[request_cut_def, scfg_data_agree_def, execution_frame_def,
           venom_state_component_equality] >>
      qpat_x_assum `taint_within_rq_upto D k C vs` mp_tac >>
      simp[taint_within_rq_upto_def] >>
      disch_then (CONJUNCTS_THEN2 (mp_tac o Q.SPECL
        [`fs`, `PG`, `G`, `tn`, `f`, `i`, `src`, `fuel`, `out`]) (K all_tac)) >>
      fs[scfg_data_agree_def, execution_frame_def, venom_state_component_equality]) >>
  rpt strip_tac >>
  drule_all scfg_context_trace_live_frame_back >> strip_tac >>
  drule_all scfg_live_position_halt_back >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  rename1 `frame_reachable vs C fs PG G tn f i src` >>
  rename1 `step_inst fuel C i src = Halt out` >>
  `active_inst f i src` by metis_tac[scfg_frame_reachable_active] >>
  `request_cut k src` by
    fs[request_cut_def, scfg_data_agree_def, execution_frame_def,
       venom_state_component_equality] >>
  qpat_x_assum `taint_within_rq_upto D k C vs` mp_tac >>
  simp[taint_within_rq_upto_def] >>
  disch_then (CONJUNCTS_THEN2 (K all_tac) (mp_tac o Q.SPECL
    [`fs`, `PG`, `G`, `tn`, `f`, `i`, `src`, `fuel`, `out`])) >>
  simp[] >> strip_tac >> gvs[] >>
  imp_res_tac scfg_data_agree_step_taint >>
  imp_res_tac scfg_data_agree_ret_taint >>
  fs[scfg_data_agree_def, execution_frame_def, venom_state_component_equality] >>
  metis_tac[]
QED

Theorem scfg_request_cut_replay:
  scfg_context_trace C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  EVERY wf_function C.ctx_functions /\ raw_reachable vs C' g j t ==>
  ?f i s. raw_reachable vs C f i s /\
    s.vs_requests = t.vs_requests /\ s.vs_outcomes = t.vs_outcomes /\
    scfg_live_position_trace f i s g j t /\ scfg_data_agree s t
Proof
  strip_tac >> drule ptr_raw_reachable_frame >> strip_tac >>
  drule_all scfg_context_trace_live_frame_back >> strip_tac >>
  `raw_reachable vs C f i s` by metis_tac[frameRawProjectionTheory.frame_reachable_raw] >>
  qexistsl_tac [`f`, `i`, `s`] >> simp[] >>
  fs[scfg_data_agree_def, execution_frame_def, venom_state_component_equality]
QED

Theorem scfg_ctx_rq_upto:
  scfg_context_trace C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  EVERY wf_function C.ctx_functions ==>
  ctx_rq_upto D k C C' vs vs
Proof
  simp[ctx_rq_upto_def] >> rpt strip_tac >>
  drule_all scfg_request_cut_replay >> strip_tac >>
  qexistsl_tac [`f`, `i'`, `s`] >> simp[request_agree_except_refl]
QED

Theorem ctx_rq_upto_trans:
  dead_wf D /\ ctx_rq_upto D k C0 C1 s0 s1 /\
  ctx_rq_upto D k C1 C2 s1 s2 ==>
  ctx_rq_upto D k C0 C2 s0 s2
Proof
  rw[ctx_rq_upto_def] >> metis_tac[request_agree_except_trans]
QED

Theorem raw_safe_rq_upto_ctx_agree:
  ctx_agree R C C' /\ C'.ctx_entry = C.ctx_entry /\
  (!entry. C.ctx_entry = SOME entry ==> R entry) /\
  (!fn. MEM fn C'.ctx_functions ==> MEM fn C.ctx_functions) /\
  raw_safe_rq_upto D lo k C vs ==>
  raw_safe_rq_upto D lo k C' vs
Proof
  strip_tac >> fs[raw_safe_rq_upto_def] >>
  conj_tac
  >- (fs[ptr_discipline_rq_upto_def] >> conj_tac
      >- (qexists_tac `P` >> fs[EVERY_MEM]) >>
      rpt gen_tac >> strip_tac >>
      drule_all frame_reachable_ctx_agree_back >> strip_tac >>
      first_x_assum drule_all >> strip_tac >> simp[] >>
      strip_tac >> first_x_assum irule >>
      fs[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
  conj_tac
  >- (fs[taint_within_rq_upto_def] >> conj_tac >>
      rpt gen_tac >> strip_tac >>
      drule_all frame_reachable_ctx_agree_back >> strip_tac >>
      metis_tac[]) >>
  rpt strip_tac >>
  `raw_reachable vs C fn inst s` by metis_tac[raw_reachable_ctx_agree, ctx_agree_sym] >>
  metis_tac[raw_mem_ok_ctx_free, dload_offset_ok_ctx_free]
QED

Theorem ctx_rq_upto_ctx_agree:
  ctx_agree R C C' /\ C'.ctx_entry = C.ctx_entry /\
  (!entry. C.ctx_entry = SOME entry ==> R entry) ==>
  ctx_rq_upto D k C C' vs vs
Proof
  simp[ctx_rq_upto_def] >> rpt strip_tac >>
  qexistsl_tac [`fn'`, `inst'`, `t'`] >>
  metis_tac[raw_reachable_ctx_agree, ctx_agree_sym, request_agree_except_refl]
QED

Theorem prune_raw_safe_rq_upto:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  raw_safe_rq_upto D lo k unit.cu_context vs ==>
  raw_safe_rq_upto D lo k (prune_unit_fcg_unreachable unit fcg).cu_context vs /\
  ctx_rq_upto D k unit.cu_context (prune_unit_fcg_unreachable unit fcg).cu_context vs vs
Proof
  strip_tac >> gvs[] >>
  `ctx_wf unit.cu_context /\ wf_invoke_targets unit.cu_context` by
    metis_tac[o1_ctx_shape_wf] >>
  `ctx_agree (fcg_is_reachable (fcg_analyze unit.cu_context)) unit.cu_context
    (prune_unit_fcg_unreachable unit (fcg_analyze unit.cu_context)).cu_context` by
    (irule prune_unit_ctx_agree >> simp[]) >>
  `fcg_is_reachable (fcg_analyze unit.cu_context) entry` by metis_tac[fcg_analyze_entry_reachable] >>
  simp[prune_unit_fcg_unreachable_fields] >>
  conj_tac >- (irule raw_safe_rq_upto_ctx_agree >>
    qexistsl_tac [`unit.cu_context`, `fcg_is_reachable (fcg_analyze unit.cu_context)`] >>
    simp[prune_unit_fcg_unreachable_fields, MEM_prune_unit_fcg_unreachable_functions]) >>
  irule ctx_rq_upto_ctx_agree >> simp[prune_unit_fcg_unreachable_fields] >>
  qexists_tac `fcg_is_reachable (fcg_analyze unit.cu_context)` >> simp[]
QED

Theorem scfg_request_cut_raw_memory[local]:
  scfg_live_position_trace f i s g j t /\ scfg_data_agree s t /\
  raw_mem_ok C f i s /\ dload_offset_ok C f i s /\ inst_dload_in_section i s ==>
  raw_mem_ok C' g j t /\ dload_offset_ok C' g j t /\ inst_dload_in_section j t
Proof
  strip_tac >>
  `s.vs_alloca_next = t.vs_alloca_next /\ s.vs_fmp = t.vs_fmp /\
    s.vs_initial_fmp = t.vs_initial_fmp /\ s.vs_data_section = t.vs_data_section` by
    fs[scfg_data_agree_def, execution_frame_def, venom_state_component_equality] >>
  Cases_on `j.inst_opcode = JMP \/ j.inst_opcode = JNZ \/ j.inst_opcode = PHI`
  >- gvs[raw_mem_ok_def, inst_mem_ok_in_fn_def, inst_mem_below_frontiers_def,
         dalloca_no_wrap_def, dload_offset_ok_def, inst_dload_in_section_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `i = j` by metis_tac[scfg_live_position_trace_nonbranch] >>
  `!op. eval_operand op s = eval_operand op t` by
    metis_tac[scfg_data_agree_eval_operand] >>
  `inst_mem_below_frontiers j s <=> inst_mem_below_frontiers j t` by
    (simp[inst_mem_below_frontiers_def] >>
     metis_tac[scfg_data_agree_read_ranges, scfg_data_agree_write_ranges]) >>
  `in_revert_forward f s ==> in_revert_forward g t` by
    metis_tac[scfg_live_position_trace_revert] >>
  `scfg_payload s t` by metis_tac[scfg_data_agree_payload] >>
  `dload_offset_ok C' g j t` by
    metis_tac[scfg_payload_dload_offset_ok] >>
  fs[raw_mem_ok_def, inst_mem_ok_in_fn_def, GSYM in_revert_forward_def,
     dalloca_no_wrap_def, inst_dload_in_section_def] >>
  metis_tac[]
QED

Theorem simplify_cfg_stage_raw_safe_rq_upto:
  ctx_pass_stage rp (CFP_Simple VP_SimplifyCFG) view C C' /\
  o1_ctx_shape C /\ EVERY simplify_cfg_fn_ok C.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\ raw_safe_rq_upto D lo k C vs ==>
  raw_safe_rq_upto D lo k C' vs /\ ctx_rq_upto D k C C' vs vs
Proof
  strip_tac >>
  `C' = C with ctx_functions := MAP simplify_cfg_fn C.ctx_functions` by
    (drule simplify_cfg_stage_functions >> strip_tac >>
     fs[ctx_pass_stage_def, venom_context_component_equality]) >>
  `EVERY scfg_static C.ctx_functions /\ EVERY wf_function C.ctx_functions` by
    (fs[o1_ctx_shape_def, EVERY_MEM, simplifyCfgStaticInterfaceTheory.scfg_static_def] >>
     metis_tac[o1_fn_shape_def, simplifyCfgShapeCoreTheory.fn_shape_ok_scfg_shape]) >>
  `scfg_context_trace C C' /\ (ctx_has_dalloca C' ==> ctx_has_dalloca C)` by
    metis_tac[scfg_context_trace_simplify_cfg, scfg_simplify_cfg_no_dalloca] >>
  conj_tac >| [
    fs[raw_safe_rq_upto_def] >> rpt conj_tac
    >- (qpat_assum `ptr_discipline_rq_upto lo k C vs`
          (strip_assume_tac o REWRITE_RULE [ptr_discipline_rq_upto_def]) >>
        pure_rewrite_tac[ptr_discipline_rq_upto_def] >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac
        >- (qexists_tac `P` >> simp[EVERY_MAP, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
            gen_tac >> strip_tac >> irule simplify_cfg_fn_shape_ptr_ok >>
            fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
        metis_tac[scfg_request_cut_frame_rows])
    >- metis_tac[scfg_request_cut_taint] >>
    rpt strip_tac >> gvs[] >> drule_all scfg_request_cut_replay >> strip_tac >>
    rename1 `raw_reachable vs C _ _ source` >>
    `request_cut k source` by
      (fs[request_cut_def] >> metis_tac[]) >>
    metis_tac[scfg_request_cut_raw_memory],
    metis_tac[scfg_ctx_rq_upto]]
QED

Theorem request_cut_pre_walk:
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit sup0 =
    SOME (pre,sup') /\ o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok sup0 /\
  EVERY fn_defs_reach_uses unit.cu_context.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) unit.cu_context.ctx_functions /\
  pre.cu_context.ctx_entry = SOME entry /\
  C0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  dead_wf D /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  raw_safe_rq_upto D lo k unit.cu_context vs ==>
  raw_safe_rq_upto D lo k C0 vs /\ ctx_rq_upto D k unit.cu_context C0 vs vs
Proof
  strip_tac >> drule o1_pre_walk_runs >> strip_tac >>
  `o1_step_contract rp (CFP_Simple VP_SimplifyCFG)` by
    simp[o1_contract_simplify_cfg_pre_walk] >>
  drule_all mapped_pass_stage >> strip_tac >>
  `EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_no_phi >>
     simp[EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  drule_all simplify_cfg_stage_raw_safe_rq_upto >> strip_tac >>
  `o1_step_contract rp (CFP_Simple VP_DretDesugar)` by
    simp[o1_contract_dret_desugar_pre_walk] >>
  drule unit_labels_wf_namespace >> strip_tac >>
  `ctx_pass_stage rp (CFP_Simple VP_DretDesugar) any_view mid.cu_context pre.cu_context` by
    metis_tac[mapped_pass_stage] >>
  `pre.cu_context = mid.cu_context` by metis_tac[dret_desugar_stage_identity] >>
  `raw_safe_rq_upto D lo k C0 vs /\ ctx_rq_upto D k pre.cu_context C0 vs vs` by
    (qpat_x_assum `C0 = _` SUBST1_TAC >>
     irule prune_raw_safe_rq_upto >> metis_tac[]) >>
  metis_tac[ctx_rq_upto_trans]
QED
