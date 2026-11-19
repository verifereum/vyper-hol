Theory requestCutSourceRecording
Ancestors
  requestCutSimplifyCfg
  o1ContractSimplifyCfg o1DretDesugarContract o1ComposeSupport o1ContractTheorems
  o1PassContract irSupply ctxLookupAgree
  fcgPruning unitTransformDefs unitShapeDefs venomExecSemantics venomWf venomState
  list finite_map

Theorem request_cut_pre_walk_recording:
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit sup0 =
    SOME (pre,sup') /\ o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok sup0 /\
  EVERY fn_defs_reach_uses unit.cu_context.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) unit.cu_context.ctx_functions /\
  pre.cu_context.ctx_entry = SOME entry /\
  C0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  raw_reachable vs C0 g i t /\ i.inst_opcode <> INVOKE /\
  step_inst fuel C0 i t = OK t' /\ LENGTH t.vs_requests < LENGTH t'.vs_requests ==>
  ?f s s'. raw_reachable vs unit.cu_context f i s /\
    step_inst fuel unit.cu_context i s = OK s' /\
    s.vs_requests = t.vs_requests /\ s.vs_outcomes = t.vs_outcomes /\
    s'.vs_requests = t'.vs_requests
Proof
  strip_tac >> drule o1_pre_walk_runs >> strip_tac >>
  `o1_step_contract rp (CFP_Simple VP_SimplifyCFG)` by
    simp[o1_contract_simplify_cfg_pre_walk] >>
  drule_all mapped_pass_stage >> strip_tac >>
  `o1_step_contract rp (CFP_Simple VP_DretDesugar)` by
    simp[o1_contract_dret_desugar_pre_walk] >>
  drule unit_labels_wf_namespace >> strip_tac >>
  `ctx_pass_stage rp (CFP_Simple VP_DretDesugar) any_view mid.cu_context pre.cu_context` by
    metis_tac[mapped_pass_stage] >>
  `pre.cu_context = mid.cu_context` by metis_tac[dret_desugar_stage_identity] >>
  `ctx_wf pre.cu_context /\ wf_invoke_targets pre.cu_context` by
    metis_tac[o1_ctx_shape_wf] >>
  `ctx_agree (fcg_is_reachable (fcg_analyze pre.cu_context)) pre.cu_context C0` by
    (qpat_assum `C0 = _` SUBST1_TAC >> irule prune_unit_ctx_agree >> simp[]) >>
  `C0.ctx_entry = pre.cu_context.ctx_entry` by
    simp[prune_unit_fcg_unreachable_fields] >>
  `fcg_is_reachable (fcg_analyze pre.cu_context) entry` by
    metis_tac[fcg_analyze_entry_reachable] >>
  `raw_reachable vs pre.cu_context g i t` by
    (mp_tac (Q.SPECL [`fcg_is_reachable (fcg_analyze pre.cu_context)`,
       `C0`, `pre.cu_context`, `vs`] raw_reachable_ctx_agree) >>
     (impl_tac >- (simp[] >> metis_tac[ctx_agree_sym])) >>
     disch_then (mp_tac o Q.SPECL [`g`, `i`, `t`]) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC) >>
  `raw_reachable vs mid.cu_context g i t` by metis_tac[] >>
  `step_inst fuel mid.cu_context i t = OK t'` by
    (qpat_assum `step_inst fuel C0 i t = OK t'` mp_tac >>
     qpat_assum `i.inst_opcode <> INVOKE` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >> simp[step_inst_non_invoke]) >>
  `EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_no_phi >>
     simp[EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  drule_all (Q.INST [`C` |-> `unit.cu_context`, `CT` |-> `mid.cu_context`]
    simplify_cfg_stage_recording_step) >>
  simp[]
QED
