(* Fixed O1 prewalk preserves entry-local exclusion, not machine confinement. *)
Theory ctorDeployLoweringFrameO1Prewalk
Ancestors
  ctorDeployLoweringFrameRunner ctorDeployLoweringFrameDret
  ctorDeployLoweringFramePrewalk venomPassSchedule venomPassDispatcher
  venomPipelineRunner

Theorem configured_simplify_cfg_call_free[local]:
  execute_configured_fn_pass rp (CFP_Simple VP_SimplifyCFG) observed s fn = SOME out /\
  EVERY (\i. ~MEM i.inst_opcode
    [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts fn) ==>
  EVERY (\i. ~MEM i.inst_opcode
    [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts out.fpo_function)
Proof
  simp[execute_configured_fn_pass_simplify_cfg] >>
  Cases_on `simplify_cfg_fn_with_labels fn` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  mp_tac (Q.INST [`fn` |-> `fn`] simplify_cfg_entry_call_free) >> simp[]
QED

Theorem configured_dret_call_free[local]:
  execute_configured_fn_pass rp (CFP_Simple VP_DretDesugar) observed s fn = SOME out /\
  EVERY (\i. ~MEM i.inst_opcode
    [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts fn) ==>
  EVERY (\i. ~MEM i.inst_opcode
    [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts out.fpo_function)
Proof
  simp[execute_configured_fn_pass_dret] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  drule (GEN_ALL (SRULE [] dret_desugar_function_call_free)) >>
  disch_then drule >> simp[]
QED

Theorem mapped_simplify_cfg_call_free[local]:
  lookup_unique_function entry u.cu_context.ctx_functions = SOME fn /\
  EVERY (\i. ~MEM i.inst_opcode
    [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts fn) /\
  run_mapped_functions rp (CFP_Simple VP_SimplifyCFG) u s = SOME (u',s') ==>
  ?fn'. lookup_unique_function entry u'.cu_context.ctx_functions = SOME fn' /\
    EVERY (\i. ~MEM i.inst_opcode
      [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts fn')
Proof
  strip_tac >> irule (BETA_RULE (Q.INST [`P` |-> `\op. ~MEM op [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`]
    mapped_functions_opcode_lookup)) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> metis_tac[configured_simplify_cfg_call_free]
QED

Theorem mapped_dret_call_free[local]:
  lookup_unique_function entry u.cu_context.ctx_functions = SOME fn /\
  EVERY (\i. ~MEM i.inst_opcode
    [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts fn) /\
  run_mapped_functions rp (CFP_Simple VP_DretDesugar) u s = SOME (u',s') ==>
  ?fn'. lookup_unique_function entry u'.cu_context.ctx_functions = SOME fn' /\
    EVERY (\i. ~MEM i.inst_opcode
      [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts fn')
Proof
  strip_tac >> irule (BETA_RULE (Q.INST [`P` |-> `\op. ~MEM op [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`]
    mapped_functions_opcode_lookup)) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> metis_tac[configured_dret_call_free]
QED

Theorem o1_prewalk_entry_call_free:
  lookup_unique_function entry u.cu_context.ctx_functions = SOME fn /\
  EVERY (\i. ~MEM i.inst_opcode
    [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts fn) /\
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages u s = SOME (u',s') ==>
  ?fn'. lookup_unique_function entry u'.cu_context.ctx_functions = SOME fn' /\
    EVERY (\i. ~MEM i.inst_opcode
      [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts fn')
Proof
  rpt strip_tac >>
  gvs[o1_pipeline_spec_def, run_pipeline_stages_def, run_pipeline_stage_def,
      AllCaseEqs()] >>
  drule_all (SRULE [] mapped_simplify_cfg_call_free) >> strip_tac >>
  drule_all (SRULE [] mapped_dret_call_free) >> simp[]
QED

Theorem o1_prewalk_function_names:
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages u s = SOME (u',s') ==>
  MAP (\f. f.fn_name) u'.cu_context.ctx_functions =
  MAP (\f. f.fn_name) u.cu_context.ctx_functions
Proof
  rpt strip_tac >>
  gvs[o1_pipeline_spec_def, run_pipeline_stages_def, run_pipeline_stage_def,
      AllCaseEqs()] >>
  imp_res_tac mapped_functions_function_names >> simp[]
QED
