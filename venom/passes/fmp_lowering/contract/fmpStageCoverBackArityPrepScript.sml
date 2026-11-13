(* Static arity transport along the actual post-FMP suffix. *)
Theory fmpStageCoverBackArityPrep
Ancestors
  fmpStageCoverBackFmpArity fmpStageCoverBackLaterArity
  fmpStageCoverBackScfgShape fmpStageCoverBackScfgStructure fmpStageCoverBackCfgArity
  fmpStageOpBase fmpStageOpBaseActual fmpStageRel
  o1PassContract venomPassSchedule venomPassDispatcher concretizeStageLookup
  fmpStepBridge fmpLowerDefs fmpLowerProps callLayoutDefs venomInst venomWf
  simplifyCfgLabelProps simplifyCfgDefs dftCorrectness dftDefs
  venomFnScheduleRunner venomFnScheduleRunnerProps list arithmetic
  concretizeAnalysisMetadataOwnership fmpAnalysisProps

Theorem scfg_pass_distinct_labels[local]:
  fn_pass_step rp (CFP_Simple VP_SimplifyCFG) ob sp f out /\
  ALL_DISTINCT (fn_labels f) ==>
  ALL_DISTINCT (fn_labels out.fpo_function)
Proof
  strip_tac >> drule simplify_cfg_fn_with_labels_transition >>
  gvs[fn_pass_step_def, execute_configured_fn_pass_simplify_cfg, AllCaseEqs(),
      label_map_transition_def]
QED

Theorem dft_pass_labels[local]:
  fn_pass_step rp (CFP_Simple VP_DFT) ob sp f out ==>
  fn_labels out.fpo_function = fn_labels f
Proof
  rw[fn_pass_step_def] >> simp[fn_labels_def, dft_fn_labels_map]
QED

Theorem fmp_suffix_user_count_conditional[local]:
  (!rp ob sp f out.
    fn_pass_step rp (CFP_Simple VP_CFGNormalization) ob sp f out /\
    ALL_DISTINCT (fn_labels f) ==>
    LENGTH (fn_user_param_insts f) <= LENGTH (fn_user_param_insts out.fpo_function)) /\
  fmp_stage_lowered infos ctx runner source lowered /\ o1_fn_shape C source /\
  fn_steps rpolicy (DROP 4 o1_fn_passes) lowered observed ==>
  LENGTH (fn_user_param_insts lowered) <= LENGTH (fn_user_param_insts observed)
Proof
  simp[o1_fn_passes_def, fn_steps_def] >> strip_tac >>
  drule_all fmp_cover_back_scfg_input_shape >> strip_tac >>
  `ALL_DISTINCT (fn_labels lowered)` by
    (drule_all fmp_cover_back_lower_structure >> simp[]) >>
  drule_all fmp_make_ssa_user_count >> strip_tac >>
  drule_all scfg_user_param_count >> strip_tac >>
  drule_all fmp_sue_user_count >> strip_tac >>
  drule_all scfg_pass_distinct_labels >> strip_tac >>
  drule fmp_sue_labels >> strip_tac >> fs[] >>
  rename1 `fn_pass_step rpolicy (CFP_Simple VP_DFT) dob dsp df dout` >>
  `ALL_DISTINCT (fn_labels df)` by metis_tac[] >>
  drule_all fmp_dft_user_count >> strip_tac >>
  drule dft_pass_labels >> strip_tac >>
  `ALL_DISTINCT (fn_labels dout.fpo_function)` by metis_tac[] >>
  `LENGTH (fn_user_param_insts dout.fpo_function) <=
   LENGTH (fn_user_param_insts observed)` by
    (fs[] >> first_x_assum irule >> metis_tac[]) >>
  gvs[] >> decide_tac
QED

Theorem fmp_stage_source_invoke_user_arity_conditional:
  (!rp observed supply f out.
    fn_pass_step rp (CFP_Simple VP_CFGNormalization) observed supply f out /\
    ALL_DISTINCT (fn_labels f) ==>
    LENGTH (fn_user_param_insts f) <= LENGTH (fn_user_param_insts out.fpo_function)) /\
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label name::args /\
  lookup_function name C.ctx_functions = SOME callee ==>
  LENGTH (fn_user_param_insts callee) <= LENGTH args
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
     (o1_walk_view rpolicy 3) C C'` by gvs[fmp_stage_ctx_def] >>
  `lookup_function fn.fn_name C.ctx_functions = SOME fn` by
    (irule fmp_lookup_function_self >>
     gvs[fmp_stage_ctx_def, o1_ctx_shape_def, ctx_wf_def,
         ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  `?lowered ob sp out.
     lookup_function fn.fn_name C'.ctx_functions = SOME lowered /\
     fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) ob sp fn out /\
     out.fpo_function = lowered /\ o1_walk_view rpolicy 3 C' fn ob` by
    (drule_all ctx_pass_stage_lookup >> metis_tac[]) >>
  `?target. lookup_function name C'.ctx_functions = SOME target` by
    metis_tac[ctx_pass_stage_lookup] >>
  `MEM name (fn_invoke_targets fn)` by
    (simp[invoke_target_instruction] >> metis_tac[]) >>
  `?seen. lookup_function name ob.cu_context.ctx_functions = SOME seen /\
      fn_steps rpolicy (DROP 4 o1_fn_passes) target seen` by
    (gvs[o1_walk_view_def] >> drule_all walk_view_fn_steps >> metis_tac[]) >>
  `MEM callee C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `callee.fn_name = name` by metis_tac[lookup_function_name] >>
  `?ci cc cr. fmp_stage_lowered ci cc cr callee target` by
    metis_tac[fmp_stage_actual_witness] >>
  `o1_fn_shape C callee` by
    (gvs[fmp_stage_ctx_def, o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `LENGTH (fn_user_param_insts target) <= LENGTH (fn_user_param_insts seen)` by
    (irule fmp_suffix_user_count_conditional >> metis_tac[]) >>
  `LENGTH (fn_user_param_insts callee) <= LENGTH (fn_user_param_insts target)` by
    (gvs[fmp_stage_lowered_def] >> metis_tac[fmp_lower_user_param_count]) >>
  `LENGTH args = LENGTH (fn_user_param_insts seen)` by
    (drule fmp_fn_pass_step_result >> strip_tac >>
     gvs[fmp_lower_function_def, AllCaseEqs()] >>
     drule_all fmp_lower_invoke_user_arity >> strip_tac >> gvs[]) >>
  decide_tac
QED
