(*
 * The arity of a source INVOKE under FmpLowering's stage context: its
 * arguments match the callee's user parameters.  FmpLowering checks the
 * arity against the callee it observes (fmp_resolve_invoke), which is the
 * C' callee taken through the passes after it; the walk view carries their
 * shape facts and rows, and each of those passes and FmpLowering itself
 * keep the user PARAM count.
 *
 * TOP-LEVEL:
 *   fmp_stage_invoke_arity  - LENGTH args = LENGTH (fn_user_param_insts callee)
 *)
Theory fmpStageCallArity
Ancestors
  fmpStageRel fmpStageOpBaseActual fmpStageCoverBackFmpArity fmpStepBridge
  fmpStepLayout fmpLowerDefs
  fmpLowerProps concretizeStageLookup o1MakeSsaRows o1ContractMakeSsaReplay
  o1ContractSimplifyCfg o1ContractSimplifyCfgParams o1ContractSue
  o1ContractSueStep o1DftStep o1ContractCfgNorm o1ContractCfgNormStep
  o1PassContract callLayoutDefs venomExecSemantics venomPassSchedule
  venomPassDispatcher venomFnScheduleRunner fcgDefs fcgBridge venomWf
  venomInst list

Theorem make_ssa_pass_user_param_count[local]:
  fn_pass_step rpolicy (CFP_Simple VP_MakeSSA) observed s fn out /\
  o1_fn_shape C fn ==>
  LENGTH (fn_user_param_insts out.fpo_function) =
    LENGTH (fn_user_param_insts fn)
Proof
  strip_tac >> drule make_ssa_pass_step_replay >> strip_tac >>
  drule_all make_ssa_step_user_param_count >> simp[]
QED

Theorem simplify_cfg_pass_user_param_count[local]:
  fn_pass_step rpolicy (CFP_Simple VP_SimplifyCFG) observed s fn out /\
  o1_fn_shape C fn /\ o1_fn_row 5 fn ==>
  LENGTH (fn_user_param_insts out.fpo_function) =
    LENGTH (fn_user_param_insts fn)
Proof
  strip_tac >> drule simplify_cfg_pass_step_function >> strip_tac >>
  gvs[o1_fn_row_def] >> irule simplify_cfg_fn_user_param_count >>
  metis_tac[]
QED

Theorem sue_pass_user_param_count[local]:
  fn_pass_step rpolicy (CFP_Simple VP_SingleUseExpansion) observed s fn out ==>
  LENGTH (fn_user_param_insts out.fpo_function) =
    LENGTH (fn_user_param_insts fn)
Proof
  strip_tac >> drule sue_pass_step_replay >> strip_tac >>
  drule sue_expand_function_supply_user_param_count >> simp[]
QED

Theorem dft_pass_user_param_count[local]:
  fn_pass_step rpolicy (CFP_Simple VP_DFT) observed s fn out /\
  o1_fn_shape C fn ==>
  LENGTH (fn_user_param_insts out.fpo_function) =
    LENGTH (fn_user_param_insts fn)
Proof
  strip_tac >>
  `out.fpo_function = dft_fn fn` by gvs[fn_pass_step_def] >>
  simp[] >> irule dft_fn_user_param_count >> metis_tac[]
QED

Theorem cfg_norm_pass_user_param_count[local]:
  fn_pass_step rpolicy (CFP_Simple VP_CFGNormalization) observed s fn out /\
  o1_fn_shape C fn /\ o1_fn_row 8 fn ==>
  LENGTH (fn_user_param_insts out.fpo_function) =
    LENGTH (fn_user_param_insts fn)
Proof
  strip_tac >> drule cfg_norm_pass_step_replay >> strip_tac >>
  irule cfg_norm_function_supply_user_param_count >>
  simp[supply_o1_inv_def] >> metis_tac[]
QED

(* The five passes after FmpLowering keep the user PARAM count. *)
Theorem o1_walk_suffix_user_param_count[local]:
  fn_steps_from (\m h. o1_fn_shape C h /\ o1_fn_row m h) rpolicy 4
    (DROP 4 o1_fn_passes) f g ==>
  LENGTH (fn_user_param_insts g) = LENGTH (fn_user_param_insts f)
Proof
  simp[o1_fn_passes_def, fn_steps_from_def] >> rpt strip_tac >> gvs[] >>
  imp_res_tac make_ssa_pass_user_param_count >>
  imp_res_tac simplify_cfg_pass_user_param_count >>
  imp_res_tac sue_pass_user_param_count >>
  imp_res_tac dft_pass_user_param_count >>
  imp_res_tac cfg_norm_pass_user_param_count >>
  gvs[]
QED

Theorem fmp_stage_invoke_arity:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ MEM fn C.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,args) /\
  lookup_function nm C.ctx_functions = SOME callee ==>
  LENGTH args = LENGTH (fn_user_param_insts callee)
Proof
  strip_tac >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
     (o1_walk_view rpolicy 3) C C'` by gvs[fmp_stage_ctx_def] >>
  `lookup_function fn.fn_name C.ctx_functions = SOME fn` by
    (irule fmp_lookup_function_self >>
     gvs[fmp_stage_ctx_def, o1_ctx_shape_def, ctx_wf_def,
         ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  `?fn' observed s out.
     lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
     fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) observed s fn out /\
     out.fpo_function = fn' /\ o1_walk_view rpolicy 3 C' fn observed` by
    metis_tac[ctx_pass_stage_lookup] >>
  `?callee' obs2 s2 out2.
     lookup_function nm C'.ctx_functions = SOME callee' /\
     fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) obs2 s2 callee out2 /\
     out2.fpo_function = callee'` by
    metis_tac[ctx_pass_stage_lookup] >>
  `fn.fn_fmp_signature = NONE` by metis_tac[fmp_stage_actual_witness] >>
  `?g. lookup_function nm observed.cu_context.ctx_functions = SOME g /\
       LENGTH args = LENGTH (fn_user_param_insts g)` by
    (qpat_x_assum `fn_pass_step _ _ observed _ fn _`
       (strip_assume_tac o MATCH_MP fmp_fn_pass_step_result) >>
     gvs[fmp_lower_function_def, AllCaseEqs(), decode_invoke_def] >>
     drule_all fmp_lower_invoke_user_arity >> metis_tac[]) >>
  `MEM nm (fn_invoke_targets fn)` by
    (simp[fn_invoke_targets_def, fcg_scan_function_def,
          mem_get_invoke_targets] >>
     gvs[decode_invoke_def, AllCaseEqs()] >> metis_tac[]) >>
  `LENGTH (fn_user_param_insts callee') =
     LENGTH (fn_user_param_insts callee)` by
    (drule fmp_fn_pass_step_result >> strip_tac >>
     drule fmp_lower_function_user_param_count >> gvs[]) >>
  gvs[o1_walk_view_def, walk_view_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  drule o1_walk_suffix_user_param_count >> simp[]
QED
