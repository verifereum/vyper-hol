(* Output-list agreement at a selected FmpLowering INVOKE, before return binding. *)
Theory gasFocusFmpCutInvokeOutputs
Ancestors
  fmpStageFmpStepsRetInvokeObserved fmpStageFmpStepsRetInvokeOrigin
  fmpStageFmpStepsCallAbi concretizeStageLookup fmpStepBridge
  concretizeAnalysisMetadataOwnership o1PassContract venomInst venomInstIdsProps

Theorem observed_callee_nonpublishing[local]:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C C' /\
  fmp_free_ctx C /\ o1_walk_view rp 3 C' fn observed /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  MEM name (fn_invoke_targets fn) /\
  lookup_function name observed.cu_context.ctx_functions = SOME g ==>
  !sig. g.fn_fmp_signature = SOME sig ==> ~sig.fms_publishes
Proof
  strip_tac >>
  `MEM name (ctx_fn_names observed.cu_context)` by
    (drule venomInstTheory.lookup_function_mem >> simp[NoAsms, ctx_fn_names_def]) >>
  `?src. lookup_function name C.ctx_functions = SOME src` by
    (Cases_on `lookup_function name C.ctx_functions` >>
     gvs[ctx_fn_names_def] >> metis_tac[lookup_function_not_mem]) >>
  drule_all fmp_return_stage_callee_signature >> strip_tac >>
  drule_all fmp_call_walk_signature >> strip_tac >> gvs[]
QED

Theorem focus_fmp_cut_invoke_outputs:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C C' /\
  fmp_free_ctx C /\ lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  MEM j (fn_insts fn') /\ j.inst_opcode = INVOKE /\ j.inst_id = inst.inst_id ==>
  j.inst_outputs = inst.inst_outputs
Proof
  strip_tac >> drule_all ctx_pass_stage_lookup >> strip_tac >> gvs[] >>
  drule fmp_fn_pass_step_result >> strip_tac >>
  `!i name args callee sig.
     MEM i (fn_insts fn) /\ i.inst_opcode = INVOKE /\
     i.inst_operands = Label name::args /\
     lookup_function name observed.cu_context.ctx_functions = SOME callee /\
     callee.fn_fmp_signature = SOME sig ==> ~sig.fms_publishes` by
    (rpt strip_tac >>
     `MEM name (fn_invoke_targets fn)` by
       (simp[invoke_target_instruction] >> metis_tac[]) >>
     drule_all observed_callee_nonpublishing >> simp[]) >>
  drule fmp_return_function_origin >> disch_then (qspec_then `j` mp_tac) >>
  simp[] >> strip_tac >> metis_tac[fn_inst_ids_distinct_inj]
QED
