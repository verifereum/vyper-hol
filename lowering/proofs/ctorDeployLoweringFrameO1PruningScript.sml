(* The driver freezes fcg_analyze on pre_unit, after the fixed prewalk
   (venomPipelineDriverScript.sml:89-108), not on the original unit. *)
Theory ctorDeployLoweringFrameO1Pruning
Ancestors
  ctorDeployLoweringFrameO1Prewalk ctorDeployLoweringFramePruning
  venomFnScheduleRunner venomPassSchedule venomPipelineRunner
  venomInst list fcgPruning fcgDefs

Theorem unique_lookup_function[local]:
  !fns name fn. lookup_unique_function name fns = SOME fn ==>
    lookup_function name fns = SOME fn
Proof
  Induct >> rpt gen_tac >>
  simp[lookup_unique_function_def, lookup_function_def, FIND_thm] >>
  Cases_on `h.fn_name = name` >> simp[] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  rewrite_tac[GSYM lookup_function_def] >> first_x_assum irule >>
  simp[lookup_unique_function_def] >> metis_tac[]
QED

Theorem o1_prewalk_pruned_entry_call_free:
  lookup_unique_function entry u.cu_context.ctx_functions = SOME fn /\
  ALL_DISTINCT (MAP (\f. f.fn_name) u.cu_context.ctx_functions) /\
  EVERY (\i. ~MEM i.inst_opcode
    [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts fn) /\
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages u s = SOME (pre,ps) /\
  pre.cu_context.ctx_entry = SOME entry ==>
  ?fn'. (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context.ctx_functions = [fn'] /\
    EVERY (\i. ~MEM i.inst_opcode
      [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts fn')
Proof
  rpt strip_tac >> drule_all o1_prewalk_entry_call_free >> strip_tac >>
  drule o1_prewalk_function_names >> strip_tac >>
  drule unique_lookup_function >> strip_tac >>
  qexists `fn'` >> simp[] >> irule prune_no_invoke_entry_singleton >>
  gvs[EVERY_MEM] >> metis_tac[]
QED
