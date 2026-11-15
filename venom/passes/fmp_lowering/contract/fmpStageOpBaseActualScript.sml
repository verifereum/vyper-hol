(* Actual pass witness and source-output freshness. *)
Theory fmpStageOpBaseActual
Ancestors
  fmpStageRel fmpStepBridge fmpStepSupply concretizeStageLookup
  fmpLowerProps fmpLowerDefs venomInst venomFnScheduleRunner
  venomFnScheduleRunnerProps irSupply o1PassContract
  list venomWf fmpWfDefs

Theorem fmp_actual_runner_fresh[local]:
  ir_supply_covers_fn sp fn ==>
  !i. MEM i (fn_insts fn) ==> ~MEM (FST (fresh_ir_var sp)) i.inst_outputs
Proof
  simp[ir_supply_covers_fn_def, list_subset_def] >> strip_tac >>
  Cases_on `fresh_ir_var sp` >>
  drule_all fresh_ir_var_outside_function >> strip_tac >>
  simp[fn_insts_def, fn_insts_blocks_MEM] >>
  metis_tac[fn_ir_vars_member]
QED

Theorem fmp_actual_step_witness[local]:
  fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) observed sp fn out ==>
  ?infos runner.
    fmp_stage_lowered infos observed.cu_context runner fn out.fpo_function /\
    !i. MEM i (fn_insts fn) ==> ~MEM runner i.inst_outputs
Proof
  strip_tac >> drule fmp_fn_pass_step_result >> strip_tac >>
  `ir_supply_covers_fn sp fn` by
    (irule ir_supply_covers_unit_member >> qexists `observed` >>
     gvs[fn_pass_step_def] >>
     metis_tac[lookup_unique_function_member]) >>
  drule fmp_actual_runner_fresh >> strip_tac >>
  gvs[fmp_lower_function_def, AllCaseEqs()] >>
  qexistsl [`infos`, `FST (fresh_ir_var sp)`] >>
  simp[fmp_stage_lowered_def] >> metis_tac[]
QED

Theorem fmp_stage_actual_witness:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn /\
  ?infos0 ctx0 runner0.
    fmp_stage_lowered infos0 ctx0 runner0 fn fn' /\
    (fn_is_context_entry ctx0 fn <=> C.ctx_entry = SOME fn.fn_name) /\
    !i. MEM i (fn_insts fn) ==> ~MEM runner0 i.inst_outputs
Proof
  strip_tac >>
  `fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn` by
    (gvs[fmp_stage_ctx_def, o1_inv_def, o1_static_inv_def,
         fmp_free_ctx_def, EVERY_MEM] >> metis_tac[]) >>
  simp[] >>
  `lookup_function fn.fn_name C.ctx_functions = SOME fn` by
    (irule fmp_lookup_function_self >>
     gvs[fmp_stage_ctx_def, o1_ctx_shape_def, ctx_wf_def,
         ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
     (o1_walk_view rpolicy 3) C C'` by gvs[fmp_stage_ctx_def] >>
  drule_all ctx_pass_stage_lookup >> strip_tac >> gvs[] >>
  drule fmp_actual_step_witness >> strip_tac >>
  qexistsl [`infos`, `observed.cu_context`, `runner`] >>
  simp[fn_is_context_entry_def]
QED
