(* Identify the actual lowered function and pin any rooted lowering witness
   for that same function, without a dynamic stage invariant. *)
Theory gasFocusFmpStagePin
Ancestors
  fmpStageOpBaseRoot concretizeStageLookup ctxLookupAgreeHelpers
  fmpStageRel fmpStepBridge fmpStepLayout fmpStepSupply fmpLowerDefs
  fmpWfDefs venomInst venomWf venomFnScheduleRunner
  venomFnScheduleRunnerProps irSupply o1PassContract list

Theorem focus_fmp_selected_root_pin:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn ==>
  ?fn' infos0 ctx0 runner0.
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn' = fn_entry_label fn /\
    fmp_stage_lowered infos0 ctx0 runner0 fn fn' /\
    (fn_is_context_entry ctx0 fn <=> C.ctx_entry = SOME name) /\
    (!infos ctx runner rl rp.
      fmp_stage_lowered infos ctx runner fn fn' /\
      fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
      (fn_is_context_entry ctx fn <=> C.ctx_entry = SOME name) /\
      !j. MEM j (fn_insts fn) ==> ~MEM runner j.inst_outputs)
Proof
  strip_tac >>
  drule lookup_function_selected_name >> disch_then (SUBST_ALL_TAC o SYM) >>
  drule_all ctx_pass_stage_lookup >> strip_tac >>
  rename1 `fn_pass_step _ _ observed sp fn out` >>
  `ir_supply_covers_fn sp fn` by
    (irule ir_supply_covers_unit_member >> qexists `observed` >>
     gvs[fn_pass_step_def] >> metis_tac[lookup_unique_function_member]) >>
  `!j. MEM j (fn_insts fn) ==> ~MEM (FST (fresh_ir_var sp)) j.inst_outputs` by
    (qpat_x_assum `ir_supply_covers_fn sp fn` mp_tac >>
     simp[ir_supply_covers_fn_def, list_subset_def] >> strip_tac >>
     Cases_on `fresh_ir_var sp` >>
     drule_all fresh_ir_var_outside_function >> strip_tac >>
     simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[fn_ir_vars_member]) >>
  drule fmp_fn_pass_step_result >> strip_tac >>
  drule fmp_lower_function_preserves_entry_label >> strip_tac >>
  Cases_on `analyze_fmp_context observed.cu_context` >>
  gvs[fmp_lower_function_def] >>
  rename1 `analyze_fmp_context observed.cu_context = SOME infos0` >>
  rename1 `lookup_function _ C'.ctx_functions = SOME fn'` >>
  `fmp_stage_lowered infos0 observed.cu_context (FST (fresh_ir_var sp)) fn fn'` by
    (simp[fmp_stage_lowered_def] >> metis_tac[]) >>
  `fn_is_context_entry observed.cu_context fn <=> C.ctx_entry = SOME fn.fn_name` by
    simp[fn_is_context_entry_def] >>
  qexistsl [`infos0`, `observed.cu_context`, `FST (fresh_ir_var sp)`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  imp_res_tac fmp_stage_lowered_root_fingerprint >>
  Cases_on `fmp_stage_root infos0 observed.cu_context fn` >> gvs[] >>
  Cases_on `fn_is_context_entry ctx fn` >>
  Cases_on `fn_is_context_entry observed.cu_context fn` >> gvs[]
QED
