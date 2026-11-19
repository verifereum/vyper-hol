(* GAS is kept by FMP lowering, and neither cursor needs a restore at
   this point. Fetching the event does not require executing the GAS. *)
Theory gasFocusFmpGasPair
Ancestors
  fmpStageRel fmpStageControl o1PassContract fmpReclaimDefs fmpAnalysisDefs
  contextCodegenRel venomWf venomExecProofs venomExecSemantics venomInst
  venomState o1LowerDloadShared gasEvents finite_map pred_set list words

Theorem fmp_gas_pair_fetch[local]:
  wf_function fn /\ active_inst fn inst s /\ inst.inst_opcode = GAS /\
  fmp_frame_rel sm fmp0 raw0 eb elo lo restored fn fn' PG G tv s t ==>
  ?bb bb'.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    get_instruction bb' t.vs_inst_idx = SOME inst
Proof
  strip_tac >> fs[active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  fs[fmp_frame_rel_def] >>
  `~((s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn))` by
    (strip_tac >> drule_all fmp_stage_plan_point >>
     simp[fmp_is_reclaim_point_def, fmp_callee_info_def, fmp_invoke_target_def]) >>
  drule fmp_stage_kept_inst >>
  disch_then drule >> disch_then drule >>
  simp[pre_fmp_opcode_def] >>
  disch_then (qx_choose_then `target_bb` strip_assume_tac) >>
  qexists `target_bb` >> gvs[get_instruction_def]
QED

Theorem fmp_gas_pair_step[local]:
  s.vs_gas_readings = t.vs_gas_readings /\ inst.inst_opcode = GAS /\
  step_inst k C inst s = OK s1 ==>
  ?out x rs t1.
    inst.inst_outputs = [out] /\
    (x,rs) = (case s.vs_gas_readings of [] => (0w,[]) | h::tl => (h,tl)) /\
    s1 = update_var out x (s with vs_gas_readings := rs) /\
    t1 = update_var out x (t with vs_gas_readings := rs) /\
    (!k'. step_inst k' C' inst t = OK t1)
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  simp[exec_gas_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `s.vs_gas_readings`
  >- gvs[venom_state_component_equality, update_var_def] >>
  gvs[]
QED

Theorem focus_fmp_gas_pair:
  wf_function fn /\ active_inst fn inst s /\ inst.inst_opcode = GAS /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  ?bb bb'.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    get_instruction bb' t.vs_inst_idx = SOME inst /\
    fn'.fn_name = fn.fn_name /\
    (!k. gas_events_step k C fn.fn_name inst s = [(fn.fn_name,inst.inst_id)]) /\
    (!k'. gas_events_step k' C' fn'.fn_name inst t = [(fn.fn_name,inst.inst_id)]) /\
    (!k s1. step_inst k C inst s = OK s1 ==>
      ?out x rs t1.
        inst.inst_outputs = [out] /\
        (x,rs) = (case s.vs_gas_readings of [] => (0w,[]) | h::tl => (h,tl)) /\
        s1 = update_var out x (s with vs_gas_readings := rs) /\
        t1 = update_var out x (t with vs_gas_readings := rs) /\
        (!k'. step_inst k' C' inst t = OK t1))
Proof
  strip_tac >> fs[fmp_stage_rel_def] >>
  drule fmpAnalysisPropsTheory.lookup_function_name >> strip_tac >>
  drule_all fmp_gas_pair_fetch >>
  disch_then (qx_choose_then `bb` (qx_choose_then `bb'` strip_assume_tac)) >>
  qexistsl [`bb`, `bb'`] >> simp[gas_events_step_def] >>
  rpt strip_tac >>
  `s.vs_gas_readings = t.vs_gas_readings` by metis_tac[ld_shared_gas_readings] >>
  drule_all fmp_gas_pair_step >> simp[]
QED
