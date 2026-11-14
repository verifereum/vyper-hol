Theory o1CodeEndScheduleRetention
Ancestors
  o1PassContract o1PipelineCompose o1ComposeSupport o1ScheduleDecomp o1PartialSchedule
  o1FnScheduleDecomp o1FnScheduleDecompHelpers venomFnScheduleRunner
  venomFnScheduleRunnerProps list rich_list o1ScheduleDecompHelpers
  venomPassSchedule venomPipelineRunner venomInst irSupply venomCompilerWf venomWf unitShapeDefs fcgDefs

Theorem retained_decomp[local]:
  rows_step_contracts_from o1_fn_row rp 0 passes /\
  EVERY (o1_fn_row 0) u.cu_context.ctx_functions /\
  run_named_fn_schedules execute_configured_fn_pass rp passes names u s = SOME (u',s') /\
  o1_ctx_shape u.cu_context /\ ALL_DISTINCT (unit_label_namespace u) /\ ALL_DISTINCT names /\
  (!n. MEM n names <=> MEM n (ctx_fn_names u.cu_context)) /\ ir_supply_inst_ok s ==>
  ?chains. LENGTH chains = LENGTH u.cu_context.ctx_functions /\
    (!i. i < LENGTH chains ==> chain_facts o1_fn_row rp passes u names chains i) /\
    u'.cu_context = stage_ctx u.cu_context chains (LENGTH passes) /\ chains_ids_apart chains /\
    (!j. j < LENGTH chains ==> EVERY (\u. EVERY fmp_sig_no_param u.cu_context.ctx_functions) (SND (EL j chains)))
Proof
  strip_tac >>
  `partial_schedule o1_fn_row rp passes u names [] (MAP (\f. ([f],[])) u.cu_context.ctx_functions) u` by
    (irule partial_schedule_initial >> simp[]) >>
  drule_at (Pat `partial_schedule _ _ _ _ _ _ _ _`) (Q.INST [`P` |-> `fmp_sig_no_param`] partial_schedule_suffix_observations) >>
  disch_then (drule_at (Pat `run_named_fn_schedules _ _ _ _ _ _ = _`)) >>
  simp[] >> impl_tac >- simp[chains_ids_used_def, EL_MAP, o1_fn_row_def] >>
  disch_then (qx_choose_then `chains` strip_assume_tac) >> qexists_tac `chains` >>
  drule partial_schedule_exhausted >> simp[] >> strip_tac >>
  drule partial_schedule_final_context >> simp[] >> strip_tac >> gvs[partial_schedule_def]
QED

Theorem retained_stage[local]:
  LENGTH chains = LENGTH u.cu_context.ctx_functions /\
  o1_ctx_shape u.cu_context /\
  (!i. i < LENGTH chains ==> chain_facts o1_fn_row rp passes u names chains i) /\
  callee_first names u.cu_context.ctx_functions /\ k < LENGTH passes /\
  (!j. j < LENGTH chains ==> EVERY (\u. EVERY fmp_sig_no_param u.cu_context.ctx_functions) (SND (EL j chains))) ==>
  ctx_pass_stage rp (EL k passes)
    (\C' f observed. walk_view rp (DROP (SUC k) passes) C' f observed /\
      EVERY fmp_sig_no_param observed.cu_context.ctx_functions)
    (stage_ctx u.cu_context chains k) (stage_ctx u.cu_context chains (SUC k))
Proof
  strip_tac >> `k <= LENGTH passes` by simp[] >>
  irule ctx_pass_stage_indexed >> simp[stage_ctx_def, stage_fns_def] >>
  qx_gen_tac `i` >> strip_tac >> simp[EL_MAP] >>
  `chain_facts o1_fn_row rp passes u names chains i` by simp[] >>
  drule chain_facts_step >> disch_then (qspec_then `k` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `s` (qx_choose_then `out` strip_assume_tac)) >>
  qexistsl_tac [`EL k (SND (EL i chains))`,`s`,`out`] >> simp[] >>
  `ctx_fn_names (stage_ctx u.cu_context chains k) = ctx_fn_names u.cu_context` by
    (irule stage_ctx_names >> metis_tac[]) >>
  `walk_view rp (DROP (SUC k) passes) (stage_ctx u.cu_context chains (SUC k))
    (EL k (FST (EL i chains))) (EL k (SND (EL i chains)))` by
    (irule chain_facts_walk_view >> metis_tac[]) >>
  `EVERY fmp_sig_no_param (EL k (SND (EL i chains))).cu_context.ctx_functions` by
    (drule chain_facts_length >> strip_tac >> fs[EVERY_EL]) >>
  gvs[stage_ctx_def, stage_fns_def, chain_facts_def] >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[]
QED

Theorem o1_code_end_named_schedules_stages:
  !rp names u s u' s'.
  run_named_fn_schedules execute_configured_fn_pass rp o1_fn_passes names u s = SOME (u',s') /\
  o1_ctx_shape u.cu_context /\ ALL_DISTINCT (unit_label_namespace u) /\ ALL_DISTINCT names /\
  (!n. MEM n names <=> MEM n (ctx_fn_names u.cu_context)) /\ ir_supply_inst_ok s /\
  EVERY (o1_fn_row 0) u.cu_context.ctx_functions /\ callee_first names u.cu_context.ctx_functions ==>
  ?stage. stage 0 = u.cu_context /\ stage (LENGTH o1_fn_passes) = u'.cu_context /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k) /\
    (stage k).ctx_entry = u.cu_context.ctx_entry /\
    (stage k).ctx_global_reserved = u.cu_context.ctx_global_reserved /\
    ctx_fn_names (stage k) = ctx_fn_names u.cu_context /\ EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  (!k. k < LENGTH o1_fn_passes ==> ctx_pass_stage rp (EL k o1_fn_passes)
    (o1_walk_view rp k) (stage k) (stage (SUC k))) /\
  ctx_pass_stage rp (EL 3 o1_fn_passes)
    (\C' f observed. o1_walk_view rp 3 C' f observed /\ EVERY fmp_sig_no_param observed.cu_context.ctx_functions)
    (stage 3) (stage 4)
Proof
  rpt strip_tac >>
  `rows_step_contracts_from o1_fn_row rp 0 o1_fn_passes` by
    simp[o1_fn_passes_steps, o1_step_contracts_from_rows] >>
  drule_all retained_decomp >> disch_then (qx_choose_then `chains` strip_assume_tac) >>
  qexists_tac `stage_ctx u.cu_context chains` >>
  conj_tac >- (irule chain_facts_zero >> metis_tac[]) >>
  conj_tac >- simp[] >> conj_tac
  >- (qx_gen_tac `k` >> disch_tac >>
      `EVERY (o1_fn_row k) (stage_ctx u.cu_context chains k).ctx_functions` by
        (irule stage_ctx_rows >> metis_tac[]) >>
      drule_all chain_facts_stage_shape >> strip_tac >> fs[stage_ctx_def]) >>
  conj_tac
  >- (qx_gen_tac `k` >> disch_tac >> drule_all chain_facts_stages >> simp[o1_walk_view_def]) >>
  simp[o1_walk_view_def] >>
  irule (retained_stage |> SPEC_ALL |> Q.INST [`k` |-> `3`] |> SIMP_RULE (srw_ss()) []) >>
  simp[] >> conj_tac >- simp[o1_fn_passes_def] >> qexists_tac `names` >> simp[]
QED
