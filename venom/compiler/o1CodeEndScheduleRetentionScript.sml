Theory o1CodeEndScheduleRetention
Ancestors
  o1PassContract o1PipelineCompose o1ComposeSupport o1ScheduleDecomp o1PartialSchedule
  o1FnScheduleDecomp o1FnScheduleDecompHelpers venomFnScheduleRunner
  venomFnScheduleRunnerProps list rich_list o1ScheduleDecompHelpers
  venomPassSchedule venomPipelineRunner venomInst irSupply venomCompilerWf venomWf unitShapeDefs fcgDefs

Theorem observed_rows_no_param[local]:
  observed = unit_with_fns unit
    (replace_fn name fn unit.cu_context.ctx_functions) /\
  EVERY (\g. ?j. o1_fn_row j g) unit.cu_context.ctx_functions /\
  o1_fn_row k fn ==>
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions
Proof
  strip_tac >> gvs[unit_with_fns_def, replace_fn_def, EVERY_MEM] >>
  rpt strip_tac >> drule MEM_MAP_replace_fn >> strip_tac >> gvs[] >>
  fs[o1_fn_row_def] >> metis_tac[]
QED

Theorem retained_step[local]:
  rows_step_contracts_from o1_fn_row rpolicy 0 passes /\
  EVERY (o1_fn_row 0) original.cu_context.ctx_functions /\
  partial_schedule o1_fn_row rpolicy passes original (done ++ n::todo) done chains current /\
  (!j. j < LENGTH chains ==> EVERY (\u. EVERY fmp_sig_no_param u.cu_context.ctx_functions) (SND (EL j chains))) /\
  ALL_DISTINCT (done ++ n::todo) /\
  (!name. MEM name (done ++ n::todo) <=> MEM name (ctx_fn_names original.cu_context)) /\
  ALL_DISTINCT (unit_label_namespace current) /\
  chains_ids_used original.cu_context done chains s /\
  run_configured_fn_passes execute_configured_fn_pass rpolicy passes n current s = SOME (next,s') /\
  ir_supply_inst_ok s ==>
  ?chains'. partial_schedule o1_fn_row rpolicy passes original (done ++ n::todo)
    (done ++ [n]) chains' next /\ unit_labels_wf next /\ ir_supply_inst_ok s' /\
    chains_ids_used original.cu_context (done ++ [n]) chains' s' /\
    (!j. j < LENGTH chains' ==> EVERY (\u. EVERY fmp_sig_no_param u.cu_context.ctx_functions) (SND (EL j chains')))
Proof
  strip_tac >>
  `o1_ctx_shape current.cu_context` by gvs[partial_schedule_def] >>
  `ir_supply_covers_unit s current` by
    (drule run_configured_fn_passes_success >> simp[]) >>
  `EVERY (\g. ?j. o1_fn_row j g) current.cu_context.ctx_functions` by
    metis_tac[partial_schedule_rows] >>
  `ALL_DISTINCT (ctx_fn_names original.cu_context)` by
    (drule partial_schedule_names >> strip_tac >>
     gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def]) >>
  `LENGTH chains = LENGTH original.cu_context.ctx_functions` by gvs[partial_schedule_def] >>
  `MEM n (ctx_fn_names original.cu_context)` by metis_tac[MEM_APPEND, MEM] >>
  `?i. i < LENGTH original.cu_context.ctx_functions /\
       (EL i original.cu_context.ctx_functions).fn_name = n` by
    (qpat_x_assum `MEM n (ctx_fn_names _)` mp_tac >>
     simp[ctx_fn_names_def, MEM_EL] >>
     disch_then (qx_choose_then `idx` strip_assume_tac) >>
     qexists_tac `idx` >> gvs[EL_MAP]) >>
  drule list_precedes_prefix >> strip_tac >>
  `lookup_unique_function n current.cu_context.ctx_functions =
     SOME (EL i original.cu_context.ctx_functions)` by
    (drule partial_schedule_pending_lookup >> disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  `!fn. lookup_unique_function n current.cu_context.ctx_functions = SOME fn ==> o1_fn_row 0 fn` by gvs[EVERY_EL] >>
  drule_all run_configured_fn_passes_decomp >> strip_tac >>
  `HD fs = EL i original.cu_context.ctx_functions` by metis_tac[optionTheory.SOME_11] >>
  `~MEM n done` by gvs[ALL_DISTINCT_APPEND] >>
  `chains_ids_apart (LUPDATE (fs,obs) i chains)` by
    (irule partial_schedule_new_apart >> simp[] >>
     qexistsl_tac [`o1_fn_row`,`current`,`done`,`done ++ n::todo`,`original`,`passes`,`rpolicy`,`s`] >>
     simp[] >> metis_tac[]) >>
  `EVERY (\u. EVERY fmp_sig_no_param u.cu_context.ctx_functions) obs` by
    (simp[Once EVERY_EL] >> qx_gen_tac `k` >> strip_tac >>
     drule fn_chain_length >> strip_tac >>
     irule observed_rows_no_param >> qexistsl_tac [`EL k fs`,`k`,`n`,`current`] >> simp[]) >>
  qexists_tac `LUPDATE (fs,obs) i chains` >> simp[] >> conj_tac
  >- (irule partial_schedule_extend >> metis_tac[]) >>
  reverse conj_tac
  >- (rpt strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]) >>
  rewrite_tac[chains_ids_used_def] >> qx_genl_tac [`j`,`f`,`id`] >> strip_tac >>
  Cases_on `j = i` >- (gvs[EL_LUPDATE] >> metis_tac[]) >>
  `j < LENGTH original.cu_context.ctx_functions` by metis_tac[LENGTH_LUPDATE] >>
  `(EL j original.cu_context.ctx_functions).fn_name <> (EL i original.cu_context.ctx_functions).fn_name` by
    (`((EL j original.cu_context.ctx_functions).fn_name = (EL i original.cu_context.ctx_functions).fn_name) <=> j = i` by
       (irule distinct_fn_name_index >> fs[ctx_fn_names_def]) >> simp[]) >>
  `MEM (EL j original.cu_context.ctx_functions).fn_name done` by
    (qpat_x_assum `MEM _ (done ++ _)` mp_tac >> simp[] >> metis_tac[]) >>
  qpat_x_assum `MEM f _` mp_tac >> simp[EL_LUPDATE] >> strip_tac >>
  qpat_x_assum `chains_ids_used _ _ _ _` mp_tac >>
  simp[chains_ids_used_def] >> disch_then drule_all >> fs[list_subset_def, EVERY_MEM]
QED

Theorem retained_suffix[local]:
  !todo done chains current s final sf order.
  rows_step_contracts_from o1_fn_row rpolicy 0 passes /\
  EVERY (o1_fn_row 0) original.cu_context.ctx_functions /\
  order = done ++ todo /\
  partial_schedule o1_fn_row rpolicy passes original order done chains current /\
  (!j. j < LENGTH chains ==> EVERY (\u. EVERY fmp_sig_no_param u.cu_context.ctx_functions) (SND (EL j chains))) /\
  ALL_DISTINCT order /\
  (!name. MEM name order <=> MEM name (ctx_fn_names original.cu_context)) /\
  ALL_DISTINCT (unit_label_namespace current) /\
  chains_ids_used original.cu_context done chains s /\
  run_named_fn_schedules execute_configured_fn_pass rpolicy passes todo current s = SOME (final,sf) /\ ir_supply_inst_ok s ==>
  ?chains'. partial_schedule o1_fn_row rpolicy passes original order order chains' final /\
    (!j. j < LENGTH chains' ==> EVERY (\u. EVERY fmp_sig_no_param u.cu_context.ctx_functions) (SND (EL j chains')))
Proof
  Induct
  >- (simp[run_named_fn_schedules_def] >> rpt strip_tac >> qexists_tac `chains` >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[Once run_named_fn_schedules_def, AllCaseEqs()] >>
  rename1 `run_configured_fn_passes _ _ _ h current s = SOME (mid,sm)` >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  `!name. MEM name (done ++ h::todo) <=> MEM name (ctx_fn_names original.cu_context)` by
    (simp[] >> metis_tac[]) >>
  drule_all retained_step >> disch_then (qx_choose_then `nextchains` strip_assume_tac) >>
  `ALL_DISTINCT (unit_label_namespace mid)` by gvs[unit_labels_wf_def] >>
  `partial_schedule o1_fn_row rpolicy passes original ((done ++ [h]) ++ todo) (done ++ [h]) nextchains mid` by
    (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> asm_rewrite_tac[]) >>
  `ALL_DISTINCT ((done ++ [h]) ++ todo)` by
    (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> asm_rewrite_tac[]) >>
  first_x_assum (drule_at (Pat `partial_schedule _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `run_named_fn_schedules _ _ _ _ _ _ = _`)) >>
  simp[APPEND_ASSOC]
QED

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
  drule_at (Pat `partial_schedule _ _ _ _ _ _ _ _`) retained_suffix >>
  disch_then (drule_at (Pat `run_named_fn_schedules _ _ _ _ _ _ = _`)) >>
  simp[] >> impl_tac >- simp[chains_ids_used_def, EL_MAP] >>
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
  drule_all retained_decomp >> strip_tac >>
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
