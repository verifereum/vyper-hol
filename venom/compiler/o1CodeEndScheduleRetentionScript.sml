Theory o1CodeEndScheduleRetention
Ancestors
  o1PassContract o1PipelineCompose o1LabelFlowStaticContracts o1ComposeSupport o1ScheduleDecomp o1PartialSchedule
  o1FnScheduleDecomp o1FnScheduleDecompHelpers venomFnScheduleRunner
  venomFnScheduleRunnerProps list rich_list o1ScheduleDecompHelpers
  venomPassSchedule venomPipelineRunner venomInst irSupply venomCompilerWf venomWf unitShapeDefs fcgDefs

Theorem o1_code_end_named_schedules_stages:
  !rp names u s u' s'.
  run_named_fn_schedules execute_configured_fn_pass rp o1_fn_passes names u s = SOME (u',s') /\
  o1_ctx_shape u.cu_context /\ ALL_DISTINCT (unit_label_namespace u) /\ ALL_DISTINCT names /\
  (!n. MEM n names <=> MEM n (ctx_fn_names u.cu_context)) /\ ir_supply_inst_ok s /\
  EVERY (o1_fn_row 0) u.cu_context.ctx_functions /\ callee_first names u.cu_context.ctx_functions /\
  EVERY no_raw_fmp_ops u.cu_context.ctx_functions /\
  EVERY fmp_sig_no_param u.cu_context.ctx_functions ==>
  ?stage. stage 0 = u.cu_context /\ stage (LENGTH o1_fn_passes) = u'.cu_context /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k) /\
    (stage k).ctx_entry = u.cu_context.ctx_entry /\
    (stage k).ctx_global_reserved = u.cu_context.ctx_global_reserved /\
    ctx_fn_names (stage k) = ctx_fn_names u.cu_context /\ EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  (!k. k <= 3 ==> EVERY no_raw_fmp_ops (stage k).ctx_functions) /\
  (!k. k < LENGTH o1_fn_passes ==> ctx_pass_stage rp (EL k o1_fn_passes)
    (o1_walk_view rp k) (stage k) (stage (SUC k))) /\
  ctx_pass_stage rp (EL 3 o1_fn_passes)
    (\C' f observed. o1_walk_view rp 3 C' f observed /\ EVERY fmp_sig_no_param observed.cu_context.ctx_functions)
    (stage 3) (stage 4)
Proof
  rpt strip_tac >>
  mp_tac (Q.INST [`R` |-> `\k f. o1_fn_row k f /\
      (k <= 3 ==> no_raw_fmp_ops f) /\ fmp_sig_no_param f`,
    `P` |-> `fmp_sig_no_param`,
    `passes` |-> `o1_fn_passes`] o1_schedule_stages_observations) >>
  simp[o1_fn_passes_guard_rows] >>
  (impl_tac >- fs[EVERY_MEM]) >>
  disch_then (qx_choose_then `stage` strip_assume_tac o CONJUNCT2 o CONJUNCT2) >>
  `!k C' f observed.
     walk_view (\k f. o1_fn_row k f /\
       (k <= 3 ==> no_raw_fmp_ops f) /\ fmp_sig_no_param f)
       rp (SUC k) (DROP (SUC k) o1_fn_passes) C' f observed ==>
     o1_walk_view rp k C' f observed` by
    (rw[o1_walk_view_def, walk_view_def] >> first_x_assum drule_all >>
     strip_tac >> goal_assum (drule_at Any) >>
     irule fn_steps_from_mono >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `stage` >> rpt conj_tac
  >- simp[]
  >- simp[]
  >- (rpt strip_tac >> fs[EVERY_MEM] >> metis_tac[])
  >- (rpt strip_tac >>
      `k <= LENGTH o1_fn_passes` by simp[o1_fn_passes_def] >>
      fs[EVERY_MEM] >> metis_tac[])
  >- (qx_gen_tac `k` >> disch_tac >>
      qpat_x_assum `!k. k < LENGTH _ ==> _` (qspec_then `k` mp_tac) >>
      simp[] >> strip_tac >>
      fs[ctx_pass_stage_def] >>
      irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `3 < LENGTH o1_fn_passes` by EVAL_TAC >>
  qpat_x_assum `!k. k < LENGTH _ ==> _` (qspec_then `3` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!k C' f observed. _` (qspec_then `3` assume_tac) >>
  fs[ctx_pass_stage_def] >>
  irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
