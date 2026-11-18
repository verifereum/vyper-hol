Theory gasFocusPacketPipelineStages
Ancestors
  o1PipelineCorrect o1PipelineCompose o1ComposeSupport o1LabelFlowStaticContracts
  o1FnScheduleDecompHelpers o1DftStageSsa o1PassContract o1PassLift
  venomPassSchedule venomPipelineRunner venomFnScheduleRunner venomPassDispatcher
  fcgPruning irSupply venomWf list option

(* The packet edges and the indexed transport edges come from the same run. *)
Theorem focus_packet_pipeline_stages:
  o1PipelineCorrect$o1_pipeline rp unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  unit.cu_context.ctx_entry = SOME nm ==>
  ?pre t t' stage.
    run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit
      (init_ir_supply unit) = SOME (pre,t) /\
    pre.cu_context.ctx_entry = SOME nm /\
    run_callee_first rp o1_fn_passes (fcg_postorder (fcg_analyze pre.cu_context) nm)
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
      SOME (out.po_unit,t') /\
    stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
    stage 9 = out.po_unit.cu_context /\
    (!k. k < 9 ==> ctx_pass_stage rp (EL k o1_fn_passes) (o1_walk_view rp k)
      (stage k) (stage (SUC k))) /\
    (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
      EVERY (o1_fn_row k) (stage k).ctx_functions) /\
    (stage 7).ctx_entry = SOME nm /\
    ctx_pass_stage rp (CFP_Simple VP_DFT) any_view (stage 7) (stage 8) /\
    ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) any_view (stage 8) (stage 9) /\
    o1_pre 7 (stage 7) (stage 8) /\
    o1_ctx_shape (stage 7) /\ o1_ctx_shape (stage 8) /\ o1_ctx_shape (stage 9) /\
    EVERY wf_ssa (stage 7).ctx_functions /\ EVERY wf_ssa (stage 8).ctx_functions
Proof
  strip_tac >> fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  drule o1_driver_runs >> strip_tac >>
  rename1 `run_pipeline_stages _ _ _ _ = SOME (pre,t)` >>
  rename1 `run_callee_first _ _ _ _ _ = SOME (_,t')` >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)` by simp[init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  `o1_ctx_shape (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
   ALL_DISTINCT (unit_label_namespace
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)))` by
    metis_tac[o1_ctx_shape_prune, unit_labels_wf_namespace] >>
  `entry = nm` by metis_tac[SOME_11] >> pop_assum SUBST_ALL_TAC >>
  drule_all (SRULE [] (Q.INST [`unit` |-> `pre`, `fcg` |-> `fcg_analyze pre.cu_context`]
    o1_walk_callee_first)) >> strip_tac >>
  fs[run_callee_first_def] >>
  drule_at (Pos (el 3)) (Q.INST [`R` |-> `o1_fn_row`] o1_schedule_stages) >>
  (impl_tac >- fs[o1_fn_passes_steps, o1_step_contracts_from_rows, o1_prune_every]) >>
  strip_tac >>
  `LENGTH o1_fn_passes = 9` by simp[o1_fn_passes_def] >>
  qpat_assum `stage (LENGTH _) = _`
    (assume_tac o SRULE [o1_fn_passes_def]) >>
  qpat_assum `!k. k <= LENGTH _ ==> _` (fn th =>
    map_every (fn k => qspec_then k (strip_assume_tac o SRULE [o1_fn_passes_def]) th)
      [`7`, `8`, `9`]) >>
  qpat_assum `!k. k < LENGTH _ ==> _` (fn th =>
    map_every (fn k => qspec_then k (strip_assume_tac o SRULE [o1_fn_passes_def]) th)
      [`7`, `8`]) >>
  `o1_pre 7 (stage 7) (stage 8)` by simp[o1_pre_def] >>
  `EVERY wf_ssa (stage 7).ctx_functions` by
    (qpat_assum `EVERY (o1_fn_row 7) _`
       (mp_tac o SRULE [EVERY_MEM, o1_fn_row_def]) >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all (Q.INST [`C` |-> `stage 7`, `C'` |-> `stage 8`, `view` |-> `any_view`]
    dft_stage_wf_ssa) >> strip_tac >>
  qpat_assum `!k. k <= LENGTH _ ==> _`
    (assume_tac o SRULE [o1_fn_passes_def]) >>
  qexists `stage` >>
  simp[prune_unit_fcg_unreachable_fields] >>
  rpt strip_tac >>
  qpat_assum `!k. k < LENGTH _ ==> _` (qspec_then `k` mp_tac) >>
  simp[o1_walk_view_def]
QED
