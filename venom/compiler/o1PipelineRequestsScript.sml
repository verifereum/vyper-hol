(*
 * S4's request companion: run_venom_pipeline_correct with ctx_abort_rq
 * added under the same chosen input state.  When the unoptimized run
 * aborts, the optimized run aborts with requests that are a prefix of the
 * unoptimized run's, each agreeing up to the dead bytes D.  The halt case
 * is already in ctx_sim (dead_result_rel).
 *
 * The composition mirrors o1PipelineCompose with ctx_sim paired with
 * ctx_abort_rq: the walk's run companions (o1RequestRuns and the
 * LowerDload, ConcretizeMemLoc and DFT companions), the two pre-walk runs,
 * and pruning, which leaves runs unchanged.
 *)
Theory o1PipelineRequests
Ancestors
  o1RequestContract o1RequestRuns o1LowerDloadRequests
  concretizeStageRequests dftRequestsGas o1PipelineCorrect o1PipelineCompose
  o1ComposeSupport o1PassContract o1ContractTheorems o1ScheduleDecomp
  o1FnScheduleDecompHelpers o1DretDesugarContract o1ContractSimplifyCfg
  o1ContractLowerDloadStage o1ContractConcretize o1ContractDft
  o1DftStageSsa dftContractGas
  ctxLookupAgree ptrDiscipline unitMemInv unitTransformDefs unitShapeDefs
  venomPipelineDriver venomPipelineRunner venomFnScheduleRunner
  venomPassSchedule venomPassDispatcher venomInst venomExecSemantics
  venomState fcgDefs fcgPruning fcgPostorder fcgAnalysisProps
  contextCodegenRel venomMemDefs list rich_list

(* ===== The three remaining walk runs ===== *)

Theorem lower_dload_run_rq:
  o1_run_rq_contract_gas rpolicy D 1
Proof
  rewrite_tac[o1_run_rq_contract_gas_def] >> irule o1_stage_contract_rq_lift >>
  reverse conj_tac >- metis_tac[lower_dload_run_contract, o1_run_contract_def] >>
  `EL 1 o1_fn_passes = CFP_Simple VP_LowerDload` by simp[o1_fn_passes_def] >>
  simp[o1_inv_def] >> rpt strip_tac >>
  metis_tac[lower_dload_stage_abort_rq]
QED

Theorem concretize_run_rq:
  o1_run_rq_contract_gas rpolicy D 2
Proof
  rewrite_tac[o1_run_rq_contract_gas_def] >> irule o1_stage_contract_rq_lift >>
  reverse conj_tac >- metis_tac[o1_contract_concretize_mem_loc, o1_run_contract_def] >>
  `EL 2 o1_fn_passes = CFP_Simple VP_ConcretizeMemLoc` by EVAL_TAC >>
  simp[] >> rpt gen_tac >> strip_tac >>
  gvs[o1_inv_def, o1_src_inv_def] >>
  `ctx_inst_ids_distinct C` by fs[o1_ctx_shape_def] >>
  `EVERY all_reachable C.ctx_functions /\
   EVERY fn_defs_reach_uses C.ctx_functions` by
    fs[EVERY_MEM, make_ssa_input_ok_def] >>
  irule concretize_stage_abort_rq >> simp[] >> metis_tac[]
QED

Theorem dft_stage_sim_rq_gas:
  ctx_pass_stage rpolicy (CFP_Simple VP_DFT) view C C' /\ o1_pre 7 C C' /\
  dead_wf D /\ o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  o1_run_state_ok vs' ==>
  ?vs. gas_variant vs vs' /\ ctx_sim D C C' vs vs' /\
       ctx_abort_rq D C C' vs vs' /\
       (o1_lowered_inv C vs ==> o1_lowered_inv C' vs')
Proof
  strip_tac >> drule_all dft_stage_fn_rel >> strip_tac >>
  drule ctx_pass_stage_dft >> strip_tac >>
  irule dft_ctx_sim_rq_gas >> simp[] >>
  irule dft_ctx_labels_bound >> gvs[o1_run_state_ok_def]
QED

Theorem dft_run_rq:
  o1_run_rq_contract_gas rpolicy D 7
Proof
  simp[o1_run_rq_contract_gas_def, o1_fn_passes_def,
       o1_stage_rq_contract_gas_def, o1_inv_def, o1_ssa_inv_def] >>
  rpt strip_tac >>
  Cases_on `EVERY wf_ssa C.ctx_functions`
  >- (drule_all dft_stage_sim_rq_gas >> strip_tac >>
      qexists_tac `vs` >> rw[] >> irule dft_stage_wf_ssa >> metis_tac[]) >>
  qexists_tac `vs'` >> simp[gas_variant_refl]
QED

Theorem o1_run_rq_contracts:
  k < LENGTH o1_fn_passes ==> o1_run_rq_contract_gas rp D k
Proof
  simp[o1_fn_passes_def] >> strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/
   k = 8` by decide_tac >>
  gvs[make_ssa_run_rq_1, lower_dload_run_rq, concretize_run_rq,
      fmp_lowering_run_rq, make_ssa_run_rq_2, simplify_cfg_run_rq,
      sue_run_rq, dft_run_rq, cfg_norm_run_rq]
QED

(* ===== Composition ===== *)

Theorem guarded_ctx_sim_rq_trans:
  dead_wf D /\
  (!b. o1_run_state_ok b ==>
    ?a. gas_variant a b /\
      (Inv A a ==> ctx_sim D A B a b /\ ctx_abort_rq D A B a b /\ Mid B b)) /\
  (!c. o1_run_state_ok c ==>
    ?b. gas_variant b c /\
      (Mid B b ==> ctx_sim D B C b c /\ ctx_abort_rq D B C b c /\ Post C c)) /\
  o1_run_state_ok c ==>
  ?a. gas_variant a c /\
    (Inv A a ==> ctx_sim D A C a c /\ ctx_abort_rq D A C a c /\ Post C c)
Proof
  strip_tac >>
  qpat_x_assum `!c. _` (qspec_then `c` mp_tac) >>
  simp[] >> strip_tac >>
  `o1_run_state_ok b` by metis_tac[gas_variant_run_state_ok] >>
  qpat_x_assum `!b. _` (qspec_then `b` mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `a` >> conj_tac
  >- metis_tac[gas_variant_trans] >>
  strip_tac >> metis_tac[ctx_sim_trans, ctx_abort_rq_trans]
QED

Theorem o1_walk_stages_rq:
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  dead_wf D /\ o1_run_state_ok vs_out ==>
  ?vs_in. gas_variant vs_in vs_out /\
    (o1_inv D 0 (stage 0) vs_in ==>
     ctx_sim D (stage 0) (stage (LENGTH o1_fn_passes)) vs_in vs_out /\
     ctx_abort_rq D (stage 0) (stage (LENGTH o1_fn_passes)) vs_in vs_out /\
     o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out)
Proof
  strip_tac >>
  `!k vs. k < LENGTH o1_fn_passes /\ o1_run_state_ok vs ==>
    ?vi. gas_variant vi vs /\
      (o1_inv D k (stage k) vi ==>
       ctx_sim D (stage k) (stage (SUC k)) vi vs /\
       ctx_abort_rq D (stage k) (stage (SUC k)) vi vs /\
       o1_inv D (SUC k) (stage (SUC k)) vs)` by
    (rpt gen_tac >> strip_tac >>
     `o1_run_rq_contract_gas rpolicy D k` by simp[o1_run_rq_contracts] >>
     fs[o1_run_rq_contract_gas_def, o1_stage_rq_contract_gas_def, o1_pre_def] >>
     `k <= LENGTH o1_fn_passes /\ SUC k <= LENGTH o1_fn_passes` by simp[] >>
     `EVERY (o1_fn_row k) (stage k).ctx_functions /\
      EVERY (o1_fn_row (SUC k)) (stage (SUC k)).ctx_functions` by simp[] >>
     first_x_assum (qspecl_then [`stage k`, `stage (SUC k)`, `vs`] mp_tac) >>
     simp[]) >>
  `LENGTH o1_fn_passes = 9` by simp[o1_fn_passes_def] >>
  gvs[] >>
  `!n. n < 9 ==> !vo. o1_run_state_ok vo ==>
    ?vi. gas_variant vi vo /\
      (o1_inv D 0 (stage 0) vi ==>
       ctx_sim D (stage 0) (stage (SUC n)) vi vo /\
       ctx_abort_rq D (stage 0) (stage (SUC n)) vi vo /\
       o1_inv D (SUC n) (stage (SUC n)) vo)` by
    (Induct
     >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
     rpt strip_tac >>
     irule guarded_ctx_sim_rq_trans >> simp[] >>
     qexistsl_tac [`stage (SUC n)`, `o1_inv D (SUC n)`] >>
     simp[]) >>
  first_x_assum (qspec_then `8` mp_tac) >> simp[]
QED

(* The two pre-walk runs: SimplifyCFG is a bisimulation, DretDesugar the
   identity. *)
Theorem o1_pre_walk_rq:
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit s =
    SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s ==>
  !D vs. o1_run_state_ok vs /\ o1_pre_walk_inv D unit.cu_context vs ==>
         ctx_abort_rq D unit.cu_context unit'.cu_context vs vs
Proof
  strip_tac >> drule o1_pre_walk_runs >> strip_tac >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_SimplifyCFG`,
                  `u` |-> `unit`, `u'` |-> `mid`, `s'` |-> `t`]
            mapped_pass_stage) >>
  impl_tac >- simp[o1_contract_simplify_cfg_pre_walk] >> strip_tac >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_DretDesugar`,
                  `u` |-> `mid`, `s` |-> `t`, `u'` |-> `unit'`]
            mapped_pass_stage) >>
  impl_tac
  >- simp[o1_contract_dret_desugar_pre_walk, unit_labels_wf_namespace] >>
  strip_tac >>
  `unit'.cu_context = mid.cu_context` by metis_tac[dret_desugar_stage_identity] >>
  rpt strip_tac >> simp[] >>
  irule simplify_cfg_pre_walk_abort_rq >> metis_tac[]
QED

Theorem o1_walk_rq:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  reachable_fcg_acyclic unit.cu_context fcg /\
  ALL_DISTINCT (unit_label_namespace unit) /\
  run_callee_first rpolicy o1_fn_passes (fcg_postorder fcg entry)
    (prune_unit_fcg_unreachable unit fcg) s = SOME (unit', s') /\
  ir_supply_inst_ok s /\ EVERY (o1_fn_row 0) unit.cu_context.ctx_functions /\
  dead_wf D /\ o1_run_state_ok vs_out ==>
    ?vs_in. gas_variant vs_in vs_out /\
      (o1_walk_src_inv D (prune_unit_fcg_unreachable unit fcg).cu_context vs_in ==>
       ctx_sim D (prune_unit_fcg_unreachable unit fcg).cu_context
               unit'.cu_context vs_in vs_out /\
       ctx_abort_rq D (prune_unit_fcg_unreachable unit fcg).cu_context
               unit'.cu_context vs_in vs_out /\
       o1_lowered_inv unit'.cu_context vs_out)
Proof
  strip_tac >> drule_all o1_ctx_shape_prune >> strip_tac >>
  drule_all o1_walk_callee_first >> strip_tac >>
  fs[run_callee_first_def] >>
  drule_at (Pos (el 3)) (Q.INST [`R` |-> `o1_fn_row`] o1_schedule_stages) >>
  impl_tac
  >- fs[o1_fn_passes_steps, o1_step_contracts_from_rows, o1_prune_every] >>
  strip_tac >>
  `?names. callee_first names (stage 0).ctx_functions` by
    (qexists_tac `fcg_postorder fcg entry` >> gvs[]) >>
  `(!C vs. o1_inv D 0 C vs <=>
           o1_walk_src_inv D C vs /\ ?names. callee_first names C.ctx_functions) /\
   o1_inv D (LENGTH o1_fn_passes) = o1_lowered_inv` by
    simp[o1_inv_def, o1_fn_passes_def] >>
  `?vi. gas_variant vi vs_out /\
    (o1_inv D 0 (stage 0) vi ==>
     ctx_sim D (stage 0) (stage (LENGTH o1_fn_passes)) vi vs_out /\
     ctx_abort_rq D (stage 0) (stage (LENGTH o1_fn_passes)) vi vs_out /\
     o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out)` by
    (irule o1_walk_stages_rq >> fs[] >> qexists_tac `rpolicy` >>
     rpt strip_tac >> first_x_assum drule >> simp[o1_walk_view_def]) >>
  gvs[] >> metis_tac[]
QED

(* ===== The pipeline ===== *)

Theorem o1_pipeline_rq_facts:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy o1_pipeline_spec unit =
    SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit ==>
  !D vs_out. dead_wf D /\ o1_run_state_ok vs_out ==>
    ?vs_in. gas_variant vs_in vs_out /\
      (o1_pre_walk_inv D unit.cu_context vs_in ==>
       ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       ctx_abort_rq D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       o1_lowered_inv out.po_unit.cu_context vs_out)
Proof
  strip_tac >> drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)`
    by simp[irSupplyTheory.init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  `!D vs. o1_run_state_ok vs /\ o1_pre_walk_inv D unit.cu_context vs ==>
          ctx_abort_rq D unit.cu_context pre.cu_context vs vs` by
    (rpt strip_tac >> irule o1_pre_walk_rq >> metis_tac[]) >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 6)) o1_walk_rq >>
  disch_then (qspecl_then [`vs_out`, `D`] mp_tac) >> impl_tac
  >- (gvs[] >> metis_tac[unit_labels_wf_namespace]) >>
  disch_then (qx_choose_then `vs` strip_assume_tac) >>
  qexists_tac `vs` >> simp[] >> strip_tac >>
  `o1_run_state_ok vs` by metis_tac[gas_variant_run_state_ok] >>
  `ctx_sim D unit.cu_context pre.cu_context vs vs /\
   ctx_abort_rq D unit.cu_context pre.cu_context vs vs /\
   o1_walk_src_inv D pre.cu_context vs` by metis_tac[ctx_sim_fuel_imp_ctx_sim] >>
  `(!fuel vs. run_context fuel pre.cu_context vs =
      run_context fuel (prune_unit_fcg_unreachable pre
        (fcg_analyze pre.cu_context)).cu_context vs) /\
   !vs. mem_inv raw_mem_ok pre.cu_context vs ==>
     mem_inv raw_mem_ok (prune_unit_fcg_unreachable pre
       (fcg_analyze pre.cu_context)).cu_context vs` by
    (irule o1_prune_sim >> metis_tac[raw_mem_ok_ctx_free]) >>
  `o1_walk_src_inv D (prune_unit_fcg_unreachable pre
                        (fcg_analyze pre.cu_context)).cu_context vs` by
    (qpat_x_assum `o1_walk_src_inv D pre.cu_context vs` mp_tac >>
     rewrite_tac[o1_walk_src_inv_def] >> strip_tac >> conj_tac
     >- (irule o1_src_inv_prune >> metis_tac[])
     >> conj_tac >> irule o1_prune_every >> first_assum ACCEPT_TAC) >>
  `ctx_sim D unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs` by
    (qpat_x_assum `ctx_sim D unit.cu_context pre.cu_context vs vs` mp_tac >>
     rewrite_tac[ctx_sim_def] >> metis_tac[]) >>
  `ctx_abort_rq D unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs` by
    (irule ctx_abort_rq_run_context_eq >> qexists_tac `pre.cu_context` >> simp[]) >>
  metis_tac[ctx_sim_trans, ctx_abort_rq_trans]
QED

(* S4's request companion: run_venom_pipeline_correct's premises and guard,
   with the abort companion added under the same chosen input state. *)
Theorem run_venom_pipeline_correct_requests:
  !D lo rpolicy unit out vs_out.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\ o1_run_state_ok vs_out /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context /\ dead_wf D
    ==>
    ?vs_in. gas_variant vs_in vs_out /\
      (raw_unit_memory_ok unit.cu_context vs_in /\
       ptr_discipline lo unit.cu_context vs_in /\
       taint_within D unit.cu_context vs_in /\
       mem_inv dload_offset_ok unit.cu_context vs_in /\
       mem_inv dload_headroom_ok unit.cu_context vs_in ==>
       ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       ctx_abort_rq D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       o1_lowered_inv out.po_unit.cu_context vs_out)
Proof
  rpt strip_tac >>
  `fmp_free_ctx unit.cu_context` by (irule source_fmp_free >> fs[]) >>
  `!vi. raw_unit_memory_ok unit.cu_context vi /\
        ptr_discipline lo unit.cu_context vi /\
        taint_within D unit.cu_context vi /\
        mem_inv dload_offset_ok unit.cu_context vi /\
        mem_inv dload_headroom_ok unit.cu_context vi ==>
        o1_pre_walk_inv D unit.cu_context vi` by
    (rpt strip_tac >>
     `o1_src_inv D unit.cu_context vi` by
       (fs[o1_src_inv_def, raw_unit_memory_ok_mem_inv,
           o1_source_unit_ok_no_dalloca] >> metis_tac[]) >>
     irule o1_source_pre_walk_inv >> simp[]) >>
  fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  mp_tac (Q.INST [`mem_ok` |-> `K T`, `calling_ok` |-> `K T`,
                  `post_ok` |-> `K T`] o1_pipeline_rq_facts) >>
  impl_tac >- fs[] >>
  disch_then (qspecl_then [`D`, `vs_out`] mp_tac) >> simp[] >> metis_tac[]
QED
