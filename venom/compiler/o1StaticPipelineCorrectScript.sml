(* The static pipeline reuses one walk input through both pre-walk stages. *)
Theory o1StaticPipelineCorrect
Ancestors
  o1CodeEndWalkCompose o1CodeEndSourceTransport o1CodeEndDftTransport
  o1DftStageSsa dftContractGas dftGasOracleFromList dftGasOracleToList dftGasOracleDefs
  o1StaticPipelineCompose o1PipelineCorrect o1LabelStages o1PipelineCompose
  o1LabelFlowStaticContracts
  o1DretDesugarContract o1ScheduleDecomp o1FnScheduleDecompHelpers
  o1ComposeSupport o1ContractSimplifyCfg o1PassContract o1RequestContract
  ctxLookupAgree ctxLookupAgreeHelpers venomPipelineDriver venomPipelineRunner
  venomFnScheduleRunner venomPassSchedule fcgDefs fcgAnalysisProps fcgBridge
  fcgPruning fcgPostorder ptrDiscipline rawReachableFmp unitTransformDefs
  unitShapeDefs unitMemInv irSupply stateEquivProps staticAbortDefs
  lowerDloadDefs venomState list rich_list codegenSymRel

Theorem o1_pre_walk_sim_static_abort[local]:
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit s =
    SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s ==>
  o1_ctx_shape unit'.cu_context /\ unit_labels_wf unit' /\
  ir_supply_inst_ok s' /\
  unit'.cu_context.ctx_entry = unit.cu_context.ctx_entry /\
  unit'.cu_context.ctx_global_reserved = unit.cu_context.ctx_global_reserved /\
  ctx_fn_names unit'.cu_context = ctx_fn_names unit.cu_context /\
  !D vs. dead_wf D /\ o1_initial_state_ok vs /\
    vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
    o1_pre_walk_inv D unit.cu_context vs ==>
    ctx_sim_fuel I D unit.cu_context unit'.cu_context vs vs /\
    ctx_abort_rq D unit.cu_context unit'.cu_context vs vs /\
    o1_walk_src_inv D unit'.cu_context vs
Proof
  strip_tac >> drule_all o1_pre_walk_sim >> strip_tac >> simp[] >>
  drule o1_pre_walk_runs >> strip_tac >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_SimplifyCFG`,
                  `u` |-> `unit`, `u'` |-> `mid`, `s'` |-> `t`]
            mapped_pass_stage) >>
  impl_tac >- simp[o1_contract_simplify_cfg_pre_walk] >> strip_tac >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_DretDesugar`,
                  `u` |-> `mid`, `s` |-> `t`, `u'` |-> `unit'`]
            mapped_pass_stage) >>
  impl_tac
  >- (simp[o1_contract_dret_desugar_pre_walk] >>
      metis_tac[unit_labels_wf_namespace]) >> strip_tac >>
  `unit'.cu_context = mid.cu_context` by
    metis_tac[dret_desugar_stage_identity] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `ctx_sim_fuel I D unit.cu_context mid.cu_context vs vs /\
   o1_walk_src_inv D mid.cu_context vs` by
    (mp_tac (Q.SPECL [`unit.cu_context`, `mid.cu_context`, `vs`]
       (Q.INST [`view` |-> `any_view`] o1_static_pre_walk_simplify_cfg)) >>
     simp[no_pre_def, pass_fuel_def]) >>
  simp[] >> irule ctx_bisim_ctx_abort_rq >>
  fs[o1_initial_state_ok_def] >>
  `EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions` by
    (gvs[o1_ctx_shape_def, o1_pre_walk_inv_def, EVERY_MEM] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_no_phi >>
     simp[EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  metis_tac[simplify_cfg_stage_bisim]
QED

Theorem o1_walk_sim_static_abort[local]:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  reachable_fcg_acyclic unit.cu_context fcg /\
  ALL_DISTINCT (unit_label_namespace unit) /\
  run_callee_first rpolicy o1_fn_passes (fcg_postorder fcg entry)
    (prune_unit_fcg_unreachable unit fcg) s = SOME (unit', s') /\
  ir_supply_inst_ok s /\ EVERY (o1_fn_row 0) unit.cu_context.ctx_functions /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands) ==>
  !D fmp vs_out. dead_wf D /\ o1_initial_state_ok vs_out /\
    vs_out.vs_fmp = vs_out.vs_initial_fmp /\ code_layout_valid vs_out ==>
    ?vs_in. raw_variant fmp vs_in vs_out /\
      (o1_walk_src_inv D (prune_unit_fcg_unreachable unit fcg).cu_context vs_in /\
       fmp_variant_room (SOME fmp) unit'.cu_context vs_out ==>
       ctx_sim_fuel (cfg_norm_fuel unit'.cu_context) D
         (prune_unit_fcg_unreachable unit fcg).cu_context unit'.cu_context vs_in vs_out /\
       ctx_abort_rq D (prune_unit_fcg_unreachable unit fcg).cu_context
         unit'.cu_context vs_in vs_out /\
       (o1_lowered_inv unit'.cu_context vs_out \/
        ((?eom. max_live_eom unit'.cu_context = SOME eom /\
           mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
             lowered_mem_fact eom ctx fn inst s) unit'.cu_context vs_out) /\
         !fuel. terminates (run_context fuel
           (prune_unit_fcg_unreachable unit fcg).cu_context vs_in) ==>
           ?u. run_context fuel (prune_unit_fcg_unreachable unit fcg).cu_context vs_in =
             Abort ExHalt_abort u)))
Proof
  strip_tac >> drule_all o1_ctx_shape_prune >> strip_tac >>
  drule_all o1_walk_callee_first >> strip_tac >>
  fs[run_callee_first_def] >>
  drule_at (Pos (el 3)) (Q.INST [`R` |-> `o1_fn_row`] o1_schedule_stages) >>
  impl_tac
  >- fs[o1_fn_passes_steps, o1_step_contracts_from_rows, o1_prune_every] >>
  strip_tac >>
  `!fn inst. MEM fn (stage 0).ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands` by
    (gvs[prune_unit_fcg_unreachable_def] >>
     fs[MEM_FILTER] >> metis_tac[]) >>
  `!k fn inst. k <= LENGTH o1_fn_passes /\
     MEM fn (stage k).ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands` by
    (rpt gen_tac >> strip_tac >>
     irule (Q.INST [`n` |-> `LENGTH o1_fn_passes`,
                    `passes` |-> `o1_fn_passes`, `rpolicy` |-> `rpolicy`]
              o1_stage_chain_no_runtime_begin) >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `?names. callee_first names (stage 0).ctx_functions` by
    (qexists_tac `fcg_postorder fcg entry` >> gvs[]) >>
  `?vi. raw_variant fmp vi vs_out /\
    (o1_inv D 0 (stage 0) vi /\
     fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) vs_out ==>
     ctx_sim_fuel (cfg_norm_fuel (stage (LENGTH o1_fn_passes))) D
       (stage 0) (stage (LENGTH o1_fn_passes)) vi vs_out /\
     ctx_abort_rq D (stage 0) (stage (LENGTH o1_fn_passes)) vi vs_out /\
     (o1_lowered_inv (stage (LENGTH o1_fn_passes)) vs_out \/
      ((?eom. max_live_eom (stage (LENGTH o1_fn_passes)) = SOME eom /\
         mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
           lowered_mem_fact eom ctx fn inst s) (stage (LENGTH o1_fn_passes)) vs_out) /\
       !fuel. terminates (run_context fuel (stage 0) vi) ==>
         ?u. run_context fuel (stage 0) vi = Abort ExHalt_abort u)))` by
    (irule o1_walk_stages_sim_static_abort >> conj_tac
     >- (qexists_tac `rpolicy` >> rpt strip_tac >>
         first_x_assum drule >> simp[o1_walk_view_def]) >>
     simp[] >> strip_tac >>
     mp_tac (Q.INST [`C` |-> `stage 7`, `vs` |-> `vs_out`]
       o1_runtime_codecopy_labels_bound) >> impl_tac
     >- (conj_tac
         >- (qpat_x_assum `!k. k <= LENGTH o1_fn_passes ==>
               o1_ctx_shape (stage k) /\ _` (qspec_then `7` mp_tac) >>
             simp[o1_fn_passes_def]) >>
         qpat_x_assum `!k fn inst. _` (qspec_then `7` mp_tac) >>
         simp[o1_fn_passes_def]) >> simp[]) >>
  gvs[o1_inv_def] >> metis_tac[]
QED

Theorem o1_pre_walk_prune_static_abort[local]:
  o1_ctx_shape pre.cu_context /\ pre.cu_context.ctx_entry = SOME entry /\
  ctx_sim_fuel I D unit.cu_context pre.cu_context vs vs /\
  ctx_abort_rq D unit.cu_context pre.cu_context vs vs /\
  o1_walk_src_inv D pre.cu_context vs ==>
    ctx_sim_fuel I D unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs /\
    ctx_abort_rq D unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs /\
    o1_walk_src_inv D
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs
Proof
  strip_tac >> simp[LET_THM] >>
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
  `ctx_sim_fuel I D unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs` by
    (irule ctx_sim_run_context_eq >> qexists_tac `pre.cu_context` >> simp[]) >>
  `ctx_abort_rq D unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs` by
    (irule ctx_abort_rq_run_context_eq >> qexists_tac `pre.cu_context` >> simp[]) >>
  simp[]
QED

(* Use the walk contexts supplied by the caller's packet schedule. *)
Theorem o1_pipeline_pre_dft_source_facts_static_abort_fixed:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\ o1_source_unit_ok unit /\
  unit_entry_no_params unit /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME entry /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage (LENGTH o1_fn_passes) = out.po_unit.cu_context /\
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==>
       EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  dead_wf D /\ o1_initial_state_ok vs_out /\
  vs_out.vs_fmp = vs_out.vs_initial_fmp /\ code_layout_valid vs_out ==>
    o1_pre_walk_inv D unit.cu_context
      ((vs_out with vs_gas_readings := rds) with
        <|vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
    fmp_variant_room (SOME fmp) out.po_unit.cu_context vs_out ==>
    ctx_sim_fuel I D unit.cu_context (stage 7)
      ((vs_out with vs_gas_readings := rds) with
        <|vs_fmp := fmp; vs_initial_fmp := fmp|>)
      (vs_out with vs_gas_readings := rds) /\
    ctx_abort_rq D unit.cu_context (stage 7)
      ((vs_out with vs_gas_readings := rds) with
        <|vs_fmp := fmp; vs_initial_fmp := fmp|>)
      (vs_out with vs_gas_readings := rds) /\
    o1_inv D 0 (stage 0)
      ((vs_out with vs_gas_readings := rds) with
        <|vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
    o1_inv D 7 (stage 7) (vs_out with vs_gas_readings := rds)
Proof
  strip_tac >> simp[LET_THM] >>
  qabbrev_tac `vs_in = vs_out with
    <|vs_gas_readings := rds; vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  strip_tac >>
  `unit_wf unit /\ ALL_DISTINCT (unit_label_namespace unit) /\
   reachable_fcg_acyclic pre.cu_context (fcg_analyze pre.cu_context)` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ _ = _`
       (mp_tac o MATCH_MP o1_driver_runs o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
     strip_tac >> gvs[]) >>
  `o1_ctx_shape unit.cu_context /\ ir_supply_inst_ok (init_ir_supply unit)` by
    (simp[init_ir_supply_inst_ok] >> metis_tac[o1_source_unit_ok_ctx_shape]) >>
  drule_all o1_pre_walk_sim_static_abort >> strip_tac >>
  `o1_initial_state_ok vs_in /\ vs_in.vs_fmp = vs_in.vs_initial_fmp` by
    fs[Abbr `vs_in`, o1_initial_state_ok_def] >>
  `code_layout_valid vs_in` by
    (qpat_assum `code_layout_valid vs_out`
       (mp_tac o REWRITE_RULE [code_layout_valid_def]) >>
     simp[Abbr `vs_in`, code_layout_valid_def]) >>
  `ctx_sim_fuel I D unit.cu_context pre.cu_context vs_in vs_in /\
   ctx_abort_rq D unit.cu_context pre.cu_context vs_in vs_in /\
   o1_walk_src_inv D pre.cu_context vs_in` by metis_tac[] >>
  drule_all o1_pre_walk_prune_static_abort >> simp[LET_THM] >>
  strip_tac >>
  `o1_inv D 0 (stage 0) vs_in` by
    (simp[o1_inv_def] >>
     metis_tac[o1_walk_callee_first]) >>
  mp_tac (Q.INST [`rpolicy` |-> `rpolicy`, `stage` |-> `stage`, `D` |-> `D`,
    `vs_out` |-> `vs_out`, `rds` |-> `rds`, `fmp` |-> `fmp`]
    o1_walk_pre_dft_sim_static_abort_fixed) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
  impl_tac
  >- (conj_tac
      >- (qpat_assum `Abbrev (vs_in = _)` (fn th =>
            qpat_assum `o1_inv D 0 (stage 0) vs_in`
              (mp_tac o REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] th])) >>
          SIMP_TAC (srw_ss()) []) >>
      simp[]) >>
  strip_tac >>
  `ctx_sim_fuel (I o I) D unit.cu_context (stage 7) vs_in
     (vs_out with vs_gas_readings := rds)` by
    (irule ctx_sim_fuel_trans >> fs[Abbr `vs_in`] >> metis_tac[]) >>
  fs[Abbr `vs_in`, combinTheory.I_o_ID] >>
  metis_tac[ctx_abort_rq_trans]
QED

Theorem o1_pipeline_pre_dft_sim_static_abort_fixed:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\ o1_source_unit_ok unit /\
  unit_entry_no_params unit /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME entry /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage (LENGTH o1_fn_passes) = out.po_unit.cu_context /\
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==>
       EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  dead_wf D /\ o1_initial_state_ok vs_out /\
  vs_out.vs_fmp = vs_out.vs_initial_fmp /\ code_layout_valid vs_out ==>
    o1_pre_walk_inv D unit.cu_context
      ((vs_out with vs_gas_readings := rds) with
        <|vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
    fmp_variant_room (SOME fmp) out.po_unit.cu_context vs_out ==>
    ctx_sim_fuel I D unit.cu_context (stage 7)
      ((vs_out with vs_gas_readings := rds) with
        <|vs_fmp := fmp; vs_initial_fmp := fmp|>)
      (vs_out with vs_gas_readings := rds) /\
    ctx_abort_rq D unit.cu_context (stage 7)
      ((vs_out with vs_gas_readings := rds) with
        <|vs_fmp := fmp; vs_initial_fmp := fmp|>)
      (vs_out with vs_gas_readings := rds) /\
    o1_inv D 7 (stage 7) (vs_out with vs_gas_readings := rds)
Proof
  ntac 2 strip_tac >>
  drule_all o1_pipeline_pre_dft_source_facts_static_abort_fixed >> simp[]
QED

Theorem o1_pipeline_stage_facts_static_abort[local]:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy o1_pipeline_spec unit =
    SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands) ==>
  !D fmp vs_out. dead_wf D /\ o1_initial_state_ok vs_out /\
    vs_out.vs_fmp = vs_out.vs_initial_fmp /\ code_layout_valid vs_out ==>
    ?vs_in. raw_variant fmp vs_in vs_out /\
      (o1_pre_walk_inv D unit.cu_context vs_in /\
       fmp_variant_room (SOME fmp) out.po_unit.cu_context vs_out ==>
       ctx_sim_fuel (cfg_norm_fuel out.po_unit.cu_context) D
         unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       ctx_abort_rq D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       (o1_lowered_inv out.po_unit.cu_context vs_out \/
        ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
           mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
             lowered_mem_fact eom ctx fn inst s) out.po_unit.cu_context vs_out) /\
         !fuel. terminates (run_context fuel unit.cu_context vs_in) ==>
           ?u. run_context fuel unit.cu_context vs_in = Abort ExHalt_abort u)))
Proof
  strip_tac >> drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)` by
    simp[irSupplyTheory.init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  drule_all o1_pre_walk_sim_static_abort >> strip_tac >>
  `!fn inst. MEM fn pre.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands` by
    (mp_tac (Q.INST [`unit'` |-> `pre`, `s` |-> `init_ir_supply unit`,
                     `s'` |-> `t`] o1_pre_walk_no_runtime_begin) >>
     impl_tac >- metis_tac[] >> simp[]) >>
  mp_tac (Q.INST [`fcg` |-> `fcg_analyze pre.cu_context`, `unit` |-> `pre`,
                  `s` |-> `t`, `unit'` |-> `out.po_unit`, `s'` |-> `t'`]
            o1_walk_sim_static_abort) >> impl_tac
  >- (gvs[] >> metis_tac[unit_labels_wf_namespace]) >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!D fmp vs_out. _` (qspecl_then [`D`, `fmp`, `vs_out`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `vs` strip_assume_tac) >>
  qexists_tac `vs` >> simp[] >> strip_tac >>
  `o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs` by
    (gvs[raw_variant_def, gas_variant_def, venom_state_component_equality,
         o1_initial_state_ok_def, code_layout_valid_def] >> metis_tac[]) >>
  `ctx_sim_fuel I D unit.cu_context pre.cu_context vs vs /\
   ctx_abort_rq D unit.cu_context pre.cu_context vs vs /\
   o1_walk_src_inv D pre.cu_context vs` by metis_tac[] >>
  `ctx_sim_fuel I D unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs /\
   ctx_abort_rq D unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs /\
   o1_walk_src_inv D
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs` by
    (drule_all o1_pre_walk_prune_static_abort >> simp[LET_THM]) >>
  `ctx_sim_fuel (cfg_norm_fuel out.po_unit.cu_context) D
     (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context
     out.po_unit.cu_context vs vs_out /\
   ctx_abort_rq D (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context
     out.po_unit.cu_context vs vs_out` by metis_tac[] >>
  `ctx_sim_fuel (cfg_norm_fuel out.po_unit.cu_context o I) D
     unit.cu_context out.po_unit.cu_context vs vs_out` by
    (irule ctx_sim_fuel_trans >> metis_tac[]) >>
  simp[combinTheory.I_o_ID] >> conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[ctx_abort_rq_trans] >>
  Cases_on `o1_lowered_inv out.po_unit.cu_context vs_out` >> simp[] >>
  fs[] >> rpt strip_tac >>
  `dead_result_rel D (run_context fuel unit.cu_context vs)
    (run_context fuel (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs)` by
    fs[ctx_sim_fuel_def] >>
  `terminates (run_context fuel (prune_unit_fcg_unreachable pre
      (fcg_analyze pre.cu_context)).cu_context vs)` by
    metis_tac[dead_result_rel_terminates] >>
  `?u. run_context fuel (prune_unit_fcg_unreachable pre
      (fcg_analyze pre.cu_context)).cu_context vs = Abort ExHalt_abort u` by
    metis_tac[] >>
  Cases_on `run_context fuel unit.cu_context vs` >>
  gvs[dead_result_rel_def] >> rename1 `reason <> Revert_abort` >>
  Cases_on `reason` >> gvs[]
QED

(* The semantic use of the schedule must use the same stage witness as
   the no-runtime_begin induction. Do not invoke a second schedule choice. *)
Theorem run_venom_pipeline_fuel_static_abort:
  !D lo rpolicy unit out vs_out fmp.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ ~ctx_has_dalloca unit.cu_context /\
    unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
    o1_initial_state_ok vs_out /\ vs_out.vs_fmp = vs_out.vs_initial_fmp /\
    code_layout_valid vs_out /\
    (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
       ~MEM (Label "runtime_begin") inst.inst_operands) /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context /\ dead_wf D /\
    (!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
           eom <= w2n vs_out.vs_initial_fmp) /\
    w2n vs_out.vs_initial_fmp <= w2n fmp ==>
    ?vs_in. raw_variant fmp vs_in vs_out /\
      (raw_unit_memory_ok unit.cu_context vs_in /\
       ptr_discipline lo unit.cu_context vs_in /\
       taint_within D unit.cu_context vs_in /\
       mem_inv dload_offset_ok unit.cu_context vs_in /\
       mem_inv dload_headroom_ok unit.cu_context vs_in ==>
       ctx_sim_fuel (cfg_norm_fuel out.po_unit.cu_context) D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       ctx_abort_rq D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       (o1_lowered_inv out.po_unit.cu_context vs_out \/
        ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
           mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                     lowered_mem_fact eom ctx fn inst s) out.po_unit.cu_context vs_out) /\
         !fuel. terminates (run_context fuel unit.cu_context vs_in) ==>
                ?u. run_context fuel unit.cu_context vs_in = Abort ExHalt_abort u)))

Proof
  rpt strip_tac >>
  `fmp_free_ctx unit.cu_context` by (irule source_fmp_free >> fs[]) >>
  `EVERY pre_fmp_ops unit.cu_context.ctx_functions /\
   ~ctx_has_dalloca unit.cu_context` by
    (simp[EVERY_MEM] >>
     metis_tac[source_pre_fmp_ops]) >>
  (* At an input state whose free-memory pointer is its initial one, no
     reachable state moves it: the raw phase's FMP facts hold. *)
  `!vi. vi.vs_fmp = vi.vs_initial_fmp /\
        raw_unit_memory_ok unit.cu_context vi /\
        ptr_discipline lo unit.cu_context vi /\
        taint_within D unit.cu_context vi /\
        mem_inv dload_offset_ok unit.cu_context vi /\
        mem_inv dload_headroom_ok unit.cu_context vi ==>
        o1_pre_walk_inv D unit.cu_context vi` by
    (rpt strip_tac >>
     `mem_inv raw_mem_ok unit.cu_context vi` by
       (simp[raw_unit_memory_ok_mem_inv] >> rpt gen_tac >> strip_tac >>
        drule raw_reachable_fmp_fixed >> simp[] >> strip_tac >>
        drule raw_reachable_initial_fmp >> strip_tac >>
        `inst.inst_opcode <> DALLOCA` by
          (`EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)` by
             (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >>
              metis_tac[]) >>
           imp_res_tac EVERY_active_inst >> gvs[]) >>
        simp[dalloca_no_wrap_def]) >>
     `o1_src_inv D unit.cu_context vi` by
       (fs[o1_src_inv_def] >> metis_tac[]) >>
     irule o1_source_pre_walk_inv >> simp[]) >>
  fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  drule_all o1_pipeline_stage_facts_static_abort >> strip_tac >>
  qpat_x_assum `!fmp. ?vs_in. _` (qspec_then `fmp` mp_tac) >>
  simp[fmp_variant_room_def] >> strip_tac >>
  qexists_tac `vs_in` >> simp[] >> strip_tac >>
  `vs_in.vs_fmp = vs_in.vs_initial_fmp` by
    gvs[raw_variant_def, gas_variant_def,
       venomStateTheory.venom_state_component_equality] >>
  metis_tac[]
QED

Theorem run_venom_pipeline_correct_static_abort:
  !D lo rpolicy unit out vs_out fmp.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ ~ctx_has_dalloca unit.cu_context /\
    unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
    o1_initial_state_ok vs_out /\ vs_out.vs_fmp = vs_out.vs_initial_fmp /\
    code_layout_valid vs_out /\
    (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
       ~MEM (Label "runtime_begin") inst.inst_operands) /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context /\ dead_wf D /\
    (!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
           eom <= w2n vs_out.vs_initial_fmp) /\
    w2n vs_out.vs_initial_fmp <= w2n fmp ==>
    ?vs_in. raw_variant fmp vs_in vs_out /\
      (raw_unit_memory_ok unit.cu_context vs_in /\
       ptr_discipline lo unit.cu_context vs_in /\
       taint_within D unit.cu_context vs_in /\
       mem_inv dload_offset_ok unit.cu_context vs_in /\
       mem_inv dload_headroom_ok unit.cu_context vs_in ==>
       ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       ctx_abort_rq D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       (o1_lowered_inv out.po_unit.cu_context vs_out \/
        ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
           mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                     lowered_mem_fact eom ctx fn inst s) out.po_unit.cu_context vs_out) /\
         !fuel. terminates (run_context fuel unit.cu_context vs_in) ==>
                ?u. run_context fuel unit.cu_context vs_in = Abort ExHalt_abort u)))
Proof
  rpt strip_tac >>
  drule_all run_venom_pipeline_fuel_static_abort >> strip_tac >>
  qexists_tac `vs_in` >> metis_tac[ctx_sim_fuel_imp_ctx_sim]
QED

Theorem run_venom_pipeline_run_bounded_static_abort:
  !lo rpolicy unit out cp fuel.
    o1_pipeline rpolicy unit = SOME out /\
    generate_context_plan out.po_unit.cu_context = SOME cp ==>
    ?fuel' M. !D vs fmp.
      o1_source_unit_ok unit /\ unit_entry_no_params unit /\
      unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
      o1_initial_state_ok vs /\
      vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
      (!fn inst.
        MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
        ~MEM (Label "runtime_begin") inst.inst_operands) /\
      reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
      EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
      fixed_region_reserved lo unit.cu_context /\ dead_wf D /\
      vs.vs_initial_fmp = n2w cp.cp_initial_fmp /\
      w2n vs.vs_initial_fmp <= w2n fmp /\
      (!vs_in. raw_variant fmp vs_in vs ==>
        raw_unit_memory_ok unit.cu_context vs_in /\
        ptr_discipline lo unit.cu_context vs_in /\
        taint_within D unit.cu_context vs_in /\
        mem_inv dload_offset_ok unit.cu_context vs_in /\
        mem_inv dload_headroom_ok unit.cu_context vs_in /\
        terminates (run_context fuel unit.cu_context vs_in)) ==>
      venom_run_bounded fuel' M out.po_unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  qexistsl_tac [`cfg_norm_fuel out.po_unit.cu_context fuel`,
                `2 * dimword (:256)`] >>
  rpt gen_tac >> strip_tac >>
  `!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
         eom <= w2n vs.vs_initial_fmp` by
    metis_tac[generate_context_plan_eom_room] >>
  `fmp_variant_room (SOME fmp) out.po_unit.cu_context vs` by
    simp[fmp_variant_room_def] >>
  RULE_ASSUM_TAC (REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
  drule_all o1_pipeline_stage_facts_static_abort >> strip_tac >>
  qpat_x_assum `!fmp. ?vs_in. _`
    (qspec_then `fmp` (qx_choose_then `vi` strip_assume_tac)) >>
  qpat_x_assum `!vs_in. raw_variant fmp vs_in vs ==> _`
    (qspec_then `vi` mp_tac) >> simp[] >> strip_tac >>
  `mem_inv raw_mem_ok unit.cu_context vi` by
    (simp[raw_unit_memory_ok_mem_inv] >> rpt strip_tac >>
     fs[raw_unit_memory_ok_def] >>
     metis_tac[contextRawReachableTheory.raw_reachable_least]) >>
  `o1_pre_walk_inv D unit.cu_context vi` by
    (irule o1_source_pre_walk_inv >> simp[o1_src_inv_def] >>
     metis_tac[source_fmp_free]) >>
  `ctx_sim_fuel (cfg_norm_fuel out.po_unit.cu_context) D
     unit.cu_context out.po_unit.cu_context vi vs` by metis_tac[] >>
  `terminates
     (run_context (cfg_norm_fuel out.po_unit.cu_context fuel)
       out.po_unit.cu_context vs)` by
    (fs[ctx_sim_fuel_def] >> metis_tac[dead_result_rel_terminates]) >>
  `?Inv. codegen_reachability_package Inv out.po_unit.cu_context vs` by
    (fs[o1_lowered_inv_def, mem_inv_def] >> metis_tac[]) >>
  metis_tac[venomRunBoundedTheory.venom_run_bounded_word_ceiling]
QED

Theorem o1_pipeline_code_end_offset_ok_static_abort_fixed:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\ o1_source_unit_ok unit /\
  unit_entry_no_params unit /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME entry /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage (LENGTH o1_fn_passes) = out.po_unit.cu_context /\
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==>
       EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  dead_wf D /\ o1_initial_state_ok vs_out /\
  vs_out.vs_fmp = vs_out.vs_initial_fmp /\ code_layout_valid vs_out /\
  LENGTH vs_out.vs_data_section < dimword (:256) DIV 2 /\
  v7 = (vs_out with vs_gas_readings := rds) /\
  vi = (v7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  (!fuel. gas_res_rel (run_context fuel (stage 7) v7)
     (ev_context orc fuel (stage 7) vs_out)) /\
  (!fuel. gas_res_rel (run_context fuel (stage 8) vs_out)
     (ev_context orc fuel (stage 8) vs_out)) /\
  (!p d fn inst s. ev_reachable orc vs_out (stage 7) p d fn inst s ==>
     ?ws. raw_reachable v7 (stage 7) fn inst (s with vs_gas_readings := ws)) /\
  (!fn inst s. raw_reachable vs_out (stage 8) fn inst s ==>
     ?p d. ev_reachable orc vs_out (stage 8) p d fn inst
            (s with vs_gas_readings := vs_out.vs_gas_readings)) /\
  o1_pre_walk_inv D unit.cu_context vi /\
  fmp_variant_room (SOME fmp) out.po_unit.cu_context vs_out /\
  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
    s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
    unit.cu_context vi /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "code_end") inst.inst_operands) ==>
  code_end_offset_ok
    (\ctx fn inst s. raw_reachable vs_out ctx fn inst s /\ ~in_static_abort_prefix fn s)
    out.po_unit.cu_context /\
  (code_end_offset_ok (raw_reachable vs_out) out.po_unit.cu_context \/
   !fuel. terminates (run_context fuel unit.cu_context vi) ==>
     ?u. run_context fuel unit.cu_context vi = Abort ExHalt_abort u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH o1_fn_passes = 9` by EVAL_TAC >>
  `!k. k < 9 ==> o1_pre k (stage k) (stage (SUC k))` by
    (rw[o1_pre_def] >> first_x_assum irule >> simp[]) >>
  mp_tac (Q.INST [`rpolicy` |-> `rpolicy`, `stage` |-> `stage`, `D` |-> `D`,
    `unit` |-> `unit`, `out` |-> `out`, `pre` |-> `pre`, `t` |-> `t`,
    `entry` |-> `entry`, `vs_out` |-> `vs_out`, `rds` |-> `rds`, `fmp` |-> `fmp`]
    o1_pipeline_pre_dft_source_facts_static_abort_fixed) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  PURE_REWRITE_TAC [LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  qpat_assum `v7 = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  qpat_assum `vi = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `unit_wf unit /\ ALL_DISTINCT (unit_label_namespace unit)` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ _ = _`
       (mp_tac o MATCH_MP o1_driver_runs o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
     simp[]) >>
  `o1_ctx_shape unit.cu_context /\ ir_supply_inst_ok (init_ir_supply unit)` by
    (simp[init_ir_supply_inst_ok] >> metis_tac[o1_source_unit_ok_ctx_shape]) >>
  `vi.vs_vars = FEMPTY /\ ~vi.vs_halted` by fs[o1_initial_state_ok_def] >>
  `EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions /\
   EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) unit.cu_context.ctx_functions` by
    (fs[o1_pre_walk_inv_def, o1_ctx_shape_def, EVERY_MEM] >>
     metis_tac[o1_fn_shape_def, SRULE [EVERY_MEM] simplify_cfg_fn_ok_no_phi]) >>
  `EVERY make_ssa_input_ok (stage 0).ctx_functions` by fs[o1_inv_def, o1_walk_src_inv_def] >>
  map_every (fn k =>
    qpat_assum `!k. k < LENGTH _ ==> _`
      (qspec_then k (assume_tac o SIMP_RULE (srw_ss()) [o1_fn_passes_def])) >>
    qpat_assum `!k. k <= LENGTH _ ==> o1_ctx_shape _`
      (qspec_then k (assume_tac o SIMP_RULE (srw_ss()) [o1_fn_passes_def])) >>
    qpat_assum `!k. k <= LENGTH _ ==> EVERY _ _`
      (qspec_then k (assume_tac o SIMP_RULE (srw_ss()) [o1_fn_passes_def])))
    [`0`, `7`, `8`] >>
  mp_tac (Q.INST [`C1` |-> `stage 1`, `fcg` |-> `fcg_analyze pre.cu_context`,
    `vs` |-> `vi`, `view` |-> `o1_walk_view rpolicy 0`, `rp` |-> `rpolicy`,
    `supply` |-> `init_ir_supply unit`, `supply'` |-> `t`]
    code_end_source_prefix_transport) >>
  qpat_assum `stage 0 = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >> strip_tac >>
  `fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) vs_out` by simp[] >>
  drule_all o1_code_end_pre_dft_bound_fixed >> strip_tac >>
  `EVERY wf_ssa (stage 7).ctx_functions` by fs[o1_fn_row_def, EVERY_MEM] >>
  `o1_pre 7 (stage 7) (stage 8)` by simp[o1_pre_def] >>
  `code_end_offset_ok
    (\ctx fn inst s. raw_reachable vs_out ctx fn inst s /\ ~in_static_abort_prefix fn s) (stage 9) /\
   (code_end_offset_ok (raw_reachable vs_out) (stage 9) \/
    !fuel. terminates (run_context fuel (stage 7) v7) ==>
      ?u. run_context fuel (stage 7) v7 = Abort ExHalt_abort u)` by
    (mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`, `C9` |-> `stage 9`,
      `rp` |-> `rpolicy`, `vs_out` |-> `vs_out`, `rds` |-> `rds`, `orc` |-> `orc`,
      `dft_view` |-> `o1_walk_view rpolicy 7`, `cfg_view` |-> `o1_walk_view rpolicy 8`]
      o1_code_end_dft_exit_fixed) >>
     qpat_assum `v7 = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `stage 9 = out.po_unit.cu_context` by fs[] >>
  qpat_assum `stage 9 = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  TRY (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> rpt strip_tac >>
  `dead_result_rel D (run_context fuel unit.cu_context vi)
     (run_context fuel (stage 7) v7)` by fs[ctx_sim_fuel_def] >>
  `terminates (run_context fuel (stage 7) v7)` by metis_tac[dead_result_rel_terminates] >>
  `?u. run_context fuel (stage 7) v7 = Abort ExHalt_abort u` by metis_tac[] >>
  Cases_on `run_context fuel unit.cu_context vi` >>
  gvs[dead_result_rel_def] >> rename1 `reason <> Revert_abort` >>
  Cases_on `reason` >> gvs[]
QED

Theorem o1_pipeline_code_end_offset_ok_static_abort:
  !D lo rpolicy unit out vs_out fmp.
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
    o1_initial_state_ok vs_out /\ vs_out.vs_fmp = vs_out.vs_initial_fmp /\
    code_layout_valid vs_out /\
    (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
       ~MEM (Label "runtime_begin") inst.inst_operands) /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context /\ dead_wf D /\
    (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
               ~MEM (Label "code_end") inst.inst_operands) /\
    LENGTH vs_out.vs_data_section < dimword (:256) DIV 2 /\
    (!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
           eom <= w2n vs_out.vs_initial_fmp) /\
    w2n vs_out.vs_initial_fmp <= w2n fmp ==>
    ?vs_in. raw_variant fmp vs_in vs_out /\
      (raw_unit_memory_ok unit.cu_context vs_in /\
       ptr_discipline lo unit.cu_context vs_in /\
       taint_within D unit.cu_context vs_in /\
       mem_inv dload_offset_ok unit.cu_context vs_in /\
       mem_inv dload_headroom_ok unit.cu_context vs_in /\
       mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                               s.vs_code = vs_in.vs_code /\
                               s.vs_data_section = vs_in.vs_data_section)
         unit.cu_context vs_in ==>
       code_end_offset_ok
         (\ctx fn inst s. raw_reachable vs_out ctx fn inst s /\
                          ~in_static_abort_prefix fn s)
         out.po_unit.cu_context /\
       (code_end_offset_ok (raw_reachable vs_out) out.po_unit.cu_context \/
        !fuel. terminates (run_context fuel unit.cu_context vs_in) ==>
               ?u. run_context fuel unit.cu_context vs_in = Abort ExHalt_abort u))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out`
    (assume_tac o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
  drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)` by simp[init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  drule_all o1_pre_walk_sim_static_abort >> strip_tac >>
  `ALL_DISTINCT (unit_label_namespace pre)` by metis_tac[unit_labels_wf_namespace] >>
  mp_tac (Q.INST [`unit` |-> `pre`, `fcg` |-> `fcg_analyze pre.cu_context`]
    o1_ctx_shape_prune) >> simp[] >> strip_tac >>
  mp_tac (Q.INST [`unit` |-> `pre`, `fcg` |-> `fcg_analyze pre.cu_context`,
    `entry` |-> `entry`] o1_walk_callee_first) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC))) >>
  strip_tac >>
  fs[run_callee_first_def] >>
  drule_at (Pos (el 3)) (Q.INST [`R` |-> `o1_fn_row`] o1_schedule_stages) >>
  impl_tac
  >- fs[o1_fn_passes_steps, o1_step_contracts_from_rows, o1_prune_every] >>
  strip_tac >>
  `!k. k < LENGTH o1_fn_passes ==>
      ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
        (stage k) (stage (SUC k))` by
    (rpt strip_tac >> first_x_assum drule >> simp[o1_walk_view_def]) >>
  `(!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
   (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions)` by
    (conj_tac >> rpt strip_tac >>
     qpat_assum `!k. k <= LENGTH _ ==> o1_ctx_shape _ /\ _` (qspec_then `k` mp_tac) >>
     simp[]) >>
  `LENGTH o1_fn_passes = 9` by EVAL_TAC >>
  qpat_assum `!k. k < LENGTH _ ==> ctx_pass_stage rpolicy _ (o1_walk_view _ _) _ _`
    (qspec_then `7` (assume_tac o SIMP_RULE (srw_ss()) [o1_fn_passes_def])) >>
  qpat_assum `!k. k <= LENGTH _ ==> o1_ctx_shape _`
    (qspec_then `7` (assume_tac o SIMP_RULE (srw_ss()) [o1_fn_passes_def])) >>
  map_every (fn k =>
    qpat_assum `!k. k <= LENGTH _ ==> EVERY _ _`
      (qspec_then k (assume_tac o SIMP_RULE (srw_ss()) [o1_fn_passes_def])))
    [`7`, `8`] >>
  `o1_pre 7 (stage 7) (stage 8)` by simp[o1_pre_def] >>
  `EVERY wf_ssa (stage 7).ctx_functions` by fs[o1_fn_row_def, EVERY_MEM] >>
  drule_all dft_stage_fn_rel >> strip_tac >>
  drule_all dft_ctx_gas_replay_witness >>
  disch_then (qspec_then `vs_out`
    (qx_choosel_then [`orc`, `rds`] strip_assume_tac)) >>
  qabbrev_tac `v7 = vs_out with vs_gas_readings := rds` >>
  qabbrev_tac `vi = v7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  qexists_tac `vi` >> conj_tac
  >- simp[Abbr `vi`, Abbr `v7`, raw_variant_def, gas_variant_def,
          venom_state_component_equality] >>
  strip_tac >>
  `mem_inv raw_mem_ok unit.cu_context vi` by
    (simp[raw_unit_memory_ok_mem_inv] >> rpt strip_tac >>
     fs[raw_unit_memory_ok_def] >>
     metis_tac[contextRawReachableTheory.raw_reachable_least]) >>
  `fmp_free_ctx unit.cu_context` by (irule source_fmp_free >> fs[]) >>
  `o1_src_inv D unit.cu_context vi` by
    (simp[o1_src_inv_def] >> qexists_tac `lo` >> simp[]) >>
  `o1_pre_walk_inv D unit.cu_context vi` by
    (irule o1_source_pre_walk_inv >> simp[]) >>
  `fmp_variant_room (SOME fmp) out.po_unit.cu_context vs_out` by
    simp[fmp_variant_room_def] >>
  mp_tac (Q.INST [`D` |-> `D`, `rpolicy` |-> `rpolicy`, `unit` |-> `unit`,
    `out` |-> `out`, `vi` |-> `vi`, `v7` |-> `v7`, `pre` |-> `pre`,
    `stage` |-> `stage`, `t` |-> `t`, `entry` |-> `entry`,
    `vs_out` |-> `vs_out`, `rds` |-> `rds`, `orc` |-> `orc`, `fmp` |-> `fmp`]
    o1_pipeline_code_end_offset_ok_static_abort_fixed) >>
  simp[Abbr `vi`, Abbr `v7`] >> metis_tac[]
QED
