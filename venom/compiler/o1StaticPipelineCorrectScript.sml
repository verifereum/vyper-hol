(* The static pipeline reuses one walk input through both pre-walk stages. *)
Theory o1StaticPipelineCorrect
Ancestors
  o1StaticPipelineCompose o1PipelineCorrect o1LabelStages o1PipelineCompose
  o1LabelFlowStaticContracts
  o1DretDesugarContract o1ScheduleDecomp o1FnScheduleDecompHelpers
  o1ComposeSupport o1ContractSimplifyCfg o1PassContract o1RequestContract
  ctxLookupAgree ctxLookupAgreeHelpers venomPipelineDriver venomPipelineRunner
  venomFnScheduleRunner venomPassSchedule fcgDefs fcgAnalysisProps fcgBridge
  fcgPruning fcgPostorder ptrDiscipline rawReachableFmp unitTransformDefs
  unitShapeDefs unitMemInv irSupply stateEquivProps staticAbortDefs
  lowerDloadDefs venomState list rich_list

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
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
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
     metis_tac[source_pre_fmp_ops, o1_source_unit_ok_no_dalloca]) >>
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
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
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
