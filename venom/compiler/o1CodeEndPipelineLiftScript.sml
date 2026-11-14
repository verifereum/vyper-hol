Theory o1CodeEndPipelineLift
Ancestors
  codegenSymRel o1CodeEndScheduleRetention o1CodeEndSourceTransport
  o1PipelineCompose o1PassContract venomFnScheduleRunner
  unitMemInv contextRawReachable words list o1ComposeSupport
  venomPipelineRunner venomPipelineRunnerProps venomPassSchedule
  irSupply unitShapeDefs unitTransformDefs o1ContractSimplifyCfg

Theorem o1_code_end_pipeline_from_walk:
  (!rpolicy stage D vs_out.
    (!k. k < LENGTH o1_fn_passes ==>
      ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
        (stage k) (stage (SUC k))) /\
    ctx_pass_stage rpolicy (EL 3 o1_fn_passes)
      (\C' f observed. o1_walk_view rpolicy 3 C' f observed /\
        EVERY fmp_sig_no_param observed.cu_context.ctx_functions)
      (stage 3) (stage 4) /\
    (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
    (!k. k <= LENGTH o1_fn_passes ==>
      EVERY (o1_fn_row k) (stage k).ctx_functions) /\
    dead_wf D /\ o1_run_state_ok vs_out /\
    LENGTH vs_out.vs_data_section < dimword (:256) DIV 2 ==>
    ?vi. gas_variant vi vs_out /\
      (o1_inv D 0 (stage 0) vi /\
       mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
         s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
         (stage 1) vi /\
       (!f i. MEM f (stage 1).ctx_functions /\ MEM i (fn_insts f) ==>
         ~MEM (Label "code_end") i.inst_operands) ==>
       ctx_sim_fuel (cfg_norm_fuel (stage (LENGTH o1_fn_passes))) D
         (stage 0) (stage (LENGTH o1_fn_passes)) vi vs_out /\
       o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out /\
       code_end_offset_ok (raw_reachable vs_out) (stage (LENGTH o1_fn_passes)))) ==>
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy o1_pipeline_spec unit =
    SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit ==>
  !D vs_out. dead_wf D /\ o1_run_state_ok vs_out /\
    LENGTH vs_out.vs_data_section < dimword (:256) DIV 2 ==>
    ?vs_in. gas_variant vs_in vs_out /\
      (o1_pre_walk_inv D unit.cu_context vs_in /\
       mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
         s.vs_code = vs_in.vs_code /\ s.vs_data_section = vs_in.vs_data_section)
         unit.cu_context vs_in /\
       (!f i. MEM f unit.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
         ~MEM (Label "code_end") i.inst_operands) ==>
       ctx_sim_fuel (cfg_norm_fuel out.po_unit.cu_context) D
         unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       o1_lowered_inv out.po_unit.cu_context vs_out /\
       code_end_offset_ok (raw_reachable vs_out) out.po_unit.cu_context)
Proof
  disch_tac >> strip_tac >> drule o1_driver_runs >> strip_tac >>
  rename1 `run_pipeline_stages _ _ _ _ = SOME (pre,pre_supply)` >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)` by
    simp[irSupplyTheory.init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  mp_tac (Q.INST [`unit` |-> `pre`,
    `fcg` |-> `fcg_analyze pre.cu_context`] o1_ctx_shape_prune) >>
  simp[] >> strip_tac >>
  mp_tac (Q.INST [`unit` |-> `pre`,
    `fcg` |-> `fcg_analyze pre.cu_context`] o1_walk_callee_first) >>
  simp[] >> strip_tac >>
  fs[run_callee_first_def] >>
  drule o1_code_end_named_schedules_stages >>
  (impl_tac >- metis_tac[o1_prune_every, unit_labels_wf_namespace]) >>
  disch_then (qx_choose_then `stage` strip_assume_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!rpolicy stage D vs_out. _`
    (qspecl_then [`rpolicy`, `stage`, `D`, `vs_out`] mp_tac) >>
  simp[] >>
  disch_then (qx_choose_then `vi` strip_assume_tac) >>
  qexists_tac `vi` >> simp[] >> strip_tac >>
  suspend "forward"
QED

Resume o1_code_end_pipeline_from_walk[forward]:
  `o1_run_state_ok vi` by metis_tac[gas_variant_run_state_ok] >>
  `ctx_sim_fuel I D unit.cu_context pre.cu_context vi vi /\
   o1_walk_src_inv D pre.cu_context vi` by metis_tac[] >>
  `o1_walk_src_inv D (stage 0) vi` by
    (asm_rewrite_tac[] >>
     qpat_x_assum `o1_walk_src_inv D pre.cu_context vi` mp_tac >>
     rewrite_tac[o1_walk_src_inv_def] >> strip_tac >> conj_tac
     >- (irule o1_src_inv_prune >> metis_tac[]) >>
     conj_tac >> irule o1_prune_every >> first_assum ACCEPT_TAC) >>
  `o1_inv D 0 (stage 0) vi` by
    (simp[o1_inv_def] >> metis_tac[]) >>
  `EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions /\
   EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f))
     unit.cu_context.ctx_functions` by
    (fs[o1_pre_walk_inv_def, o1_ctx_shape_def, EVERY_MEM] >>
     metis_tac[o1_fn_shape_def, SRULE [EVERY_MEM] simplify_cfg_fn_ok_no_phi]) >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) (o1_walk_view rpolicy 0)
     (stage 0) (stage 1)` by
    (qpat_x_assum `!k. k < LENGTH _ ==> _` (qspec_then `0` mp_tac) >>
     simp[o1_fn_passes_def]) >>
  `EVERY make_ssa_input_ok (stage 0).ctx_functions` by
    fs[o1_walk_src_inv_def] >>
  `vi.vs_vars = FEMPTY /\ ~vi.vs_halted` by
    fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  drule (Q.INST [`C1` |-> `stage 1`, `fcg` |-> `fcg_analyze pre.cu_context`,
    `vs` |-> `vi`, `view` |-> `o1_walk_view rpolicy 0`]
    code_end_source_prefix_transport) >>
  disch_then (qspecl_then [`vi`, `stage`, `rpolicy`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  qpat_x_assum `o1_inv D 0 _ vi /\ _ ==> _` mp_tac >>
  simp[] >> strip_tac >>
  `(!fuel vs. run_context fuel pre.cu_context vs =
      run_context fuel (stage 0) vs)` by
    (asm_rewrite_tac[] >>
     mp_tac (Q.INST [`M` |-> `raw_mem_ok`, `unit` |-> `pre`,
       `fcg` |-> `fcg_analyze pre.cu_context`] o1_prune_sim) >>
     simp[] >> (impl_tac >- metis_tac[raw_mem_ok_ctx_free]) >> simp[]) >>
  `ctx_sim_fuel I D unit.cu_context (stage 0) vi vi` by
    (irule ctx_sim_run_context_eq >> qexists_tac `pre.cu_context` >> simp[]) >>
  fs[o1_inv_def, o1_fn_passes_def] >>
  metis_tac[SRULE [] (Q.INST [`f` |-> `I`] ctx_sim_fuel_trans)]
QED
Finalise o1_code_end_pipeline_from_walk
