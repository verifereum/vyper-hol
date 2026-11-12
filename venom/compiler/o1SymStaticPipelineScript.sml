Theory o1SymStaticPipeline
Ancestors
  o1SymStaticSimple o1SymStaticMakeSSA o1SymStaticSimplifyCFG
  o1SymStaticCFGNormalization o1SymStaticFMP o1SymStaticSchedule
  o1PipelineCorrect o1PipelineCompose o1ComposeSupport
  venomPassDispatcher venomFnScheduleRunner fmpStepBridge
  o1PassContract venomFnScheduleRunnerProps o1DretDesugarContract
  o1ContractSimplifyCfg o1FnScheduleDecompHelpers fcgPruning
  venomPipelineRunner venomInst list rich_list

Theorem configured_runtime_reflect:
  fn_pass_step rp pass observed s fn out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s ==>
  ((?i. MEM i (fn_insts out.fpo_function) /\
        MEM (Label "runtime_begin") i.inst_operands) ==>
   (?i. MEM i (fn_insts fn) /\ MEM (Label "runtime_begin") i.inst_operands))
Proof
  strip_tac >>
  `MEM fn observed.cu_context.ctx_functions` by
    metis_tac[fn_pass_step_def, lookup_unique_function_member] >>
  `o1_fn_shape observed.cu_context fn` by
    gvs[o1_ctx_shape_def, EVERY_MEM] >>
  `ir_supply_covers_fn s fn` by
    metis_tac[fn_pass_step_def, ir_supply_covers_unit_member] >>
  fs[fn_pass_step_def] >> Cases_on `pass` >> Cases_on `v` >>
  gvs[execute_configured_fn_pass_def, AllCaseEqs()] 
  >- metis_tac[concretize_context_runtime_reflect]
  >- metis_tac[cfg_norm_function_supply_runtime_reflect]
  >- metis_tac[dft_runtime_reflect]
  >- (gvs[o1_fn_shape_def] >> metis_tac[dret_runtime_reflect])
  >- metis_tac[fmp_lower_function_label_origin]
  >- metis_tac[lower_dload_runtime_reflect]
  >- metis_tac[make_ssa_current_fn_runtime_reflect]
  >- (drule simplify_cfg_runtime_reflect >> gvs[])
  >- metis_tac[sue_runtime_reflect]
QED

Theorem pre_walk_runtime_reflect:
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit s =
    SOME (unit',s') /\ o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s ==>
  ((?fn i. MEM fn unit'.cu_context.ctx_functions /\ MEM i (fn_insts fn) /\
           MEM (Label "runtime_begin") i.inst_operands) ==>
   (?fn i. MEM fn unit.cu_context.ctx_functions /\ MEM i (fn_insts fn) /\
           MEM (Label "runtime_begin") i.inst_operands))
Proof
  strip_tac >> drule o1_pre_walk_runs >> strip_tac >>
  `o1_ctx_shape mid.cu_context /\ unit_labels_wf mid /\ ir_supply_inst_ok t` by
    (mp_tac (Q.INST [`rp` |-> `rp`, `pass` |-> `CFP_Simple VP_SimplifyCFG`,
       `u` |-> `unit`, `u'` |-> `mid`, `s'` |-> `t`] mapped_pass_stage) >>
     simp[o1_contract_simplify_cfg_pre_walk] >> metis_tac[]) >>
  `ALL_DISTINCT (unit_label_namespace mid)` by
    metis_tac[unit_labels_wf_namespace] >>
  `!pass a b sa sb.
     o1_step_contract rp pass /\
     run_mapped_functions rp pass a sa = SOME (b,sb) /\
     o1_ctx_shape a.cu_context /\ ALL_DISTINCT (unit_label_namespace a) /\
     ir_supply_inst_ok sa ==>
     ((?fn. MEM fn b.cu_context.ctx_functions /\
       ?i. MEM i (fn_insts fn) /\ MEM (Label "runtime_begin") i.inst_operands) ==>
      (?fn. MEM fn a.cu_context.ctx_functions /\
       ?i. MEM i (fn_insts fn) /\ MEM (Label "runtime_begin") i.inst_operands))` by
    (rpt gen_tac >> strip_tac >>
     match_mp_tac (BETA_RULE (Q.INST [`s` |-> `sa`, `s'` |-> `sb`, `P` |-> `\fn. ?i. MEM i (fn_insts fn) /\
       MEM (Label "runtime_begin") i.inst_operands`] run_mapped_functions_reflect)) >>
     metis_tac[configured_runtime_reflect]) >>
  first_assum (qspecl_then [`CFP_Simple VP_SimplifyCFG`, `unit`, `mid`, `s`, `t`] mp_tac) >>
  simp[o1_contract_simplify_cfg_pre_walk] >> strip_tac >>
  first_x_assum (qspecl_then [`CFP_Simple VP_DretDesugar`, `mid`, `unit'`, `t`, `s'`] mp_tac) >>
  simp[o1_contract_dret_desugar_pre_walk] >> metis_tac[]
QED

Theorem walk_runtime_reflect:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  reachable_fcg_acyclic unit.cu_context fcg /\
  ALL_DISTINCT (unit_label_namespace unit) /\
  run_callee_first rp o1_fn_passes (fcg_postorder fcg entry)
    (prune_unit_fcg_unreachable unit fcg) s = SOME (unit',s') /\
  ir_supply_inst_ok s /\ EVERY (o1_fn_row 0) unit.cu_context.ctx_functions ==>
  ((?fn i. MEM fn unit'.cu_context.ctx_functions /\ MEM i (fn_insts fn) /\
           MEM (Label "runtime_begin") i.inst_operands) ==>
   (?fn i. MEM fn unit.cu_context.ctx_functions /\ MEM i (fn_insts fn) /\
           MEM (Label "runtime_begin") i.inst_operands))
Proof
  strip_tac >> drule_all o1_ctx_shape_prune >> strip_tac >>
  drule_all o1_walk_callee_first >> strip_tac >>
  `EVERY (o1_fn_row 0)
    (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions` by
    metis_tac[o1_prune_every] >>
  fs[run_callee_first_def] >>
  mp_tac (Q.INST [`R` |-> `o1_fn_row`, `passes` |-> `o1_fn_passes`,
    `unit` |-> `prune_unit_fcg_unreachable unit fcg`,
    `names` |-> `fcg_postorder fcg entry`, `P` |-> `\fn. ?i. MEM i (fn_insts fn) /\
                      MEM (Label "runtime_begin") i.inst_operands`]
    run_named_fn_schedules_reflect) >>
  simp[o1_fn_passes_steps, o1_step_contracts_from_rows] >>
  impl_tac >- metis_tac[configured_runtime_reflect] >>
  simp[MEM_prune_unit_fcg_unreachable_functions] >> metis_tac[]
QED

Theorem o1_pipeline_runtime_reference_reflects:
  !rpolicy unit out.
  o1_pipeline rpolicy unit = SOME out /\ o1_source_unit_ok unit /\
  unit_entry_no_params unit /\ unit_defs_reach_uses unit /\
  unit_fmp_unsealed unit ==>
  ((?fn inst. MEM fn out.po_unit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) /\
              MEM (Label "runtime_begin") inst.inst_operands) ==>
   (?fn inst. MEM fn unit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) /\
              MEM (Label "runtime_begin") inst.inst_operands))
Proof
  rpt gen_tac >> strip_tac >> fs[o1_pipeline_def] >>
  drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by
    metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)` by
    simp[irSupplyTheory.init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  `ALL_DISTINCT (unit_label_namespace pre)` by
    metis_tac[unit_labels_wf_namespace] >>
  strip_tac >>
  `?fn i. MEM fn pre.cu_context.ctx_functions /\ MEM i (fn_insts fn) /\
          MEM (Label "runtime_begin") i.inst_operands` by
    (mp_tac (Q.INST [`unit` |-> `pre`, `rp` |-> `rpolicy`,
       `fcg` |-> `fcg_analyze pre.cu_context`, `unit'` |-> `out.po_unit`,
       `s` |-> `t`, `s'` |-> `t'`] walk_runtime_reflect) >>
     simp[] >> metis_tac[]) >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `unit'` |-> `pre`,
     `s` |-> `init_ir_supply unit`, `s'` |-> `t`] pre_walk_runtime_reflect) >>
  simp[] >> metis_tac[]
QED
