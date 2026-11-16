Theory o1SymStaticPipeline
Ancestors
  o1LabelFlowStaticContracts
  o1LabelReadiness o1LabelStages o1SymStaticSchedule
  o1PipelineCorrect o1PipelineCompose o1ComposeSupport
  venomPassDispatcher venomFnScheduleRunner fmpStepBridge
  o1PassContract venomFnScheduleRunnerProps o1DretDesugarContract
  o1ContractSimplifyCfg o1FnScheduleDecompHelpers fcgPruning
  venomPipelineRunner venomInst list rich_list

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
  impl_tac
  >- (rpt gen_tac >> strip_tac >>
      `MEM fn observed.cu_context.ctx_functions` by
        metis_tac[fn_pass_step_def, lookup_unique_function_member] >>
      `o1_fn_shape observed.cu_context fn` by
        gvs[o1_ctx_shape_def, EVERY_MEM] >>
      metis_tac[fn_pass_step_no_runtime_begin]) >>
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
  metis_tac[o1_pre_walk_no_runtime_begin]
QED
