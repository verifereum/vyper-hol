Theory o1SymStaticPipeline
Ancestors
  o1LabelFlowStaticContracts
  o1LabelStages
  o1PipelineCorrect o1PipelineCompose o1ComposeSupport
  venomPassDispatcher venomFnScheduleRunner fmpStepBridge
  o1PassContract venomFnScheduleRunnerProps o1DretDesugarContract
  o1ContractSimplifyCfg o1FnScheduleDecompHelpers fcgPruning
  venomPipelineRunner venomInst list rich_list

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
  strip_tac >> CCONTR_TAC >> fs[] >>
  mp_tac (Q.INST [`unit` |-> `unit`, `unit'` |-> `pre`,
                 `s` |-> `init_ir_supply unit`, `s'` |-> `t`]
    o1_pre_walk_no_runtime_begin) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  `o1_ctx_shape
     (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
   ALL_DISTINCT (unit_label_namespace
     (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)))` by
    metis_tac[o1_ctx_shape_prune, unit_labels_wf_namespace] >>
  `!fn inst.
    MEM fn (prune_unit_fcg_unreachable pre
      (fcg_analyze pre.cu_context)).cu_context.ctx_functions /\
    MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands` by
    (simp[MEM_prune_unit_fcg_unreachable_functions] >> metis_tac[]) >>
  mp_tac (Q.INST [`unit` |-> `pre`,
                 `fcg` |-> `fcg_analyze pre.cu_context`] o1_walk_callee_first) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  `?walk_out. run_named_fn_schedules execute_configured_fn_pass rpolicy
    o1_fn_passes (fcg_postorder (fcg_analyze pre.cu_context) entry)
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
    SOME (out.po_unit,walk_out)` by fs[run_callee_first_def] >>
  drule_at (Pos (el 3))
    (Q.INST [`R` |-> `o1_fn_row`] o1_schedule_stages_no_runtime_begin) >>
  impl_tac
  >- (fs[o1_fn_passes_steps, o1_step_contracts_from_rows, o1_prune_every] >>
      metis_tac[]) >>
  strip_tac >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED
