(* Value-label readiness in the actual generated entry environment. *)
Theory runtimeLabelEntry
Ancestors
  e2eEntry e2eProducers immutableCodeLayout codegen asmIR symbolResolve
  runtimeLabelReadiness o1LabelStages o1PipelineCompose o1ComposeSupport
  o1PassContract o1ContractTheorems o1DretDesugarContract
  o1FnScheduleDecompHelpers
  compileVyper venomPipelineDriver venomPipelineRunner venomFnScheduleRunner irSupply
  fcgPruning venomPassSchedule finite_map list

Theorem generated_entry_code_end_label:
  codegen_assembly policy unit = SOME prog ==>
  IS_SOME (FLOOKUP (entry_venom_state prog cplan es).vs_labels "code_end")
Proof
  strip_tac >> drule codegen_assembly_success_shape >> strip_tac >>
  `?prefix. prog = prefix ++ [AsmDataHeader "code_end"]` by
    metis_tac[APPEND_ASSOC] >>
  gvs[entry_venom_state_frame_fields, immutable_code_end_offset]
QED

Theorem runtime_o1_stage_labels_bound:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy o1_pipeline_spec unit =
    SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\
  unit_fmp_unsealed unit ==>
  ?pre t entry t' stage.
    run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
      (init_ir_supply unit) = SOME (pre,t) /\
    pre.cu_context.ctx_entry = SOME entry /\
    run_callee_first rpolicy o1_fn_passes
      (fcg_postorder (fcg_analyze pre.cu_context) entry)
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
      SOME (out.po_unit,t') /\
    stage 0 =
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
    stage (LENGTH o1_fn_passes) = out.po_unit.cu_context /\
    (!k. k <= LENGTH o1_fn_passes ==>
      o1_ctx_shape (stage k) /\ EVERY (o1_fn_row k) (stage k).ctx_functions) /\
    (!k. k < LENGTH o1_fn_passes ==>
      ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
        (stage k) (stage (SUC k))) /\
    (!vs fn inst l.
      MEM fn (stage 7).ctx_functions /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode = CODECOPY /\ MEM (Label l) inst.inst_operands ==>
      l IN FDOM vs.vs_labels)
Proof
  strip_tac >> drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)` by simp[init_ir_supply_inst_ok] >>
  `!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands` by
    metis_tac[lower_vyper_runtime_unit_no_runtime_begin] >>
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
  strip_tac >> qexistsl_tac [`pre`, `t`, `entry`, `t'`, `stage`] >>
  gvs[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[o1_walk_view_def]) >>
  gen_tac >>
  `7 <= LENGTH o1_fn_passes` by simp[o1_fn_passes_def] >>
  mp_tac (Q.INST [`C` |-> `stage 7`] o1_runtime_codecopy_labels_bound) >>
  impl_tac >- metis_tac[] >> simp[]
QED

