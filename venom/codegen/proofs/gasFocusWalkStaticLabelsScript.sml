(* CODECOPY label readiness along the caller-supplied static O1 walk. *)
Theory gasFocusWalkStaticLabels
Ancestors
  o1PipelineCorrect o1LabelStages o1ComposeSupport o1PipelineCompose
  fcgPruning irSupply finite_map

Theorem focus_walk_static_c7_codecopy_labels:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  (vs0.vs_call_ctx.cc_static ==>
     !fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
               ~MEM (Label "runtime_begin") inst.inst_operands) /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
                  (stage k) (stage (SUC k))) /\
  (!k. k <= 9 ==> o1_ctx_shape (stage k)) ==>
  (vs0.vs_call_ctx.cc_static ==>
     !fn inst l. MEM fn (stage 7).ctx_functions /\ MEM inst (fn_insts fn) /\
                 inst.inst_opcode = CODECOPY /\ MEM (Label l) inst.inst_operands ==>
                 l IN FDOM vs0.vs_labels)
Proof
  simp[o1PipelineCorrectTheory.o1_pipeline_def] >> strip_tac >> disch_tac >>
  drule o1_driver_runs >>
  disch_then (CONJUNCTS_THEN2 assume_tac (assume_tac o CONJUNCT1)) >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)` by simp[init_ir_supply_inst_ok] >>
  `!fn inst. MEM fn pre.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
             ~MEM (Label "runtime_begin") inst.inst_operands` by
    (drule o1_pre_walk_no_runtime_begin >> simp[] >> metis_tac[]) >>
  `!k. k <= 7 ==> !fn inst.
      MEM fn (stage k).ctx_functions /\ MEM inst (fn_insts fn) ==>
      ~MEM (Label "runtime_begin") inst.inst_operands` by
    (Induct >- (simp[MEM_prune_unit_fcg_unreachable_functions] >> metis_tac[]) >>
     strip_tac >>
     `k <= 7 /\ k < 9 /\ k <= 9` by decide_tac >>
     `o1_ctx_shape (stage k)` by simp[] >>
     `ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
        (stage k) (stage (SUC k))` by simp[] >>
     qpat_x_assum `k <= 7 ==> _` mp_tac >> simp[] >> disch_tac >>
     metis_tac[ctx_pass_stage_no_runtime_begin]) >>
  `o1_ctx_shape (stage 7)` by simp[] >>
  first_x_assum (qspec_then `7` mp_tac) >> simp[] >> strip_tac >>
  metis_tac[o1_runtime_codecopy_labels_bound]
QED
