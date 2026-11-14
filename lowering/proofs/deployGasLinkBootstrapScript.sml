(* Bootstrap the deployment gas mask from the raw witness's exit arm. *)
Theory deployGasLinkBootstrap
Ancestors
  e2eDeployAtMarks deployUnitExitSafe ctorDeployMemoryFrontier ctorDeployDefs
  ctorDeployShape ctorDeployDead o1PipelineCorrect o1PassContract
  fragGasOrigin fragGasOriginPtr gasSummary vyperStorageFootprint

(* The all-dead witness's exit arm bootstraps the output invariant before
   selecting a gas mask or a source filling. *)
Theorem deploy_unit_exit_pipeline:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es
   vs func sites marks src obs result.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!D. dead_wf D ==>
       raw_unit_memory_ok dunit.cu_context vs /\
       ptr_discipline (imm_len tops) dunit.cu_context vs /\
       taint_within D dunit.cu_context vs /\
       mem_inv dload_offset_ok dunit.cu_context vs /\
       mem_inv dload_headroom_ok dunit.cu_context vs ==>
       ctx_sim D dunit.cu_context dout.po_unit.cu_context vs
         (deploy_entry_state prog cplan tops es) /\
       o1_lowered_inv dout.po_unit.cu_context
         (deploy_entry_state prog cplan tops es)) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__deploy" /\
    exit_result result /\
    storage_trace_domain (deploy_evaluation_context tops am tx)
      (initial_state am []) obs /\
    gas_origin_path T sites dunit.cu_context func
      (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                  vs_inst_idx := 0 |>) marks result /\
    (!H. valid_horizon (deploy_evaluation_context tops am tx)
           (initial_state am []) H obs ==>
       deploy_venom_result_rel H tops runtime_bc tx src result /\
       !fuel. ptr_safe_blocks (deploy_dead H tops runtime_bc am tx)
         (imm_len tops) fuel dunit.cu_context func [] FEMPTY entry_taint
         (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                     vs_inst_idx := 0 |>)) ==>
    o1_lowered_inv dout.po_unit.cu_context
      (deploy_entry_state prog cplan tops es) /\
    ?fuel. terminates (run_context fuel dout.po_unit.cu_context
      (deploy_entry_state prog cplan tops es))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_entry_facts >> strip_tac >>
  drule_all deploy_unit_run_entry >> strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule o1_source_unit_ok_no_dalloca >> strip_tac >>
  drule_all deploy_unit_exit_arm_runs >> strip_tac >>
  drule_all deploy_selected_memory >> strip_tac >>
  qabbrev_tac `H = storage_trace_horizon obs` >>
  `ctx_sim (deploy_dead H tops runtime_bc am tx) dunit.cu_context
     dout.po_unit.cu_context vs (deploy_entry_state prog cplan tops es) /\
   o1_lowered_inv dout.po_unit.cu_context
     (deploy_entry_state prog cplan tops es)` by
    (qpat_x_assum `!D. dead_wf D ==> _`
       (qspec_then `deploy_dead H tops runtime_bc am tx` mp_tac) >>
     impl_tac >- simp[deploy_dead_wf] >>
     impl_tac >- fs[Abbr `H`] >> simp[]) >>
  simp[] >>
  `terminates (run_context fuel dunit.cu_context vs)` by
    metis_tac[deploy_venom_result_rel_terminates] >>
  metis_tac[ctx_sim_def, dead_result_rel_terminates]
QED

