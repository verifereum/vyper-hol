(* Conditional composition: no use of the family admissions or their consumer. *)
Theory calldataIdentityRevertCompose
Ancestors
  e2eProducers e2eEntry e2eDefs o1PipelineCorrect o1PassContract
  loweringCalldataCorrect vyperLoweringCorrect loweringShapeSource
  loweringShapeProps loweringMemCorrect supportedProgram
  codegenCorrectness contextCodegenRel immutableCodeLayout
  unitShapeDefs unitTransformDefs passSimulationDefs lowerDloadDefs
  fragGasPathMem ptrDiscipline venomExecSemantics
  loweringStateRelDefs compileVyper finite_map list

Theorem calldata_identity_reverts_from_suppliers:
  (!tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs
    ==>
    ?func s G' tn'.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      s.vs_returndata = [] /\
      (?fuel. run_context fuel unit.cu_context vs = Abort Revert_abort s) /\
      gas_path_mem unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (Abort Revert_abort s) /\
      (!D. gas_path_ptr D 0 unit.cu_context func [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0 |>) 0 G' tn' (Abort Revert_abort s)) /\
      (!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY entry_taint
                  (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                              vs_inst_idx := 0 |>))) /\
  (!tops rpolicy unit out am tx vs fuel s.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_run_state_ok vs /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs /\
    run_context fuel out.po_unit.cu_context vs = Abort Revert_abort s
    ==>
    s.vs_returndata = []) ==>
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    calldata_dispatch tops
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) = NONE
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       ?lgs. frame_outcome es r es' (SOME Reverted) [] lgs)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "raw_revert")
                            (mk_asm "empty_revert")) >>
  rpt gen_tac >> strip_tac >>
  drule compile_vyper_runtime_phases >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qpat_x_assum `runtime_bc = assemble _` SUBST_ALL_TAC >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `initial_venom_state_rel tops am tx (entry_venom_state prog cplan es)` by
    (irule entry_venom_state_initial_venom_state_rel >> simp[]) >>
  `initial_ctx_rel cplan prog out.po_unit.cu_context
     (entry_venom_state prog cplan es) es` by
    (irule entry_venom_state_initial_ctx_rel >> metis_tac[]) >>
  `code_layout_valid (entry_venom_state prog cplan es)` by
    (irule generated_entry_code_layout_shape >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `initial_venom_state_rel tops am tx vs` >>
  `vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs.vs_call_ctx.cc_calldata =
     buffer_to_list (FST (HD es.contexts)).msgParams.data` by
    simp[Abbr `vs`, entry_venom_state_def] >>
  `source_deployment_rel tops am tx` by fs[call_state_rel_def] >>
  `o1_run_state_ok vs` by
    (simp[o1_run_state_ok_def, Abbr `vs`,
          entry_venom_state_o1_initial_state_ok] >>
     gvs[entry_venom_state_def, call_state_rel_def]) >>
  `EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
   fixed_region_reserved 0 unit.cu_context` by
    (drule lower_vyper_runtime_unit_raw_defaults >>
     simp[fixed_region_reserved_def]) >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >>
     simp[staticLayoutDefsTheory.reserved_intervals_wf_def]) >>
  suspend "pipeline_and_codegen"
QED

Resume calldata_identity_reverts_from_suppliers[pipeline_and_codegen]:
  qabbrev_tac `D0 = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                       d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf D0` by simp[Abbr `D0`, dead_wf_def] >>
  qspecl_then [`D0`, `0`] mp_tac run_venom_pipeline_correct >>
  disch_then drule_all >> strip_tac >>
  `initial_venom_state_rel tops am tx vs_in /\
   vs_in.vs_call_ctx = vs.vs_call_ctx /\ code_layout_valid vs_in` by
    (qpat_x_assum `gas_variant _ _` mp_tac >>
     simp[gas_variant_def] >> strip_tac >>
     qpat_x_assum `vs = _` SUBST_ALL_TAC >>
     gvs[initial_venom_state_rel_def, venom_env_rel_def,
         code_layout_valid_def]) >>
  `calldata_dispatch tops vs_in.vs_call_ctx.cc_calldata = NONE` by simp[] >>
  asm "raw_revert" (drule_then mp_tac) >>
  disch_then drule_all >> strip_tac >>
  `~ctx_has_dalloca unit.cu_context` by metis_tac[o1_source_unit_ok_no_dalloca] >>
  drule_all lower_vyper_runtime_unit_reverts_memory_ok >> strip_tac >>
  `taint_within D0 unit.cu_context vs_in` by
    simp[Abbr `D0`, taint_within_def] >>
  `mem_inv dload_headroom_ok unit.cu_context vs_in` by
    (irule lower_vyper_runtime_unit_dload_headroom_ok >> metis_tac[]) >>
  `ctx_sim D0 unit.cu_context out.po_unit.cu_context vs_in vs /\
   o1_lowered_inv out.po_unit.cu_context vs` by metis_tac[] >>
  `terminates (run_context fuel unit.cu_context vs_in)` by
    simp[terminates_def] >>
  qpat_x_assum `ctx_sim _ _ _ _ _`
    (mp_tac o Q.SPEC `fuel` o REWRITE_RULE [ctx_sim_def]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `?s'. run_context fuel' out.po_unit.cu_context vs = Abort Revert_abort s'` by
    (qpat_x_assum `dead_result_rel _ _ _` mp_tac >>
     Cases_on `run_context fuel' out.po_unit.cu_context vs` >>
     simp[dead_result_rel_def]) >>
  `s'.vs_returndata = []` by
    (asm "empty_revert" (drule_then mp_tac) >> metis_tac[]) >>
  drule_all o1_pipeline_memory_obligations >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  `?r es'. run_call es = SOME (r, es') /\
     (frame_resource_starved es r es' \/
      venom_frame_rel es r es' (run_context fuel' out.po_unit.cu_context vs))` by
    (irule codegen_correct >> metis_tac[]) >>
  qexistsl_tac [`r`, `es'`] >> gvs[venom_frame_rel_def] >> metis_tac[]
QED

Finalise calldata_identity_reverts_from_suppliers
