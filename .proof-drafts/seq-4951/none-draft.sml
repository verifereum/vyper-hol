Theorem vyper_call_reverts_asm_opt:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    calldata_dispatch tops
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) = NONE
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       ?lgs. frame_outcome es r es' (SOME Reverted) [] lgs)
Proof
  rpt strip_tac >>
  drule compile_vyper_runtime_phases_asm_opt >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qpat_x_assum `runtime_bc = assemble _` SUBST_ALL_TAC >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `assemble prog <> []` by
    metis_tac[codegenAsmProgOkTheory.codegen_assembly_nonempty] >>
  drule compile_vyper_runtime_nonempty_asm_opt >> strip_tac >>
  (* The Venom side runs on es's entry state with the unoptimized layout. *)
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`] mp_tac
    opt_entry_initial_venom_state_rel >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`, `out.po_unit`]
    mp_tac opt_entry_codegen_asm_entry_rel >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`, `out.po_unit`]
    mp_tac opt_entry_asm_frame_rel >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`, `rpolicy`,
               `out.po_unit`] mp_tac opt_entry_code_layout_valid >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`,
               `opt_entry_state prog prog' cplan es`] mp_tac opt_entry_fields >>
  impl_tac >- simp[] >> strip_tac >>
  qabbrev_tac `vs = opt_entry_state prog prog' cplan es` >>
  (* The Venom run sees the unoptimized code: run the source side on txp. *)
  qabbrev_tac `txp = tx with code := vs.vs_code` >>
  `source_typing_ok tops am txp` by
    (simp[Abbr `txp`] >> irule source_typing_ok_code_update >>
     drule code_layout_valid_code_length >> simp[]) >>
  `source_deployment_rel tops am txp` by
    (simp[Abbr `txp`, source_deployment_rel_code_update] >>
     fs[call_state_rel_def]) >>
  `o1_run_state_ok vs` by fs[o1_run_state_ok_def] >>
  `EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
   fixed_region_reserved 0 unit.cu_context` by
    (drule lower_vyper_runtime_unit_raw_defaults >>
     simp[fixed_region_reserved_def]) >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >>
     simp[staticLayoutDefsTheory.reserved_intervals_wf_def]) >>
  (* A revert's dead bytes don't matter: take every byte dead. *)
  qabbrev_tac `D0 = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                       d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf D0` by simp[Abbr `D0`, dead_wf_def] >>
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`,
                  `rpolicy`, `out.po_unit`] mp_tac opt_entry_data_section_bound >>
     impl_tac >- simp[] >> simp[Abbr `vs`]) >>
  drule_all lower_vyper_runtime_unit_sym_src_ok >> strip_tac >>
  drule_all o1_pipeline_code_end_offset_ok >> strip_tac >>
  `initial_venom_state_rel tops am txp vs_in` by
    (irule gas_variant_initial_venom_state_rel >> qexists_tac `vs` >> simp[]) >>
  `vs_in.vs_call_ctx = vs.vs_call_ctx` by
    (irule gas_variant_call_ctx >> simp[]) >>
  `calldata_dispatch tops vs_in.vs_call_ctx.cc_calldata = NONE` by simp[] >>
  (* S1: the input run reverts. *)
  `?fuel s. run_context fuel unit.cu_context vs_in = Abort Revert_abort s` by
    (drule lower_vyper_runtime_unit_reverts >>
     disch_then (qspecl_then [`am`, `txp`, `vs_in`] mp_tac) >>
     impl_tac >- simp[] >> metis_tac[]) >>
  (* S3: the input memory facts. *)
  `code_layout_valid vs_in` by
    (irule gas_variant_code_layout_valid >> qexists_tac `vs` >> asm_rewrite_tac[]) >>
  drule o1_source_unit_ok_no_dalloca >> strip_tac >>
  drule lower_vyper_runtime_unit_reverts_memory_ok >>
  disch_then (qspecl_then [`am`, `txp`, `vs_in`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rpt (qpat_x_assum `code_layout_valid vs_in ==> _` mp_tac >>
       impl_tac >- first_assum ACCEPT_TAC >> strip_tac) >>
  `taint_within D0 unit.cu_context vs_in` by
    simp[Abbr `D0`, taint_within_def] >>
  `mem_inv dload_headroom_ok unit.cu_context vs_in` by
    (irule lower_vyper_runtime_unit_dload_headroom_ok >> metis_tac[]) >>
  `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
     s.vs_code = vs_in.vs_code /\ s.vs_data_section = vs_in.vs_data_section)
     unit.cu_context vs_in` by
    (irule lower_vyper_runtime_unit_dload_in_section >> metis_tac[]) >>
  qpat_x_assum `raw_unit_memory_ok _ vs_in /\ _ ==> _` mp_tac >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  (* S4: the output run reverts too, with no data. *)
  `terminates (run_context fuel unit.cu_context vs_in)` by
    simp[terminates_def] >>
  qpat_x_assum `ctx_sim _ _ _ _ _` mp_tac >>
  simp[ctx_sim_def] >> disch_then drule >> strip_tac >>
  rename1 `dead_result_rel D0 _ (run_context fuel' _ vs)` >>
  `?s'. run_context fuel' out.po_unit.cu_context vs = Abort Revert_abort s'` by
    (qpat_x_assum `dead_result_rel _ _ _` mp_tac >>
     Cases_on `run_context fuel' out.po_unit.cu_context vs` >>
     simp[dead_result_rel_def]) >>
  `s'.vs_returndata = []` by
    (qspecl_then [`tops`, `rpolicy`, `unit`, `out`, `am`, `txp`, `vs`,
                  `fuel'`, `s'`] mp_tac o1_pipeline_reverts_empty >>
     impl_tac >- simp[] >> simp[]) >>
  (* S5-S7 through the optimized assembly. *)
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  `label_flow_ok out.po_unit.cu_context` by
    (irule o1_pipeline_label_flow_ok >> metis_tac[]) >>
  `sym_unit_static_ok out.po_unit` by
    (irule o1_pipeline_sym_unit_static_ok >> metis_tac[]) >>
  qspecl_then [`fuel'`, `rpolicy`, `out.po_unit`, `cplan`, `prog`, `prog'`,
               `raw_reachable vs`, `vs`, `es`] mp_tac codegen_correct_asm_opt >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  qexistsl_tac [`r`, `es'`] >> gvs[venom_frame_rel_def] >> metis_tac[]
QED
