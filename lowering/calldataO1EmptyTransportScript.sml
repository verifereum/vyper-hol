(* Empty-revert transport, conditional on the raw entry's joint certificate.
   This owner deliberately does not use the admitted raw-entry theorem. *)
Theory calldataO1EmptyTransport
Ancestors
  loweringCalldataCorrect o1PipelineCorrect o1PipelineCompose
  loweringShapeSource ctorDeployRunBounded vyperLoweringCorrect e2eDefs
  o1PassContract ptrDiscipline loweringMemCorrect staticLayoutDefs
  unitMemInv passSimulationDefs

Theorem calldata_o1_empty_from_raw_reverts:
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
                              vs_inst_idx := 0 |>))) ==>
  !tops rpolicy unit out am tx vs fuel s.
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
    s.vs_returndata = []
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  `o1_source_unit_ok unit` by
    (drule supported_program_raw_shape_free_program >> strip_tac >>
     gvs[source_typing_ok_def] >>
     drule_all lower_vyper_runtime_unit_source_unit_ok >> simp[]) >>
  `unit_entry_no_params unit /\ unit_fmp_unsealed unit` by
    metis_tac[lower_vyper_runtime_unit_o1_shape_extras] >>
  `unit_defs_reach_uses unit` by
    metis_tac[lower_vyper_runtime_unit_defs_reach_uses] >>
  qabbrev_tac `D = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                      d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf D` by simp[Abbr `D`, dead_wf_def] >>
  `run_venom_pipeline (K T) (K T) (K T) rpolicy o1_pipeline_spec unit = SOME out`
    by fs[o1_pipeline_def] >>
  drule_all o1_pipeline_sim_revert_empty >> strip_tac >>
  first_x_assum (qspecl_then [`D`, `vs`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `vi` strip_assume_tac) >>
  `o1_run_state_ok vi` by metis_tac[gas_variant_run_state_ok] >>
  `initial_venom_state_rel tops am tx vi /\
   vi.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_x_assum `gas_variant _ _` mp_tac >>
     rw[gas_variant_def] >>
     qpat_x_assum `vs = _` SUBST_ALL_TAC >>
     gvs[initial_venom_state_rel_def, venom_env_rel_def]) >>
  qpat_x_assum `!tops rpolicy unit am tx vs. _`
    (qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vi`] mp_tac) >>
  simp[] >> strip_tac >>
  `~ctx_has_dalloca unit.cu_context` by
    metis_tac[o1_source_unit_ok_no_dalloca] >>
  drule_all lower_vyper_runtime_unit_reverts_memory_ok >> strip_tac >>
  `mem_inv dload_offset_ok unit.cu_context vi` by fs[o1_run_state_ok_def] >>
  `mem_inv dload_headroom_ok unit.cu_context vi` by
    metis_tac[lower_vyper_runtime_unit_dload_headroom_ok] >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >>
     simp[reserved_intervals_wf_def]) >>
  `o1_pre_walk_inv D unit.cu_context vi` by
    (irule o1_source_pre_walk_inv >> simp[] >>
     simp[o1_src_inv_def, raw_unit_memory_ok_mem_inv,
          Abbr `D`, taint_within_def] >>
     conj_tac >- fs[raw_unit_memory_ok_mem_inv] >>
     conj_tac >- (qexists_tac `0` >> simp[]) >>
     irule source_fmp_free >> simp[]) >>
  qpat_x_assum `o1_pre_walk_inv _ _ _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!fuel post. _`
    (qspecl_then [`fuel'`, `s'`] mp_tac) >> simp[] >> strip_tac >>
  `run_context (MAX fuel (cfg_norm_fuel out.po_unit.cu_context fuel'))
     out.po_unit.cu_context vs = Abort Revert_abort s` by
    (irule EQ_TRANS >> irule_at Any run_context_terminates_mono >>
     qexists_tac `fuel` >> simp[terminates_def]) >>
  `run_context (MAX fuel (cfg_norm_fuel out.po_unit.cu_context fuel'))
     out.po_unit.cu_context vs = Abort Revert_abort tpost` by
    (irule EQ_TRANS >> irule_at Any run_context_terminates_mono >>
     qexists_tac `cfg_norm_fuel out.po_unit.cu_context fuel'` >>
     simp[terminates_def]) >>
  gvs[]
QED
