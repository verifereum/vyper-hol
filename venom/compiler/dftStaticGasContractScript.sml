(* A single reading witness for actual-frame DFT simulation and abort requests. *)
Theory dftStaticGasContract
Ancestors
  dftStaticContextSim dftStaticRequestSim dftGasRequestContract
  dftGasRequestRel dftContractGas dftGasOracleFromList dftGasOracleToList
  dftGasOracleSim dftGasOracleDefs o1RequestContract o1PassContract o1PassLift
  unitShapeDefs dftRunRel dftDefs dftScheduleOrder dftWf venomExecSemantics
  venomState list venomRetProps passSimulationDefs venomInst
  o1StaticAbortDefs dftGasToListAbort dftStaticMemoryInv
  unitMemInv stackPlanGen dftCorrectnessFinal

Theorem static_mem_ok_abort_gas_readings[simp]:
  static_mem_ok_abort eom ctx fn inst (t with vs_gas_readings := ws) <=>
  static_mem_ok_abort eom ctx fn inst t
Proof
  simp[staticAbortMemDefsTheory.static_mem_ok_abort_def,
       staticAbortDefsTheory.in_static_abort_prefix_def]
QED

Theorem ev_reachable_static_write_exhalt:
  EVERY wf_function ctx.ctx_functions /\
  ev_reachable orc s ctx p d fn inst t /\
  MEM inst.inst_opcode [SSTORE; TSTORE; LOG] /\
  t.vs_call_ctx.cc_static /\
  IS_SOME (eval_operands inst.inst_operands t) ==>
  !fuel. terminates (ev_context orc fuel ctx s) ==>
    ?u. ev_context orc fuel ctx s = Abort ExHalt_abort u
Proof
  strip_tac >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE` by gvs[] >>
  `ev_step orc p d 0 ctx inst t =
     Abort ExHalt_abort (halt_state (set_returndata [] t))` by
    (irule dftStaticAbortCompletionTheory.inv_reached_static_write_fails >>
     simp[]) >>
  `step_inst_base inst t =
     Abort ExHalt_abort (halt_state (set_returndata [] t))` by
    (qpat_x_assum `ev_step _ _ _ 0 _ _ _ = _` mp_tac >>
     simp[Once ev_step_def, Once step_inst_def]) >>
  metis_tac[ev_reachable_primitive_abort]
QED

Theorem dft_ctx_sim_rq_gas_static_forward:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ C'.ctx_global_reserved = C.ctx_global_reserved /\
  o1_ctx_shape C /\ dead_wf D /\
  ctx_labels_bound C vs'.vs_labels /\ o1_initial_state_ok vs' /\
  vs'.vs_fmp = vs'.vs_initial_fmp /\ code_layout_valid vs' /\
  (vs'.vs_call_ctx.cc_static ==>
    !fn inst l. MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode = CODECOPY /\ MEM (Label l) inst.inst_operands ==>
      l IN FDOM vs'.vs_labels) ==>
  ?vs. gas_variant vs vs' /\ ctx_sim D C C' vs vs' /\
       ctx_abort_rq D C C' vs vs'
Proof
  strip_tac >>
  `C'.ctx_functions = MAP dft_fn C.ctx_functions` by
    metis_tac[dft_ctx_functions_map] >>
  drule dft_ctx_block_ids_distinct >> strip_tac >>
  drule_all o1_ctx_shape_wf_functions >> strip_tac >>
  drule_all dft_ctx_wf_functions >> strip_tac >>
  mp_tac (Q.INST [`ctx:venom_context` |-> `C'`, `s:venom_state` |-> `vs'`]
            gas_oracle_from_list) >>
  (impl_tac >- simp[]) >> strip_tac >>
  mp_tac (Q.INST [`ctx:venom_context` |-> `C`, `s:venom_state` |-> `vs'`]
            gas_oracle_to_list) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `run_context _ C (vs' with vs_gas_readings := rds)` >>
  qexists_tac `vs' with vs_gas_readings := rds` >>
  conj_tac >- simp[gas_variant_def, venom_state_component_equality] >>
  conj_tac
  >- (rw[ctx_sim_def] >> qexists_tac `fuel` >>
      irule gas_dft_dead_result >>
      simp[run_context_not_ok, o1_ctx_shape_run_context_no_intret] >>
      qexistsl [`ev_context orc fuel C vs'`, `ev_context orc fuel C' vs'`] >>
      simp[] >> irule dft_ev_context_sim_static >> simp[] >>
      metis_tac[gas_res_rel_terminates]) >>
  rw[ctx_abort_rq_def] >>
      qpat_x_assum `!fuel. gas_res_rel (run_context fuel C _) _`
        (qspec_then `fuel` mp_tac) >>
      simp[] >> disch_tac >>
      `terminates (ev_context orc fuel C vs')` by
        (irule gas_res_rel_terminates >> goal_assum (drule_at Any) >>
         simp[terminates_def]) >>
      `dft_rq_res_rel D (ev_context orc fuel C vs')
                         (ev_context orc fuel C' vs')` by
        (irule dft_ev_context_sim_rq_static >> simp[] >> metis_tac[]) >>
      drule (cj 1 gas_res_rel_abort_requests) >> strip_tac >>
      gvs[dft_rq_res_rel_abort] >>
      qpat_x_assum `!fuel. gas_res_rel (run_context fuel C' _) _`
        (qspec_then `fuel` mp_tac) >>
      simp[gas_res_rel_abort] >> strip_tac >>
      qexists_tac `fuel` >>
      metis_tac[gas_variant_requests]
QED

Theorem dft_ctx_sim_gas_static_abort:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ C'.ctx_global_reserved = C.ctx_global_reserved /\
  o1_ctx_shape C /\
  ctx_labels_bound C vs'.vs_labels /\ o1_initial_state_ok vs' /\
  vs'.vs_fmp = vs'.vs_initial_fmp /\ code_layout_valid vs' /\
  (vs'.vs_call_ctx.cc_static ==>
    !fn inst l. MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode = CODECOPY /\ MEM (Label l) inst.inst_operands ==>
      l IN FDOM vs'.vs_labels) ==>
  ?vs. gas_variant vs vs' /\ ctx_sim_fuel I D C C' vs vs' /\
       (o1_lowered_inv C vs ==>
          o1_lowered_inv C' vs' \/
          (o1_lowered_inv_abort C' vs' /\
           !fuel. terminates (run_context fuel C vs) ==>
                  ?u. run_context fuel C vs = Abort ExHalt_abort u))
Proof
  strip_tac >>
  `C'.ctx_functions = MAP dft_fn C.ctx_functions` by
    metis_tac[dft_ctx_functions_map] >>
  drule dft_ctx_block_ids_distinct >> strip_tac >>
  drule_all o1_ctx_shape_wf_functions >> strip_tac >>
  drule_all dft_ctx_wf_functions >> strip_tac >>
  mp_tac (Q.INST [`ctx:venom_context` |-> `C'`, `s:venom_state` |-> `vs'`]
            gas_oracle_from_list) >>
  (impl_tac >- simp[]) >> strip_tac >>
  mp_tac (Q.INST [`ctx:venom_context` |-> `C`, `s:venom_state` |-> `vs'`]
            gas_oracle_to_list) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `run_context _ C (vs' with vs_gas_readings := rds)` >>
  qexists_tac `vs' with vs_gas_readings := rds` >>
  conj_tac >- simp[gas_variant_def, venom_state_component_equality] >>
  conj_tac
  >- (rw[ctx_sim_fuel_def] >>
      irule gas_dft_dead_result >>
      simp[run_context_not_ok, o1_ctx_shape_run_context_no_intret] >>
      qexistsl [`ev_context orc fuel C vs'`, `ev_context orc fuel C' vs'`] >>
      simp[] >> irule dft_ev_context_sim_static >> simp[] >>
      metis_tac[gas_res_rel_terminates]) >>
  simp[o1_lowered_inv_def, mem_inv_raw_reachable] >> strip_tac >>
  `max_live_eom C' = SOME eom` by
    gvs[max_live_eom_def, collect_fn_eoms_dft] >>
  `?name fn lbl. C'.ctx_entry = SOME name /\
     lookup_function name C'.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl` by
    (simp[lookup_function_map, dft_fn_entry_label] >> metis_tac[]) >>
  gvs[] >>
  `!p d fn inst t. ev_reachable orc vs' C p d fn inst t ==>
     static_mem_ok eom C fn inst t` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  Cases_on `!p d fn inst t. ev_reachable orc vs' C' p d fn inst t ==>
     static_mem_ok eom C' fn inst t`
  >- (disj1_tac >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >>
      first_x_assum drule >> simp[]) >>
  disj2_tac >> conj_tac
  >- (simp[o1_lowered_inv_abort_def, mem_inv_raw_reachable,
           lookup_function_map, dft_fn_entry_label] >>
      `!p d fn inst t. ev_reachable orc vs' C' p d fn inst t ==>
         static_mem_ok_abort eom C' fn inst t` by
        (mp_tac (Q.INST [`s:venom_state` |-> `vs'`]
                   dft_ev_lowered_inv_static_abort) >>
         simp[] >> impl_tac
         >- (rpt strip_tac >>
             simp[staticAbortMemDefsTheory.static_mem_ok_abort_def] >>
             metis_tac[]) >> simp[]) >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >>
      first_x_assum drule >> simp[]) >>
  qpat_x_assum `~(!p d fn inst t. _)` mp_tac >>
  simp[NOT_FORALL_THM] >> strip_tac >>
  rename1 `~static_mem_ok eom C' badfn inst t` >>
  mp_tac (Q.INST [`s:venom_state` |-> `vs'`, `fn':ir_function` |-> `badfn`]
            dft_ev_static_mem_violation_source_write_available) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  `!fuel. terminates (ev_context orc fuel C vs') ==>
     ?u. ev_context orc fuel C vs' = Abort ExHalt_abort u` by
    (rpt strip_tac >> irule ev_reachable_static_write_exhalt >>
     simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `terminates (ev_context orc fuel C vs')` by
    metis_tac[gas_res_rel_terminates] >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `!fuel. gas_res_rel (run_context fuel C _) _`
    (qspec_then `fuel` mp_tac) >>
  simp[gas_res_rel_def] >>
  Cases_on `run_context fuel C (vs' with vs_gas_readings := rds)` >>
  simp[gas_res_rel_def]
QED
