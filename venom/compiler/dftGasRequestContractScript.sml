(* One gas-reading witness for both the ordinary simulation and its
 * request companion.  The event request simulation is deliberately a
 * premise here: scheduling and fuel proofs discharge it independently.
 *)
Theory dftGasRequestContract
Ancestors
  dftGasRequestRel dftContractGas dftGasOracleFromList dftGasOracleToList
  dftGasOracleSim dftGasOracleInv dftGasOracleDefs contextRawReachable
  o1RequestContract o1PassContract o1PassLift unitMemInv unitShapeDefs
  dftRunRel dftDefs dftScheduleOrder dftWf venomExecSemantics venomState list
  venomRetProps passSimulationDefs stackPlanGen venomInst dftCorrectnessFinal

Theorem dft_ctx_sim_rq_gas_conditional:
  (!orc fuel s.
    ctx_labels_bound C s.vs_labels /\ o1_run_state_ok s /\
    terminates (ev_context orc fuel C s) ==>
    dft_rq_res_rel D (ev_context orc fuel C s) (ev_context orc fuel C' s)) /\
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ C'.ctx_global_reserved = C.ctx_global_reserved /\
  o1_ctx_shape C /\ dead_wf D /\
  ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' ==>
  ?vs. gas_variant vs vs' /\ ctx_sim D C C' vs vs' /\
       ctx_abort_rq D C C' vs vs' /\
       (o1_lowered_inv C vs ==> o1_lowered_inv C' vs')
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
      simp[] >> irule dft_ev_context_sim >> simp[] >>
      metis_tac[gas_res_rel_terminates]) >>
  conj_tac
  >- (rw[ctx_abort_rq_def] >>
      qpat_x_assum `!fuel. gas_res_rel (run_context fuel C _) _`
        (qspec_then `fuel` mp_tac) >>
      simp[] >> disch_tac >>
      `terminates (ev_context orc fuel C vs')` by
        (irule gas_res_rel_terminates >> goal_assum (drule_at Any) >>
         simp[terminates_def]) >>
      `dft_rq_res_rel D (ev_context orc fuel C vs')
                         (ev_context orc fuel C' vs')` by metis_tac[] >>
      qpat_x_assum `!orc fuel s. _ ==> dft_rq_res_rel _ _ _` kall_tac >>
      drule (cj 1 gas_res_rel_abort_requests) >> strip_tac >>
      gvs[dft_rq_res_rel_abort] >>
      qpat_x_assum `!fuel. gas_res_rel (run_context fuel C' _) _`
        (qspec_then `fuel` mp_tac) >>
      simp[gas_res_rel_abort] >> strip_tac >>
      qexists_tac `fuel` >>
      metis_tac[gas_variant_requests]) >>
  suspend "lowered"
QED

Resume dft_ctx_sim_rq_gas_conditional[lowered]:
  rw[o1_lowered_inv_def] >> qexists_tac `eom` >>
  conj_tac >- gvs[max_live_eom_def, collect_fn_eoms_dft] >>
  gvs[mem_inv_raw_reachable] >>
  `!p d fn inst t. ev_reachable orc vs' C p d fn inst t ==>
     static_mem_ok eom C fn inst t` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `!p d fn inst t. ev_reachable orc vs' C' p d fn inst t ==>
     static_mem_ok eom C' fn inst t` by
    (mp_tac (Q.INST [`s:venom_state` |-> `vs'`] dft_ev_lowered_inv) >>
     simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  conj_tac
  >- (simp[lookup_function_map, dft_fn_entry_label] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Finalise dft_ctx_sim_rq_gas_conditional
