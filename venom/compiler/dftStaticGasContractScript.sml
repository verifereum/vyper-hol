(* A single reading witness for actual-frame DFT simulation and abort requests. *)
Theory dftStaticGasContract
Ancestors
  dftStaticContextSim dftStaticRequestSim dftGasRequestContract
  dftGasRequestRel dftContractGas dftGasOracleFromList dftGasOracleToList
  dftGasOracleSim dftGasOracleDefs o1RequestContract o1PassContract o1PassLift
  unitShapeDefs dftRunRel dftDefs dftScheduleOrder dftWf venomExecSemantics
  venomState list venomRetProps passSimulationDefs venomInst o1StaticAbortDefs

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
