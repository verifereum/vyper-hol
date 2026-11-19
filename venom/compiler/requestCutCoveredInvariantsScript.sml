Theory requestCutCoveredInvariants
Ancestors
  requestCutReplaySuffix dftContractGas o1ContractCfgNorm
  o1PassContract unitMemInv unitTransformDefs dftGasOracleDefs
  venomState venomInst venomPassSchedule

(* Combine the two native visit covers with the pre-DFT cut facts. *)
Theorem request_cut_covered_invariants:
  ctx_pass_stage rp (CFP_Simple VP_DFT) dft_view C7 C8 /\ o1_pre 7 C7 C8 /\
  ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) cfg_view C8 C9 /\
  o1_ctx_shape C7 /\ EVERY wf_ssa C7.ctx_functions /\ o1_ctx_shape C8 /\
  ctx_labels_bound C7 vs0.vs_labels /\ o1_initial_state_ok vs0 /\
  vs0.vs_fmp = vs0.vs_initial_fmp /\ code_layout_valid vs0 /\
  (!fn inst t. raw_reachable vs0 C8 fn inst t /\ LENGTH t.vs_requests <= k /\
    ~in_static_abort_prefix fn t ==>
    ?p d. ev_reachable orc vs0 C8 p d fn inst (t with vs_gas_readings := vs0.vs_gas_readings)) /\
  (!p d fn inst s. ev_reachable orc vs0 C7 p d fn inst s /\ LENGTH s.vs_requests <= k ==>
    ?ws. raw_reachable source C7 fn inst (s with vs_gas_readings := ws)) /\
  mem_inv (\ctx fn inst s. LENGTH s.vs_requests <= k ==>
    lowered_mem_fact eom ctx fn inst s) C7 source /\
  (guarded ==> code_end_offset_ok
    (\ctx fn inst s. raw_reachable source ctx fn inst s /\ LENGTH s.vs_requests <= k) C7) ==>
  mem_inv (\ctx fn inst t. LENGTH t.vs_requests <= k /\ ~in_static_abort_prefix fn t ==>
    lowered_mem_ok eom (w2n t.vs_initial_fmp) ctx fn inst t) C9 vs0 /\
  (guarded ==> code_end_offset_ok (\ctx fn inst t. raw_reachable vs0 ctx fn inst t /\
    LENGTH t.vs_requests <= k /\ ~in_static_abort_prefix fn t) C9)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `mem_inv _ C7 source`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [mem_inv_raw_reachable]) >>
  `!p d fn inst s. ev_reachable orc vs0 C7 p d fn inst s /\
     LENGTH s.vs_requests <= k ==> in_static_abort_prefix fn s \/
     lowered_mem_fact eom C7 fn inst s` by
    (qx_genl_tac [`p7`, `d7`, `fn7`, `i7`, `s7`] >> strip_tac >> disj2_tac >>
     qpat_assum `!p d fn inst s. ev_reachable orc vs0 C7 p d fn inst s /\ LENGTH s.vs_requests <= k ==> _`
       (drule_all_then strip_assume_tac) >>
     `LENGTH (s7 with vs_gas_readings := ws).vs_requests <= k` by simp[] >>
     `lowered_mem_fact eom C7 fn7 i7 (s7 with vs_gas_readings := ws)` by
       metis_tac[] >>
     fs[lowered_mem_fact_gas_readings]) >>
  mp_tac request_cut_dft_cfg_invariants >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[])) >>
  disch_then ACCEPT_TAC
QED
