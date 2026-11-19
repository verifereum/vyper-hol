Theory requestCutTerminalInvariants
Ancestors
  requestCutCoveredInvariants requestCutNativeEventCover requestCutNativeAbortVisit
  requestCutAbortBound jointRequestCut frameJointTrace frameJointTransition frameRawProjection dftGasFromListTraceDefs dftContractGas
  dftGasOracleDefs passSimulationDefs o1PassContract unitMemInv venomPassSchedule venomExecSemantics
  contextCodegenRel codegenSymRel staticAbortDefs unitShapeDefs venomInst venomState list

(* A primitive abort bounds the request count at every native visit. *)
Theorem request_cut_abort_invariants:
  EVERY wf_function C.ctx_functions /\
  raw_reachable v C fn inst s /\
  LENGTH s.vs_requests <= k /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = Abort ab post /\
  mem_inv (\ctx fn j t. LENGTH t.vs_requests <= k /\ ~in_static_abort_prefix fn t ==>
    lowered_mem_ok eom (w2n t.vs_initial_fmp) ctx fn j t) C v /\
  (guarded ==> code_end_offset_ok (\ctx fn j t. raw_reachable v ctx fn j t /\
    LENGTH t.vs_requests <= k /\ ~in_static_abort_prefix fn t) C) ==>
  mem_inv (\ctx fn j t. in_static_abort_prefix fn t \/
    lowered_mem_fact eom ctx fn j t) C v /\
  (guarded ==> code_end_offset_ok
    (\ctx fn j t. raw_reachable v ctx fn j t /\ ~in_static_abort_prefix fn t) C)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule raw_reachable_joint_trace >> strip_tac >>
  `!g j t. raw_reachable v C g j t ==> LENGTH t.vs_requests <= k` by
    (rpt strip_tac >> drule_all joint_trace_primitive_abort_request_bound >>
     decide_tac) >>
  fs[mem_inv_raw_reachable, lowered_mem_fact_def, code_end_offset_ok_def] >>
  metis_tac[]
QED

(* When both native DFT runs stop, their agreed traces cover all visits.
   An early C9 primitive abort then turns the request-cut bounds into
   whole-run premises for the static-abort code generator. *)
Theorem request_cut_terminal_invariants:
  ctx_pass_stage rp (CFP_Simple VP_DFT) dft_view C7 C8 /\ o1_pre 7 C7 C8 /\
  ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) cfg_view C8 C9 /\
  o1_ctx_shape C7 /\ EVERY wf_ssa C7.ctx_functions /\ o1_ctx_shape C8 /\
  EVERY wf_function C7.ctx_functions /\ EVERY wf_function C8.ctx_functions /\
  EVERY wf_function C9.ctx_functions /\
  ctx_labels_bound C7 vs0.vs_labels /\ o1_initial_state_ok vs0 /\
  vs0.vs_fmp = vs0.vs_initial_fmp /\ code_layout_valid vs0 /\
  source = (vs0 with vs_gas_readings := filling) /\
  terminates (run_context bound7 C7 source) /\
  trace_agrees orc (trace_context bound7 C7 source) /\
  terminates (run_context bound8 C8 vs0) /\
  trace_agrees orc (trace_context bound8 C8 vs0) /\
  mem_inv (\ctx fn inst s. LENGTH s.vs_requests <= k ==>
    lowered_mem_fact eom ctx fn inst s) C7 source /\
  (guarded ==> code_end_offset_ok
    (\ctx fn inst s. raw_reachable source ctx fn inst s /\ LENGTH s.vs_requests <= k) C7) /\
  joint_trace vs0 C9 q0 evs qs
    (JointConfig stk PG G tn fn9 inst9 s9 oms om hs hist) /\
  LENGTH s9.vs_requests <= k /\ inst9.inst_opcode <> INVOKE /\
  step_inst fuel C9 inst9 s9 = Abort ab post ==>
  mem_inv (\ctx fn inst t. in_static_abort_prefix fn t \/
    lowered_mem_fact eom ctx fn inst t) C9 vs0 /\
  (guarded ==> code_end_offset_ok
    (\ctx fn inst t. raw_reachable vs0 ctx fn inst t /\ ~in_static_abort_prefix fn t) C9)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!p d fn inst s. ev_reachable orc vs0 C7 p d fn inst s ==>
       ?ws. raw_reachable source C7 fn inst (s with vs_gas_readings := ws)` by
    (rpt strip_tac >> drule_all request_cut_terminal_native_event_cover >>
     disch_then ACCEPT_TAC) >>
  `!fn inst t. raw_reachable vs0 C8 fn inst t ==>
     ?p d. ev_reachable orc vs0 C8 p d fn inst
       (t with vs_gas_readings := vs0.vs_gas_readings)` by
    (rpt strip_tac >>
     `!err. run_context bound8 C8 vs0 <> Error err` by (Cases_on `run_context bound8 C8 vs0` >> gvs[terminates_def]) >>
     mp_tac (Q.INST [`bound` |-> `bound8`, `C` |-> `C8`, `v` |-> `vs0`,
       `i` |-> `inst`, `s` |-> `t`, `ws` |-> `vs0.vs_gas_readings`]
       native_terminal_trace_cover) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[venom_state_component_equality]) >>
  `raw_reachable vs0 C9 fn9 inst9 s9` by
    metis_tac[joint_trace_reachable, joint_config_raw] >>
  mp_tac request_cut_covered_invariants >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  strip_tac >>
  irule request_cut_abort_invariants >>
  metis_tac[]
QED
