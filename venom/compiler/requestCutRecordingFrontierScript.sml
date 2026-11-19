Theory requestCutRecordingFrontier
Ancestors
  requestCutFrontierCover requestCutDftExternal dftGasFromListTraceDefs
  dftGasOracleDefs dftRunRel dftDefs contextCodegenRel o1PassContract
  venomExecSemantics venomWf venomInst venomState list arithmetic

(* If the rooted cut returns an earlier stop at every sufficiently large
   fuel, its native traces still cover the same event recording and visits. *)
Theorem request_cut_recording_frontier:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  C8.ctx_entry = C7.ctx_entry /\ o1_ctx_shape C7 /\
  ctx_labels_bound C7 initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn)) C7.ctx_functions /\
  EVERY wf_function C7.ctx_functions /\
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  ev_reachable orc initial C8 p d fn8 inst (s8 with vs_gas_readings := initial.vs_gas_readings) /\
  inst.inst_opcode <> INVOKE /\ step_inst n C8 inst s8 = OK u8 /\
  LENGTH s8.vs_requests = k /\ k < LENGTH u8.vs_requests /\
  (!fuel. N <= fuel ==> trace_agrees orc (trace_context fuel C7
    (initial with vs_gas_readings := filling))) ==>
  (?fn7 s7 u7.
    raw_reachable (initial with vs_gas_readings := filling) C7 fn7 inst s7 /\
    step_inst 0 C7 inst s7 = OK u7 /\
    s7.vs_requests = s8.vs_requests /\ s7.vs_outcomes = s8.vs_outcomes /\
    u7.vs_requests = u8.vs_requests /\ u7.vs_outcomes = u8.vs_outcomes) /\
  (!p d fn i s. ev_reachable orc initial C7 p d fn i s ==>
    ?ws. raw_reachable (initial with vs_gas_readings := filling) C7 fn i
      (s with vs_gas_readings := ws))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!p d fn i s. ev_reachable orc initial C7 p d fn i s ==>
    ?ws. raw_reachable (initial with vs_gas_readings := filling) C7 fn i
      (s with vs_gas_readings := ws)` by
    (qx_genl_tac [`a`, `e`, `g`, `j`, `t`] >> strip_tac >>
     mp_tac (Q.INST [`v` |-> `initial`, `C` |-> `C7`, `success` |-> `F`,
       `readings` |-> `filling`, `p` |-> `a`, `d` |-> `e`,
       `fn` |-> `g`, `inst` |-> `j`]
       request_cut_native_frontier_visit) >>
     simp[]) >>
  conj_tac >- (
    mp_tac (Q.INST [`C` |-> `C7`, `C'` |-> `C8`, `fn'` |-> `fn8`,
      `t` |-> `s8`, `post` |-> `u8`, `fuel` |-> `n`] request_cut_dft_native_recording) >>
    (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[])) >>
    disch_then ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
