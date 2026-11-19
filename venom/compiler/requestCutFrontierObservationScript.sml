Theory requestCutFrontierObservation
Ancestors
  requestCutObservationLift requestCutFrontierCover
  dftGasFromListTraceDefs dftGasOracleDefs dftRunRel dftDefs
  contextCodegenRel o1PassContract staticAbortDefs venomState venomInst venomWf
  list arithmetic

(* A successful rooted cut identifies the observation by its key. If all
   rooted cuts stop, their native trace agreement restores any event visit. *)
Theorem request_cut_frontier_observation:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  C8.ctx_entry = C7.ctx_entry /\ o1_ctx_shape C7 /\ EVERY wf_function C7.ctx_functions /\
  ctx_labels_bound C7 initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  v7 = (initial with vs_gas_readings := filling) /\
  ev_reachable orc initial C8 p d fn8 inst
    (t with vs_gas_readings := initial.vs_gas_readings) /\
  inv_memory_observation inst.inst_opcode /\ inst.inst_opcode <> DRET /\
  ~in_revert_forward fn8 t /\
  ((?fn7 s7. raw_reachable v7 C7 fn7 inst s7 /\ ev_reachable orc initial C7 p d fn7 inst
      (s7 with vs_gas_readings := initial.vs_gas_readings) /\
     ~in_revert_forward fn7 s7 /\ fn8 = dft_fn fn7 /\
     s7.vs_current_bb = t.vs_current_bb) \/
   (!fuel. N <= fuel ==> trace_agrees orc (trace_context fuel C7 v7))) ==>
  (?fn7 u ws. raw_reachable v7 C7 fn7 inst (u with vs_gas_readings := ws) /\
    ~in_revert_forward fn7 u /\ fn8 = dft_fn fn7 /\
    u.vs_current_bb = t.vs_current_bb /\ ev_reachable orc initial C7 p d fn7 inst u) \/
  (in_static_abort_prefix fn8 t /\
   !p d fn i s. ev_reachable orc initial C7 p d fn i s ==>
     ?ws. raw_reachable v7 C7 fn i (s with vs_gas_readings := ws))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `v7 = _` SUBST_ALL_TAC >>
  qpat_x_assum `(?fn7 s7. _) \/ _` (DISJ_CASES_THEN strip_assume_tac)
  >- (disj1_tac >> qexistsl_tac [`fn7`, `s7 with vs_gas_readings := initial.vs_gas_readings`,
                              `s7.vs_gas_readings`] >>
      gvs[in_revert_forward_def, venom_state_component_equality]) >>
  `!p d fn i s. ev_reachable orc initial C7 p d fn i s ==>
    ?ws. raw_reachable (initial with vs_gas_readings := filling) C7 fn i
      (s with vs_gas_readings := ws)` by
    (qx_genl_tac [`a`,`e`,`g`,`i`,`s`] >> strip_tac >>
     mp_tac (Q.INST [`success` |-> `F`, `v` |-> `initial`, `C` |-> `C7`,
       `readings` |-> `filling`, `p` |-> `a`, `d` |-> `e`, `fn` |-> `g`,
       `inst` |-> `i`, `t` |-> `s`] request_cut_native_frontier_visit) >>
     simp[]) >>
  mp_tac (Q.INST [`v7` |-> `initial with vs_gas_readings := filling`]
    request_cut_native_observation_or_static_write) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[])) >>
  metis_tac[]
QED
