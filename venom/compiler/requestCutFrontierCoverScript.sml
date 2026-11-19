Theory requestCutFrontierCover
Ancestors
  requestCutNativeEventCover
  dftGasFromListTraceDefs dftGasFromListRestore dftGasFromListReplay
  dftGasToListTrace dftGasToListFuel dftGasToListReachWitness
  dftGasToListVisitReplay dftGasToListAbort dftGasOracleDefs
  contextCodegenRel venomExecSemantics venomState venomWf
  passSimulationDefs list arithmetic

(* The rooted cut is available at any sufficiently large fuel. If its
   successful arm is unavailable, use a fuel that covers the event visit. *)
Theorem request_cut_native_frontier_visit:
  EVERY wf_function C.ctx_functions /\
  (!fuel. N <= fuel ==> success \/
    trace_agrees orc (dftGasFromListTraceDefs$trace_context fuel C
      (v with vs_gas_readings := readings))) /\
  ev_reachable orc v C p d fn inst t ==>
  success \/
  ?ws. raw_reachable (v with vs_gas_readings := readings) C fn inst
    (t with vs_gas_readings := ws)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ev_reachable_trace_witness >> strip_tac >>
  qabbrev_tac `bound = MAX N fuel` >>
  `N <= bound /\ fuel <= bound` by simp[Abbr `bound`] >>
  qpat_x_assum `!fuel. N <= fuel ==> _` drule >> strip_tac >> simp[] >>
  `MEM (n,p,d,fn,inst,t)
    (trace_visits 0 (dftGasToListTrace$trace_context orc bound C v))` by
    metis_tac[context_visits_fuel_preserved] >>
  metis_tac[request_cut_native_event_visit]
QED

(* A primitive event abort can fix a complete native trace while taking
   the fuel after the abort witness, including when smaller cuts errored. *)
Theorem request_cut_native_frontier_abort:
  EVERY wf_function C.ctx_functions /\
  (!fuel. N <= fuel ==> success \/
    trace_agrees orc (dftGasFromListTraceDefs$trace_context fuel C
      (v with vs_gas_readings := readings))) /\
  ev_reachable orc v C p d fn inst t /\ inst.inst_opcode <> GAS /\
  inst.inst_opcode <> INVOKE /\ step_inst_base inst t = Abort a u ==>
  success \/
  ?bound.
    terminates (run_context bound C (v with vs_gas_readings := readings)) /\
    trace_agrees orc (dftGasFromListTraceDefs$trace_context bound C
      (v with vs_gas_readings := readings))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ev_reachable_trace_item >> strip_tac >>
  qabbrev_tac `bound = MAX N fuel` >>
  `N <= bound /\ fuel <= bound` by simp[Abbr `bound`] >>
  qpat_x_assum `!fuel. N <= fuel ==> _` drule >> strip_tac >> simp[] >>
  `MEM (TraceVisit p d fn inst t)
    (dftGasToListTrace$trace_context orc bound C v)` by
    (mp_tac (Q.INST [`larger` |-> `bound`, `orc` |-> `orc`, `ctx` |-> `C`,
      `s` |-> `v`] trace_context_fuel_extension) >>
     simp[trace_extension_def] >>
     strip_tac >> gvs[]) >>
  `ev_context orc bound C v = Abort a u` by
    metis_tac[trace_context_primitive_abort] >>
  disj2_tac >> qexists_tac `bound` >> simp[] >>
  qpat_assum `trace_agrees orc _`
    (mp_tac o Q.INST [`gs` |-> `v.vs_gas_readings`] o MATCH_MP trace_context_replay) >>
  simp[venom_state_component_equality] >>
  Cases_on `run_context bound C (v with vs_gas_readings := readings)` >>
  simp[restore_rel_cases, terminates_def]
QED
