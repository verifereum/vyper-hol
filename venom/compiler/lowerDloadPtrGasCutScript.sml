(* gas_cut transport for the LowerDload pointer chain.  Source and target of
   a boundary have equal gas readings, and a prefix of an expansion only
   drops readings, so a cut at the target carries to the source and to the
   boundary state t0. *)
Theory lowerDloadPtrGasCut
Ancestors
  lowerDloadPtrAggregate lowerDloadPtrPhase lowerDloadPtrCall o1SafeUpto
  gasCount venomExecSemantics venomState list

Theorem dload_equal_environment_gas_readings:
  dload_equal_environment s t ==> s.vs_gas_readings = t.vs_gas_readings
Proof
  rw[dload_equal_environment_def] >>
  pop_assum (mp_tac o Q.AP_TERM `\x:venom_state. x.vs_gas_readings`) >>
  simp[]
QED

Theorem dload_boundary_core_gas_readings:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds ==>
  s.vs_gas_readings = t.vs_gas_readings
Proof
  strip_tac >> irule dload_equal_environment_gas_readings >>
  fs[dload_boundary_core_def]
QED

Theorem dload_prefix_match_gas_le:
  !k t0 H0 un0 t H un.
    dload_prefix_match fuel C PG emitted k t0 H0 un0 t H un ==>
    LENGTH t.vs_gas_readings <= LENGTH t0.vs_gas_readings
Proof
  Induct_on `k` >> rw[dload_prefix_match_def] >>
  first_x_assum drule >> strip_tac >>
  qspecl_then [`fuel`,`C`,`EL k emitted`,`u`] mp_tac
    (cj 1 gasCountTheory.gas_count_suffix) >>
  simp[gasCountTheory.gas_count_suffix_def, listTheory.LENGTH_DROP]
QED

Theorem dload_prefix_gas_cut:
  dload_prefix_match fuel C PG emitted n t0 H0 un0 t H un /\
  gas_cut cut vs t ==> gas_cut cut vs t0
Proof
  rw[] >> imp_res_tac dload_prefix_match_gas_le >> gvs[gas_cut_def]
QED

Theorem dload_boundary_core_gas_cut:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  gas_cut cut vs t ==> gas_cut cut vs s
Proof
  rw[] >> imp_res_tac dload_boundary_core_gas_readings >> gvs[gas_cut_def]
QED

Theorem dload_boundary_prefix_gas_cut:
  dload_boundary_core lo fs V Ws PG PH G H0 tn un0 s t0 cs ds /\
  dload_prefix_match fuel C' PH emitted n t0 H0 un0 t H un /\
  gas_cut cut vs t ==> gas_cut cut vs s
Proof
  rw[] >> imp_res_tac dload_boundary_core_gas_readings >>
  imp_res_tac dload_prefix_match_gas_le >> gvs[gas_cut_def]
QED
