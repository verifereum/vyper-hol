Theory e2eOutcomesProducer
Ancestors
  e2eRequestCutDefs e2eDefs e2eComposition e2eOutcomesGuard

Theorem closed_world_call_outcomes_ok:
  !fin policy tops runtime_bc am tx ret es H.
    vyper_call_staging fin policy tops runtime_bc am tx ret es /\
    s1_request_prefix tops /\
    vyper_closed_world fin policy tops runtime_bc am tx H es ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       gas_readings_rel (gas_readings es)
         (\gobs.
            call_storage_ok am tx (MAP SND (call_trace es)) gobs /\
            call_result_rel_at gobs tops am tx es r es'))
Proof
  rpt strip_tac >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `frame_resource_starved es r es'` >> simp[] >>
  metis_tac[call_guard_gas_link, guard_closed_world_readings]
QED
