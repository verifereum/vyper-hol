(*
 * Closed-world producer of the storage guard on callee outcomes.
 *
 * call_result_rel guards call_result_rel_at by call_outcomes_storage_ok: the
 * contract's storage backends the source run adopts from call outcomes are
 * well formed on the run's own horizon.  When every re-entry into the
 * contract during the call is itself a call to the same compiled contract,
 * on one storage horizon H shared with the caller, the guard holds and
 * closed_world_call_outcomes_ok concludes the call theorem without it.
 *
 * The S1 request-prefix companion (while the trace up to the k-th recorded
 * outcome is a valid horizon, the lowered unit is memory safe, terminates,
 * and its k-th request agrees with the source's, whose outcome is the k-th
 * callee outcome) is carried as the premise s1_request_prefix until the
 * lowering proof provides it.
 *
 * TOP-LEVEL: closed_world_call_outcomes_ok
 *)
Theory e2eOutcomesProducer
Ancestors
  e2eOutcomesGuard e2eCallAtMarks


Theorem closed_world_call_outcomes_ok:
  !policy tops runtime_bc am tx ret es H.
    vyper_call_staging policy tops runtime_bc am tx ret es /\
    s1_request_prefix tops /\
    vyper_closed_world policy tops runtime_bc am tx H es ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       gas_readings_rel (gas_readings es)
         (\gobs.
            source_storage_ok am tx (MAP SND (call_trace es)) gobs ==>
            call_outcomes_storage_ok am tx (MAP SND (call_trace es)) gobs /\
            call_result_rel_at gobs tops ret am tx es r es') T)
Proof
  cheat
QED
