(* Compose call results with the caller's fixed finite storage horizon. *)
Theory linkedCallStorage
Ancestors
  e2eModsDefs e2eCorrectness[qualified] e2eDefs e2eComposition e2eLifecycle
  guardSourceAlignment linkedCallPremises callTrace
  vyperCallFiniteStorage vyperCallFiniteStorageSupport vyperContext
  vyperInterpreter vyperStorageFootprint
  pair list

Theorem valid_horizon_for_dispatch_mods:
  e2eCorrectness$storage_ok H am tx /\ call_within_mods H mods exps am tx es /\
  calldata_dispatch_mods mods exps tx.calldata = SOME (f, vals) ==>
  valid_horizon
    (initial_evaluation_context am.sources am.layouts
       (tx with <| function_name := f; args := vals |>) NONE)
    (initial_state am []) H
    (source_storage_trace am (tx with <| function_name := f; args := vals |>)
       (MAP SND (call_trace es)) gobs)
Proof
  simp[e2eCorrectnessTheory.storage_ok_def, call_within_mods_def, valid_horizon_def] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `storage_well_formed_on cx _ _` >>
  qmatch_goalsub_abbrev_tac `storage_well_formed_on selected_cx _ _` >>
  `selected_cx.txn.target = cx.txn.target` by
    simp[Abbr `cx`, Abbr `selected_cx`, initial_evaluation_context_def] >>
  `storage_well_formed_on selected_cx (initial_state am []) (FST H) <=>
   storage_well_formed_on cx (initial_state am []) (FST H)` by
    (irule storage_well_formed_on_target >> simp[]) >>
  drule storage_observations_ok_target >> strip_tac >> fs[]
QED

Theorem call_result_rel_from_readings_mods:
  source_typing_ok_mods mods exps am tx /\ source_deployment_rel_mods mods exps am tx /\
  (!gobs. valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) H (source_storage_trace am tx (MAP SND (call_trace es)) gobs)) /\
  gas_readings_rel (gas_readings es)
    (\gobs. call_storage_ok am tx (MAP SND (call_trace es)) gobs ==>
            call_result_rel_at_mods gobs mods exps am tx es r es') ==>
  call_result_rel_mods H mods exps am tx es r es'
Proof
  simp[call_result_rel_mods_def] >> strip_tac >>
  drule_all source_typing_ok_runtime_ready_mods >> strip_tac >>
  drule gas_readings_rel_mono >> disch_then irule >>
  qx_gen_tac `gobs` >> BETA_TAC >> strip_tac >>
  qpat_assum `!gobs. valid_horizon _ _ _ _` (qspec_then `gobs` assume_tac) >>
  conj_tac
  >- (qpat_x_assum `call_storage_ok _ _ _ gobs ==> _` irule >>
      irule valid_horizon_call_storage_ok >> qexists_tac `H` >> simp[]) >>
  qabbrev_tac `os = MAP SND (call_trace es)` >>
  Cases_on `call_external_trace (SOME os) gobs am tx` >>
  rename1 `call_external_trace _ _ _ _ = (res,rest)` >>
  PairCases_on `rest` >>
  rename1 `call_external_trace _ _ _ _ = (res,am',rqs,obs)` >>
  drule call_external_trace_result >> strip_tac >>
  drule_all call_external_static_fields >> strip_tac >>
  `valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
     (initial_state am []) H obs` by fs[] >>
  drule_all call_external_storage_well_formed_on >> strip_tac >>
  fs[e2eCorrectnessTheory.storage_ok_def, valid_horizon_def]
QED
