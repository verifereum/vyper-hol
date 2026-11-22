(* Successful dispatch uses the selected raw execution at the dispatch
   transaction, with the no-wrap/floor post supplied for that very entry. *)
Theory entryCreateCallSelected
Ancestors
  entryCreateBodyCut loweringCalldataCorrect e2eCorrectness e2eDefs
  sourceUnitExecution fragExec fragGasOrigin vyperInterpreter
  unitShapeDefs o1PassContract dftGasFromListTraceDefs
  externalCallSelected nonreentrantEquiv gasSummaryCompose vyperStorageFootprint
  vyperState venomState vyperCall

Theorem selected_call_terminal[local]:
  o1_source_unit_ok unit /\
  source_unit_execution_correct_at marks tops ret am tx unit vi /\
  (!gs. call_storage_ok am tx vi.vs_outcomes gs) /\
  (!gs. ~source_exempt tops (call_external (SOME vi.vs_outcomes) gs am tx)) ==>
  ?shadow_ctx func rv fuel res am' rqs obs.
    gas_origin_path T (gas_explicit_sites unit.cu_context shadow_ctx)
      unit.cu_context func
      (vi with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>) marks rv /\
    exit_result rv /\ run_context fuel unit.cu_context vi = rv /\
    (!err. rv <> Error err) /\
    (!tail. call_external_trace (SOME vi.vs_outcomes)
      (gas_explicit marks vi.vs_gas_readings ++ tail) am tx = (res, am', rqs, obs)) /\
    storage_trace_domain (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am []) obs
Proof
  strip_tac >>
  qpat_x_assum `source_unit_execution_correct_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [source_unit_execution_correct_at_def,
                                      source_unit_execution_correct_with_def])
  >- (qpat_x_assum `!tail. ~_` (qspec_then `[]` mp_tac) >> simp[])
  >- (qpat_assum `!tail. call_external_trace _ _ _ _ = _`
        (qspec_then `[]` assume_tac) >>
      drule call_external_trace_result >> simp[] >> strip_tac >>
      qpat_x_assum `!gs. ~source_exempt _ _`
        (qspec_then `gas_explicit marks vi.vs_gas_readings` mp_tac) >> simp[]) >>
  drule_all selected_run >> strip_tac >>
  qexistsl_tac [`shadow_ctx`, `func`, `r`, `fuel`, `res`, `am'`, `rqs`, `obs`] >>
  simp[] >> Cases_on `r` >> gvs[exit_result_def]
QED

(* An invocation-local source error is a unit exemption only after the
   entry adapter has projected it through the actual call trace. *)
Theorem selected_call_trace_failure[local]:
  call_external_trace (SOME os) gs am tx = (res, am', rqs, obs) /\
  create_cut_failure tops res ==>
  source_exempt tops (call_external (SOME os) gs am tx) \/
  FST (call_external (SOME os) gs am tx) =
    INR (Error (RuntimeError "create initcode too large"))
Proof
  strip_tac >> drule call_external_trace_result >> strip_tac >>
  fs[create_cut_failure_def] >> simp[source_exempt_def]
QED

(* The dispatch and default-binding prefix selects es0 for every residual
   GAS stream. In the failing body arm, the call trace stops before unlock. *)
Theorem selected_bound_call_cut[local]:
  source_deployment_rel tops am td /\
  vyperInterpreter$lookup_function NONE td.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  (!gx. external_entry_bound tops am td vi.vs_outcomes (prefix ++ gx)
    mut args dflts (es0 with gas_obs := gx)) /\
  lock_if_nr (initial_evaluation_context am.sources am.layouts td NONE)
    nr (is_view_mut mut) es0 = (INL (),es_lock) /\
  (!gx. eval_stmts (initial_evaluation_context am.sources am.layouts td NONE)
          compiled_body (es_lock with gas_obs := gx) =
        eval_stmts (initial_evaluation_context am.sources am.layouts td NONE)
          fbody (es_lock with gas_obs := gx)) /\
  create_body_cut explicit tops (initial_evaluation_context am.sources am.layouts td NONE)
    (initial_state am [])
    (eval_stmts (initial_evaluation_context am.sources am.layouts td NONE) compiled_body)
    (es_lock,sb) (before,(key,fn,inst,s)) /\
  (!gs. call_storage_ok am td vi.vs_outcomes gs) /\
  (!gs. ~source_exempt tops (call_external (SOME vi.vs_outcomes) gs am td)) /\
  (!gs. FST (call_external (SOME vi.vs_outcomes) gs am td) <>
      INR (Error (RuntimeError "create initcode too large"))) ==>
  inst_create_size_ok inst s
Proof
  strip_tac >> CCONTR_TAC >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts td NONE` >>
  qabbrev_tac `gx = gas_explicit (create_cut_marks explicit before) sb.vs_gas_readings` >>
  Cases_on `eval_stmts cx fbody (es_lock with gas_obs := gx)` >>
  rename1 `_ = (res,ee)` >>
  `?eu. unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),eu)` by
    (simp[unlock_if_nr_def, release_nonreentrant_lock_execution, return_def] >>
     Cases_on `cx.nonreentrant_slot` >>
     simp[release_nonreentrant_lock_execution, return_def] >>
     IF_CASES_TAC >> simp[release_nonreentrant_lock_execution, return_def]) >>
  pop_assum strip_assume_tac >>
  `external_entry_bound tops am td vi.vs_outcomes (prefix ++ gx)
    mut args dflts (es0 with gas_obs := gx)` by simp[] >>
  qunabbrev_tac `cx` >>
  drule_all selected_call_trace_result_nr >> strip_tac >>
  `storage_trace_domain (initial_evaluation_context am.sources am.layouts td NONE)
    (initial_state am []) obs` by
    (`call_storage_ok am td vi.vs_outcomes (prefix ++ gx)` by simp[] >>
     drule source_storage_guards_domain >>
     drule call_external_trace_result >> simp[]) >>
  suspend "body_horizon"
QED

Resume selected_bound_call_cut[body_horizon]:
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts td NONE` >>
  qabbrev_tac `H = storage_trace_horizon obs` >>
  `valid_horizon cx (initial_state am []) H obs` by
    fs[storage_trace_domain_def, Abbr `H`] >>
  `valid_horizon cx (initial_state am []) H ee.storage_trace` by
    (Cases_on `res = INL () \/ ?v. res = INR (ReturnException v)`
     >- (`?tail. eu.storage_trace = ee.storage_trace ++ tail` by
           (Cases_on `cx.nonreentrant_slot`
            >- fs[unlock_if_nr_def, return_def] >>
            drule unlock_if_nr_success_trace >>
            disch_then (qspecl_then [`nr`, `is_view_mut mut`, `ee`] strip_assume_tac) >>
            gvs[] >> metis_tac[]) >>
         metis_tac[gasOutcomeFullTheory.valid_horizon_append]) >>
     gvs[]) >>
  `create_cut_failure tops res` by
    (qpat_x_assum `create_body_cut _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE[create_body_cut_def]) >>
     simp[] >> disch_then (qspecl_then [`H`, `[]`, `res`, `ee`] mp_tac) >>
     qpat_assum `Abbrev (gx = _)`
       (fn eq => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq)]) >>
     simp[]) >>
  `create_cut_failure tops r` by
    (qpat_x_assum `create_cut_failure tops res` mp_tac >>
     simp[create_cut_failure_def] >> strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all selected_call_trace_failure >>
  qpat_x_assum `!gs. ~source_exempt _ _` (qspec_then `prefix ++ gx` assume_tac) >>
  qpat_x_assum `!gs. FST _ <> _` (qspec_then `prefix ++ gx` assume_tac) >> simp[]
QED
Finalise selected_bound_call_cut
