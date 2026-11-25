(*
 * The source side of the selected external call, and the guarded body's
 * code, as S1 (loweringRuntimeCorrect) and the counted body runs
 * (loweringPtrBodyRun, loweringMemBodyRun) use them.
 *
 * TOP-LEVEL:
 *   call_external_selected_body, call_external_selected_body_gas -- the
 *     source runs the selected body, at any gas observations
 *   type_stmts_none_valued_return -- a body typed at NoneT has no valued
 *     return
 *   guarded_body_code, guarded_body_stmts_env -- the guarded body's code
 *)

Theory externalCallSelected
Ancestors
  externalEntryBound vyperState vyperContext vyperInterpreter vyperTypeSystem
  vyperTypeSelectedEntrySoundness vyperTypeExternalCallMachine nonreentrantEquiv
  e2eDefs supportedStmts vyperStorageFootprint
  compileEnv compileVyper stmtLowering stmtLoweringMono moduleLowering
  fragExec loweringPosts stmtSimProps bodySim stmtsEnvRetTy

val _ = Parse.hide "body";

(* call_external_body sets the scopes before it reads them. *)
Theorem call_external_body_scopes[local]:
  !am cx nr mut tenv s sc env body ret.
    call_external_body am cx nr mut tenv (s with scopes := sc) env body ret =
    call_external_body am cx nr mut tenv s env body ret
Proof
  simp[call_external_body_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.set_scopes_def]
QED

(* The call valid_vyper_call selects, at gas observations gobs, sends the
   call value and then runs call_external_body from the bound arguments,
   with pending deletions finalised on success and on halt.  es0 is the state after
   the value moved, as external_entry_reaches_body starts the body from
   it; the body starts from es0 with the call's observations. *)
Theorem call_external_selected_body_gas:
  !tops am tx ret mut nr args fbody env orc gobs es0.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, nr, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
      (INL (), es0) ==>
    call_external orc gobs am tx =
      case call_external_body am
             (initial_evaluation_context am.sources am.layouts tx NONE)
             nr mut (type_env tops) (es0 with gas_obs := gobs) env fbody ret of
        (INL v, am', rqs) => (INL v, finalize_pending_deletions am', rqs)
      | (INR HaltException, am', rqs) =>
          (INR HaltException, finalize_pending_deletions am', rqs)
      | failure => failure
Proof
  rw[source_deployment_rel_def] >>
  `type_env_all_modules [(NONE, tops)] = type_env tops` by
    simp[type_env_all_modules_def, type_env_def] >>
  simp[call_external_def, call_external_trace_def, find_function_module_def,
       lookup_exported_function_def, get_self_code_def, get_module_code_def,
       initial_evaluation_context_def] >>
  qmatch_goalsub_abbrev_tac `call_external_function_trace orc gobs am cx` >>
  qabbrev_tac `es1 = (es0 with gas_obs := gobs) with scopes := [FEMPTY]` >>
  `send_call_value mut cx
     (initial_state am [FEMPTY] with
        <| outcomes := orc; requests := []; gas_obs := gobs |>) =
   (INL (), es1)` by
    (qpat_x_assum `send_call_value _ _ _ = _` mp_tac >>
     simp[Abbr `cx`, initial_evaluation_context_def] >> strip_tac >>
     drule send_call_value_with_gas_obs >> strip_tac >>
     pop_assum (qspec_then `gobs` assume_tac) >>
     drule send_call_value_with_scopes >> strip_tac >>
     pop_assum (qspec_then `[FEMPTY]` mp_tac) >>
     simp[Abbr `es1`, initial_state_def]) >>
  `eval_external_defaults cx [] es1 = (INL [], es1)` by
    simp[Abbr `es1`, eval_external_defaults_def, evaluate_def,
         vyperStateTheory.bind_def,
         vyperStateTheory.ignore_bind_def, vyperStateTheory.get_scopes_def,
         vyperStateTheory.set_scopes_def, vyperStateTheory.finally_def,
         vyperStateTheory.return_def] >>
  `call_external_function orc gobs am cx nr mut tops [(NONE, tops)] args []
     tx.args fbody ret =
   call_external_body am cx nr mut (type_env tops) es1 env fbody ret` by
    (qpat_assum `_ = type_env tops` (SUBST1_TAC o SYM) >>
     irule call_external_function_body >> gvs[Abbr `cx`]) >>
  gvs[Abbr `es1`, call_external_body_scopes] >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ _ = _`
    (mp_tac o GSYM) >>
  simp[call_external_function_def] >>
  Cases_on `call_external_function_trace orc gobs am cx nr mut tops
              [(NONE,tops)] args [] tx.args fbody ret` >>
  PairCases_on `r` >> Cases_on `q` >> simp[] >>
  rename1 `INR exc` >> Cases_on `exc` >> simp[]
QED

(* Expose the selected call after value transfer and argument binding. *)
val selected_external_trace_tac =
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_deployment_rel _ _ _`
    (strip_assume_tac o REWRITE_RULE [source_deployment_rel_def]) >>
  `type_env_all_modules [(NONE, tops)] = type_env tops` by
    simp[type_env_all_modules_def, type_env_def] >>
  `es0.scopes = [env]` by
    (drule (cj 1 send_call_value_with_scopes) >> simp[initial_state_def]) >>
  simp[call_external_trace_def, find_function_module_def,
       lookup_exported_function_def, get_self_code_def, get_module_code_def,
       initial_evaluation_context_def, Excl "unlock_if_nr_def"] >>
  qmatch_goalsub_abbrev_tac `call_external_function_trace orc gobs am cx` >>
  qabbrev_tac `es1 = (es0 with gas_obs := gobs) with scopes := [FEMPTY]` >>
  `send_call_value mut cx
     (initial_state am [FEMPTY] with
        <| outcomes := orc; requests := []; gas_obs := gobs |>) =
   (INL (), es1)` by
    (qpat_x_assum `send_call_value _ _ _ = _` mp_tac >>
     simp[Abbr `cx`, initial_evaluation_context_def] >> strip_tac >>
     drule send_call_value_with_gas_obs >> strip_tac >>
     pop_assum (qspec_then `gobs` assume_tac) >>
     drule send_call_value_with_scopes >> strip_tac >>
     pop_assum (qspec_then `[FEMPTY]` mp_tac) >>
     simp[Abbr `es1`, initial_state_def]) >>
  `es1 with scopes := [env] = es0 with gas_obs := gobs` by
    simp[Abbr `es1`, evaluation_state_component_equality] >>
  `~cx.in_deploy` by simp[Abbr `cx`] >>
  `initial_state am [FEMPTY] with
     <| outcomes := orc; requests := []; gas_obs := gobs; storage_trace := [] |> =
   initial_state am [FEMPTY] with
     <| outcomes := orc; requests := []; gas_obs := gobs |>` by
    simp[initial_state_def] >>
  simp[call_external_function_trace_def,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.set_scopes_def, vyperStateTheory.return_def,
       Excl "lock_if_nr_def", Excl "unlock_if_nr_def"]

(* The source unlocks on ordinary fallthrough and Return. *)
Theorem call_external_body_run_nr:
  !am cx nr mut tenv env fbody ret es0 es_lock res ee eu.
    es0.scopes = [env] /\
    lock_if_nr cx nr (is_view_mut mut) es0 = (INL (),es_lock) /\
    eval_stmts cx fbody es_lock = (res,ee) /\
    ((res = INL () \/ (?v. res = INR (ReturnException v))) ==>
      unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),eu)) ==>
    (res = INL () ==>
      call_external_body am cx nr mut tenv es0 env fbody ret =
        (INL NoneV,
         abstract_machine_from_state am.sources am.exports am.layouts eu,
         eu.requests)) /\
    (!v. res = INR (ReturnException v) ==>
      call_external_body am cx nr mut tenv es0 env fbody ret =
        case evaluate_type tenv ret of
          NONE => (INR (Error (TypeError "eval ret")),am,eu.requests)
        | SOME tv =>
            case safe_cast tv v of
              NONE => (INR (Error (TypeError "ext cast ret")),am,eu.requests)
            | SOME v' =>
                (INL v',
                 abstract_machine_from_state am.sources am.exports am.layouts eu,
                 eu.requests)) /\
    (res = INR HaltException ==>
      call_external_body am cx nr mut tenv es0 env fbody ret =
        (INR HaltException,
         abstract_machine_from_state am.sources am.exports am.layouts ee,
         ee.requests)) /\
    (!e. res = INR e /\ (!v. e <> ReturnException v) /\ e <> HaltException ==>
      call_external_body am cx nr mut tenv es0 env fbody ret =
        (INR e,am,ee.requests))
Proof
  rpt gen_tac >> strip_tac >>
  `es0 with scopes := [env] = es0` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  PURE_ONCE_REWRITE_TAC[call_external_body_def] >>
  PURE_REWRITE_TAC[LET_THM] >>
  PURE_ONCE_REWRITE_TAC[GSYM is_view_mut_def] >>
  PURE_ONCE_REWRITE_TAC[GSYM lock_if_nr_def, GSYM unlock_if_nr_def] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.return_def, vyperStateTheory.set_scopes_def,
       Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
  rpt strip_tac >> gvs[Excl "lock_if_nr_def", Excl "unlock_if_nr_def"]
  >- (Cases_on `evaluate_type tenv ret` >> simp[] >>
      rename1 `evaluate_type tenv ret = SOME tv` >>
      Cases_on `safe_cast tv v` >> simp[]) >>
  Cases_on `e` >> gvs[]
QED

Theorem lock_if_nr_with_gas_obs:
  lock_if_nr cx nr iv s = (result,u) ==>
  lock_if_nr cx nr iv (s with gas_obs := obs) =
    (result,u with gas_obs := obs)
Proof
  Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
  Cases_on `iv` >> Cases_on `cx.txn.is_static` >>
  simp[lock_if_nr_def, acquire_nonreentrant_lock_execution,
       check_not_static_def, vyperStateTheory.check_def,
       vyperStateTheory.assert_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem unlock_if_nr_with_gas_obs:
  unlock_if_nr cx nr iv s = (result,u) ==>
  unlock_if_nr cx nr iv (s with gas_obs := obs) =
    (result,u with gas_obs := obs)
Proof
  Cases_on `nr` >> Cases_on `iv` >> Cases_on `cx.nonreentrant_slot` >>
  simp[unlock_if_nr_def, release_nonreentrant_lock_execution,
       vyperStateTheory.return_def] >> strip_tac >> gvs[]
QED

Theorem unlock_if_nr_with_scopes:
  unlock_if_nr cx nr iv s = (result,u) ==>
  unlock_if_nr cx nr iv (s with scopes := sc) =
    (result,u with scopes := sc)
Proof
  Cases_on `nr` >> Cases_on `iv` >> Cases_on `cx.nonreentrant_slot` >>
  simp[unlock_if_nr_def, release_nonreentrant_lock_execution,
       vyperStateTheory.return_def] >> strip_tac >> gvs[]
QED

(* The selected lock is observed even if a View function only reads it. *)
Theorem lock_if_nr_success_trace:
  cx.nonreentrant_slot = SOME key /\
  lock_if_nr cx nr iv es = (INL (),se) ==>
  se.storage_trace = es.storage_trace ++ (if nr then [StorageLock key] else [])
Proof
  Cases_on `nr` >> Cases_on `iv` >> Cases_on `cx.txn.is_static` >>
  Cases_on `cx.nonreentrant_slot` >>
  simp[lock_if_nr_def, acquire_nonreentrant_lock_execution,
       check_not_static_def, vyperStateTheory.check_def,
       vyperStateTheory.assert_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem unlock_if_nr_success_trace:
  cx.nonreentrant_slot = SOME key ==>
  ?se. unlock_if_nr cx nr iv es = (INL (),se) /\
       se.storage_trace = es.storage_trace ++
         (if nr /\ ~iv then [StorageLock key] else [])
Proof
  Cases_on `nr` >> Cases_on `iv` >>
  simp[unlock_if_nr_def, release_nonreentrant_lock_execution,
       vyperStateTheory.return_def]
QED

Theorem observed_lock_horizons:
  MEM key (storage_trace_locks obs) /\ key < dimword (:256) ==>
  (storage_trace_domain cx st (obs ++ [StorageLock key]) <=>
   storage_trace_domain cx st obs) /\
  (!H. valid_horizon cx st H (obs ++ [StorageLock key]) <=>
       valid_horizon cx st H obs)
Proof
  strip_tac >>
  `key + 1 <= dimword (:256)` by decide_tac >>
  `storage_trace_regions [StorageLock key] = [] /\
   storage_trace_locks [StorageLock key] = [key]` by
    simp[storage_trace_regions_def, storage_trace_locks_def] >>
  `!k. MEM k (storage_trace_locks obs ++ [key]) <=>
       MEM k (storage_trace_locks obs)` by
    (simp[listTheory.MEM_APPEND] >> metis_tac[]) >>
  simp[storage_trace_domain_def, valid_horizon_def,
       storage_trace_horizon_def, storage_observations_ok_def,
       storage_locks_separated_def, listTheory.EVERY_MEM] >>
  simp[storage_roots_fit_def, storage_trace_backends_well_formed_def,
       listTheory.EVERY_MEM, listTheory.MEM_APPEND] >>
  metis_tac[]
QED

(* The trace includes the unlock after fallthrough or Return. *)
Theorem call_external_selected_body_trace:
  !tops am tx ret mut nr args fbody env orc gobs es0 es_lock res ee.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, nr, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
      (INL (), es0) /\
    lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
      nr (is_view_mut mut) (es0 with gas_obs := gobs) = (INL (), es_lock) /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody es_lock = (res, ee) ==>
    ?r am' rqs.
      call_external_trace orc gobs am tx =
        (r, am', rqs,
         (if res = INL () \/ (?v. res = INR (ReturnException v)) then
            SND (unlock_if_nr
              (initial_evaluation_context am.sources am.layouts tx NONE)
              nr (is_view_mut mut) ee)
          else ee).storage_trace)
Proof
  selected_external_trace_tac >>
  `?us. unlock_if_nr
     (initial_evaluation_context am.sources am.layouts tx NONE)
     nr (is_view_mut mut) ee = (INL (),us)` by
    (simp[unlock_if_nr_def, vyperStateTheory.return_def,
          release_nonreentrant_lock_execution] >>
     Cases_on `(initial_evaluation_context
       am.sources am.layouts tx NONE).nonreentrant_slot` >>
     simp[vyperStateTheory.return_def] >>
     IF_CASES_TAC >>
     simp[release_nonreentrant_lock_execution, vyperStateTheory.return_def]) >>
  gvs[Abbr `cx`, initial_evaluation_context_def, pairTheory.UNCURRY,
      Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
  Cases_on `res` >> simp[] >>
  rename1 `eval_stmts _ _ _ = (INR exc, _)` >>
  Cases_on `exc` >> simp[] >>
  Cases_on `evaluate_type (type_env tops) ret` >> simp[] >>
  rename1 `evaluate_type (type_env tops) ret = SOME tv` >>
  rename1 `eval_stmts _ _ _ = (INR (ReturnException value), _)` >>
  Cases_on `safe_cast tv value` >> simp[]
QED

(* Unfold selection through the successful transfer, defaults and binding. *)
fun selected_bound_trace_tac gobs =
  qpat_x_assum `external_entry_bound _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [external_entry_bound_def]) >>
  `LENGTH tx.args + LENGTH dflt_vs = LENGTH args` by
    (drule vyperCallTheory.bind_arguments_length >> simp[]) >>
  `LENGTH dflt_vs =
    LENGTH dflts - (LENGTH dflts - (LENGTH args - LENGTH tx.args))` by
    (drule eval_external_defaults_length >> simp[]) >>
  `~(LENGTH tx.args > LENGTH args \/
       LENGTH args - LENGTH tx.args > LENGTH dflts)` by decide_tac >>
  qpat_x_assum `source_deployment_rel _ _ _`
    (strip_assume_tac o REWRITE_RULE [source_deployment_rel_def]) >>
  `type_env_all_modules [(NONE, tops)] = type_env tops` by
    simp[type_env_all_modules_def, type_env_def] >>
  simp[call_external_trace_def, find_function_module_def,
       lookup_exported_function_def, get_self_code_def, get_module_code_def,
       initial_evaluation_context_def, Excl "unlock_if_nr_def"] >>
  qmatch_goalsub_abbrev_tac `call_external_function_trace _ _ am cx` >>
  `cx = initial_evaluation_context am.sources am.layouts tx NONE` by
    simp[Abbr `cx`, initial_evaluation_context_def] >>
  `~cx.in_deploy` by simp[Abbr `cx`] >>
  qpat_x_assum `cx = initial_evaluation_context _ _ _ _` SUBST_ALL_TAC >>
  (Q.SPECL [gobs, `os`, `am`] (Q.prove
     (`!obs os am. initial_state am [FEMPTY] with
        <|outcomes := SOME os; requests := []; gas_obs := obs; storage_trace := []|> =
      initial_state am [FEMPTY] with
        <|outcomes := SOME os; requests := []; gas_obs := obs|>`,
      simp[initial_state_def])) |> assume_tac) >>
  qpat_x_assum `_ = s2 with scopes := _` (ASSUME_TAC o SYM) >>
  qpat_x_assum `Abbrev _` kall_tac >>
  pure_rewrite_tac [call_external_function_trace_def, LET_THM] >>
  asm_simp_tac std_ss [] >>
  asm_simp_tac std_ss [vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
    vyperStateTheory.set_scopes_def, vyperStateTheory.return_def,
    optionTheory.option_case_def, sumTheory.sum_case_def,
    pairTheory.pair_case_thm, pairTheory.UNCURRY];

Theorem call_external_selected_lock_failure:
  !tops am tx ret mut nr args dflts fbody os prefix es0 exn es_abort.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,dflts,ret,fbody) /\
    (!gx. external_entry_bound tops am tx os (prefix ++ gx) mut args dflts
      (es0 with gas_obs := gx)) /\
    lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
      nr (is_view_mut mut) es0 = (INR exn,es_abort) ==>
    !gx. call_external_trace (SOME os) (prefix ++ gx) am tx =
      (INR exn,am,es_abort.requests,es_abort.storage_trace)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  qpat_x_assum `!gx. external_entry_bound _ _ _ _ _ _ _ _ _`
    (qspec_then `gx` assume_tac) >>
  `lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
    nr (is_view_mut mut) (es0 with gas_obs := gx) =
    (INR exn,es_abort with gas_obs := gx)` by
    (drule lock_if_nr_with_gas_obs >> disch_then (qspec_then `gx` ACCEPT_TAC)) >>
  qpat_assum `lock_if_nr _ _ _ es0 = _`
    (strip_assume_tac o MATCH_MP (REWRITE_RULE [GSYM lock_if_nr_def] call_lock_action_error)) >>
  selected_bound_trace_tac `prefix ++ gx` >> simp[]
QED

Theorem selected_call_trace_result_nr:
  !tops am tx ret mut nr args dflts fbody os prefix gx es0 es_lock res ee eu.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,dflts,ret,fbody) /\
    external_entry_bound tops am tx os (prefix ++ gx) mut args dflts
      (es0 with gas_obs := gx) /\
    lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
      nr (is_view_mut mut) es0 = (INL (),es_lock) /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody (es_lock with gas_obs := gx) = (res,ee) /\
    unlock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
      nr (is_view_mut mut) ee = (INL (),eu) ==>
    ?r am' rqs obs.
      call_external_trace (SOME os) (prefix ++ gx) am tx = (r,am',rqs,obs) /\
      ((res = INL () \/ (?v. res = INR (ReturnException v))) ==>
        obs = eu.storage_trace) /\
      (~(res = INL () \/ (?v. res = INR (ReturnException v))) ==>
        obs = ee.storage_trace) /\
      (res = INL () ==>
        r = INL NoneV /\ rqs = eu.requests /\
        am' = finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts eu)) /\
      (!v. res = INR (ReturnException v) ==>
        rqs = eu.requests /\
        (r,am') =
          case evaluate_type (type_env tops) ret of
            NONE => (INR (Error (TypeError "eval ret")),am)
          | SOME tv =>
              case safe_cast tv v of
                NONE => (INR (Error (TypeError "ext cast ret")),am)
              | SOME v' => (INL v',finalize_pending_deletions
                  (abstract_machine_from_state am.sources am.exports am.layouts eu))) /\
      (res = INR HaltException ==>
        r = INR HaltException /\ rqs = ee.requests /\
        am' = finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee)) /\
      (!e. res = INR e /\ (!v. e <> ReturnException v) /\ e <> HaltException ==>
        r = INR e /\ am' = am /\ rqs = ee.requests)
Proof
  rpt gen_tac >> strip_tac >>
  `lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
    nr (is_view_mut mut) (es0 with gas_obs := gx) =
    (INL (),es_lock with gas_obs := gx)` by
    (drule lock_if_nr_with_gas_obs >> disch_then (qspec_then `gx` ACCEPT_TAC)) >>
  selected_bound_trace_tac `prefix ++ gx` >>
  Cases_on `res` >> simp[Excl "unlock_if_nr_def"] >>
  rename1 `eval_stmts _ _ _ = (INR exc, _)` >>
  Cases_on `exc` >> simp[Excl "unlock_if_nr_def"] >>
  Cases_on `evaluate_type (type_env tops) ret` >> simp[] >>
  rename1 `evaluate_type (type_env tops) ret = SOME tv` >>
  rename1 `eval_stmts _ _ _ = (INR (ReturnException value), _)` >>
  Cases_on `safe_cast tv value` >> simp[]
QED

(* An unread gas tail changes neither the source result nor its final trace. *)
Theorem selected_call_trace_gas_cong_nr:
  !tops am tx ret mut nr args dflts fbody os prefix g1 g2 es0 es_lock res ee o1 o2.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,dflts,ret,fbody) /\
    (!gx. external_entry_bound tops am tx os (prefix ++ gx) mut args dflts
      (es0 with gas_obs := gx)) /\
    lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
      nr (is_view_mut mut) es0 = (INL (),es_lock) /\
    (nr /\ ~is_view_mut mut ==>
      IS_SOME (initial_evaluation_context am.sources am.layouts tx NONE).
        nonreentrant_slot) /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody (es_lock with gas_obs := g1) = (res,ee with gas_obs := o1) /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody (es_lock with gas_obs := g2) = (res,ee with gas_obs := o2) ==>
    call_external_trace (SOME os) (prefix ++ g1) am tx =
      call_external_trace (SOME os) (prefix ++ g2) am tx
Proof
  rpt gen_tac >> strip_tac >>
  `?eu. unlock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
    nr (is_view_mut mut) ee = (INL (),eu)` by
    (Cases_on `nr /\ ~is_view_mut mut`
     >- (Cases_on `(initial_evaluation_context am.sources am.layouts tx NONE).
                      nonreentrant_slot` >> fs[is_view_mut_def] >>
         rw[unlock_if_nr_def, is_view_mut_def,
            release_nonreentrant_lock_execution]) >>
     `~nr \/ is_view_mut mut` by metis_tac[] >>
     gvs[unlock_if_nr_def, vyperStateTheory.return_def]) >>
  drule unlock_if_nr_with_gas_obs >> strip_tac >>
  qspecl_then [`tops`, `am`, `tx`, `ret`, `mut`, `nr`, `args`, `dflts`, `fbody`,
               `os`, `prefix`, `g1`, `es0`, `es_lock`, `res`,
               `ee with gas_obs := o1`, `eu with gas_obs := o1`] mp_tac
    selected_call_trace_result_nr >>
  qspecl_then [`tops`, `am`, `tx`, `ret`, `mut`, `nr`, `args`, `dflts`, `fbody`,
               `os`, `prefix`, `g2`, `es0`, `es_lock`, `res`,
               `ee with gas_obs := o2`, `eu with gas_obs := o2`] mp_tac
    selected_call_trace_result_nr >>
  impl_tac >- simp[Excl "unlock_if_nr_def"] >>
  strip_tac >>
  impl_tac >- simp[Excl "unlock_if_nr_def"] >>
  strip_tac >>
  Cases_on `res` >> gvs[abstract_machine_from_state_def] >>
  rename1 `INR exc` >> Cases_on `exc` >>
  gvs[abstract_machine_from_state_def] >> BasicProvers.every_case_tac >> gvs[]
QED

(* A successful entry records the lock before the body can release it. *)
Theorem selected_unlock_trace_horizons:
  cx.nonreentrant_slot = SOME key /\ key < dimword (:256) /\
  lock_if_nr cx T iv es0 = (INL (),es_lock) /\
  eval_stmts cx fbody (es_lock with gas_obs := gs) = (res,ee) /\
  unlock_if_nr cx T iv ee = (INL (),eu) ==>
  (storage_trace_domain cx st (eu.storage_trace) <=>
   storage_trace_domain cx st ee.storage_trace) /\
  (!H. valid_horizon cx st H eu.storage_trace <=>
       valid_horizon cx st H ee.storage_trace)
Proof
  strip_tac >>
  `es_lock.storage_trace = es0.storage_trace ++ [StorageLock key]` by
    (drule_all lock_if_nr_success_trace >> simp[]) >>
  `?suffix. ee.storage_trace = es_lock.storage_trace ++ suffix` by
    (mp_tac (Q.SPECL [`cx`,`fbody`]
       (CONJUNCT1 (CONJUNCT2 vyperStorageTraceTheory.evaluate_storage_trace_frame))) >>
     simp_tac std_ss [vyperStorageTraceTheory.storage_trace_frame_def] >>
     disch_then (qspecl_then [`es_lock with gas_obs := gs`,
                             `es_lock.storage_trace`] mp_tac) >>
     Cases_on `eval_stmts cx fbody
       ((es_lock with gas_obs := gs) with storage_trace := [])` >>
     simp[] >> strip_tac >>
     qpat_x_assum `eval_stmts _ _ _ = (res,ee)` mp_tac >>
     simp[] >> strip_tac >>
     qexists_tac `r.storage_trace` >> simp[]) >>
  mp_tac (Q.INST [`nr` |-> `T`, `iv` |-> `iv`, `es` |-> `ee`]
    (SPEC_ALL unlock_if_nr_success_trace)) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `unlocked_source` strip_assume_tac) >>
  `unlocked_source = eu` by
    (qpat_assum `unlock_if_nr _ T _ _ = (INL (),unlocked_source)` (fn unlock =>
       qpat_assum `unlock_if_nr _ T _ _ = (INL (),eu)` (fn result =>
         ACCEPT_TAC (REWRITE_RULE [pairTheory.PAIR_EQ] (TRANS (SYM unlock) result))))) >>
  Cases_on `iv` >> gvs[] >>
  irule observed_lock_horizons >>
  simp[storage_trace_locks_def, listTheory.MAP_APPEND, listTheory.FLAT_APPEND,
       listTheory.MEM_APPEND]
QED

(* call_external_selected_body_gas without gas observations. *)
Theorem call_external_selected_body:
  !tops am tx ret mut nr args fbody env orc es0.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, nr, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
      (INL (), es0) ==>
    call_external orc [] am tx =
      case call_external_body am
             (initial_evaluation_context am.sources am.layouts tx NONE)
             nr mut (type_env tops) es0 env fbody ret of
        (INL v, am', rqs) => (INL v, finalize_pending_deletions am', rqs)
      | (INR HaltException, am', rqs) =>
          (INR HaltException, finalize_pending_deletions am', rqs)
      | failure => failure
Proof
  rpt strip_tac >>
  drule_all call_external_selected_body_gas >>
  disch_then (qspec_then `[]` SUBST1_TAC) >>
  `es0 with gas_obs := [] = es0` suffices_by simp[] >>
  drule (cj 1 send_call_value_with_gas_obs) >>
  simp[initial_state_def, vyperStateTheory.evaluation_state_component_equality]
QED

(* type_stmt rejects Return (SOME e) at NoneT. *)
Theorem type_stmt_none_valued_return[local]:
  (!env ret_ty s.
     ret_ty = NoneT /\ IS_SOME (type_stmt env ret_ty s) ==>
     ~stmt_valued_return s) /\
  (!env ret_ty ss.
     ret_ty = NoneT /\ IS_SOME (type_stmts env ret_ty ss) ==>
     ~stmts_valued_return ss)
Proof
  ho_match_mp_tac type_stmt_ind >>
  rw[type_stmt_def, stmt_valued_return_def] >>
  gvs[optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >> metis_tac[]
QED

(* A body typed at NoneT has no valued return. *)
Theorem type_stmts_none_valued_return:
  !env ss env'.
    type_stmts env NoneT ss = SOME env' ==> ~stmts_valued_return ss
Proof
  metis_tac[type_stmt_none_valued_return, optionTheory.IS_SOME_DEF]
QED

(* The guarded body's code from sa: the body's statements to sb, then (if
   the block is still open) the end, to st'. *)
Theorem guarded_body_code:
  !cenv nkey ut iv fbody rt sa st'.
    compile_guarded_body cenv F nkey ut iv fbody rt sa = ((), st') ==>
    ?sb. compile_stmts cenv NoLoop
           (case rt of SOME t => t | NONE => BaseT BoolT) fbody sa =
           ((), sb) /\
         cs_extends sa sb /\ cs_extends sb st'
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_guarded_body_def, comp_bind_def, comp_ignore_bind_def,
       comp_get_def, comp_return_def] >>
  Cases_on `compile_stmts cenv NoLoop
              (case rt of SOME t => t | NONE => BaseT BoolT) fbody sa` >>
  rename1 `_ = (u, sb)` >> Cases_on `u` >> simp[] >>
  `cs_extends sa sb` by
    (qspecl_then [`cenv`, `NoLoop`,
                  `case rt of SOME t => t | NONE => BaseT BoolT`, `fbody`]
       mp_tac (cj 2 compile_stmt_cs_mono) >>
     simp[cs_mono_def] >> disch_then drule >> simp[]) >>
  rw[] >>
  gvs[comp_return_def, comp_ignore_bind_def, comp_bind_def,
      cs_extends_refl] >>
  Cases_on `rt` >> gvs[] >>
  drule (SIMP_RULE std_ss [cs_appends_def] (cj 1 cs_appends_emit_helpers)) >>
  simp[]
QED

(* The body's code at the typing's return type: body_stmts_sim compiles at
   the return type the typing checks the body against, while
   compile_guarded_body compiles a function without a return type at
   BaseT BoolT. *)
Theorem guarded_body_stmts_env:
  !tops bindings ctx cx cenv fbody ret rt env_t env' sa sb.
    supported_stmts tops bindings fbody /\ body_inv tops ctx cenv cx /\
    rt = (if ret = NoneT then NONE else SOME ret) /\
    type_stmts env_t ret fbody = SOME env' /\
    compile_stmts cenv NoLoop
      (case rt of SOME t => t | NONE => BaseT BoolT) fbody sa = ((), sb) ==>
    ?cenv'. stmts_env cenv NoLoop ret fbody sa = (cenv', sb)
Proof
  rpt strip_tac >> qpat_x_assum `rt = _` SUBST_ALL_TAC >>
  `stmts_env cenv NoLoop ret fbody sa =
   stmts_env cenv NoLoop
     (case (if ret = NoneT then NONE else SOME ret) of
        SOME t => t | NONE => BaseT BoolT) fbody sa` by
    (Cases_on `ret = NoneT` >> gvs[] >>
     drule type_stmts_none_valued_return >> strip_tac >>
     drule_all stmts_env_ret_ty_no_valued_return >>
     disch_then (qspecl_then [`cenv`, `NoLoop`, `NoneT`, `BaseT BoolT`]
                   SUBST1_TAC) >> simp[]) >>
  gvs[compile_stmts_env] >>
  Cases_on `stmts_env cenv NoLoop
              (case (if ret = NoneT then NONE else SOME ret) of
                 SOME t => t | NONE => BaseT BoolT) fbody sa` >>
  gvs[]
QED
