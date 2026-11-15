(* Source outcome-consuming-step horizon, shared by call and deployment. *)
Theory sourceCallCount
Ancestors vyperState[qualified,ignore_grammar]
  vyperInterpreter vyperCallOutcome extCallOracle vyperRuntimeAccounts
  finite_map list option pair vyperTypeDeploymentMachine vyperStorageTrace
  vyperEvalOutcomeSuffix vyperEvalOutcomeReplace vyperCallOutcomeStorage
  vyperEvalPreservesScopes
Libs BasicProvers evalWalkLib

val _ = Parse.hide "body";

Definition fn_entry_run_def:
  fn_entry_run os gobs am cx nr mut all_mods args dflts vals fbody =
    let all_tenv = type_env_all_modules all_mods in
    let n_provided = LENGTH vals in
    let n_expected = LENGTH args in
    let n_missing = n_expected - n_provided in
    if n_provided > n_expected \/ n_missing > LENGTH dflts then NONE
    else
      let needed_dflts = DROP (LENGTH dflts - n_missing) dflts in
      case (if cx.in_deploy then
              evaluate_all_constants cx am cx.txn.target all_mods
            else SOME am) of
        NONE => NONE
      | SOME am_c =>
        let st0 = initial_state am_c [FEMPTY] with
                    <| outcomes := SOME os; requests := []; gas_obs := gobs |> in
        SOME (do
                send_call_value mut cx;
                dflt_vs <- eval_external_defaults cx needed_dflts;
                case bind_arguments all_tenv args (vals ++ dflt_vs) of
                  NONE => raise (Error (RuntimeError "call bind_arguments"))
                | SOME env => do
                    set_scopes [env]; lock_if_nr cx nr (is_view_mut mut);
                    eval_stmts cx fbody
                  od
              od st0)
End

Definition call_entry_run_def:
  call_entry_run os gobs am tx =
    let src_id_opt = find_function_module am tx.target tx.function_name in
    let cx = initial_evaluation_context am.sources am.layouts tx src_id_opt in
    case ALOOKUP am.sources tx.target of
      NONE => NONE
    | SOME all_mods =>
    case (case src_id_opt of
            NONE => get_self_code cx
          | SOME src_id => get_module_code cx (SOME src_id)) of
      NONE => NONE
    | SOME ts =>
    case lookup_exported_function cx am tx.function_name of
      NONE => NONE
    | SOME (mut, nr, args, dflts, ret, fbody) =>
        fn_entry_run os gobs am cx nr mut all_mods args dflts tx.args fbody
End

Definition deploy_entry_run_def:
  deploy_entry_run os gobs tops am tx =
    let mods = [(NONE,tops)] in
    let ts = case ALOOKUP mods NONE of SOME ts => ts | NONE => [] in
    case initial_immutables (type_env_all_modules mods) mods of
      NONE => NONE
    | SOME imms =>
      let am0 = am with <| immutables updated_by CONS (tx.target,imms);
                            exports updated_by CONS (tx.target,[]) |> in
      case lookup_function NONE tx.function_name Deploy ts of
        NONE => NONE
      | SOME (mut,nr,args,dflts,ret,fbody) =>
        let cx = (initial_evaluation_context ((tx.target,mods)::am0.sources)
                    am0.layouts (tx with created_in_tx := T) NONE)
                  with in_deploy := T in
        fn_entry_run os gobs am0 cx nr mut mods args dflts tx.args fbody
End

Definition empty_failed_outcome_def:
  empty_failed_outcome =
    <| co_created := 0w; co_toDelete := []; co_success := F;
       co_returnData := []; co_accounts := K empty_account_state;
       co_tStorage := empty_transient_storage; co_logs := [] |>
End

Definition probe_failed_outcome_def:
  probe_failed_outcome =
    empty_failed_outcome with
      co_accounts := K (empty_account_state with balance := 2 ** 256)
End

Definition entry_calls_within_from_def:
  entry_calls_within_from 0 os run =
    (case run os of
       NONE => T
     | SOME (_, st_end) => st_end.outcomes <> SOME []) /\
  entry_calls_within_from (SUC k) os run =
    (case run (os ++ [probe_failed_outcome]) of
       NONE => T
     | SOME (res_p, st_p) =>
         if st_p.outcomes <> SOME [] then T
         else
           let o_next =
             case run (os ++ [empty_failed_outcome]) of
               SOME (res_e, _) =>
                 if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
                    res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
                    ~NULL st_p.requests
                 then failed_outcome (LAST st_p.requests)
                 else empty_failed_outcome
             | NONE => empty_failed_outcome
           in entry_calls_within_from k (os ++ [o_next]) run)
End

Definition entry_calls_within_def:
  entry_calls_within n os run =
    entry_calls_within_from (n - LENGTH (TAKE n os)) (TAKE n os) run
End

Definition source_calls_within_def:
  source_calls_within n am tx os gobs =
    entry_calls_within n os (\xs. call_entry_run xs gobs am tx)
End

Definition deploy_source_calls_within_def:
  deploy_source_calls_within n tops am tx os gobs =
    entry_calls_within n os (\xs. deploy_entry_run xs gobs tops am tx)
End

Definition outcome_prefix_causal_def:
  outcome_prefix_causal f <=>
    !st prefix next tail res fin.
      f (st with outcomes := SOME (prefix ++ next::tail)) = (res,fin) /\
      fin.outcomes = SOME (next::tail) ==>
      !tail'. f (st with outcomes := SOME (prefix ++ tail')) =
              (res,fin with outcomes := SOME tail')
End

Theorem call_entry_run_selected:
  !os gobs am tx all_mods src cx ts mut nr args dflts ret fbody.
    src = find_function_module am tx.target tx.function_name /\
    cx = initial_evaluation_context am.sources am.layouts tx src /\
    ALOOKUP am.sources tx.target = SOME all_mods /\
    (case src of NONE => get_self_code cx
              | SOME sid => get_module_code cx (SOME sid)) = SOME ts /\
    lookup_exported_function cx am tx.function_name =
      SOME (mut,nr,args,dflts,ret,fbody) ==>
    call_entry_run os gobs am tx =
      fn_entry_run os gobs am cx nr mut all_mods args dflts tx.args fbody /\
    call_external (SOME os) gobs am tx =
      (case call_external_function (SOME os) gobs am cx nr mut ts all_mods
              args dflts tx.args fbody ret of
         (INL v,am',rqs) => (INL v,finalize_pending_deletions am',rqs)
       | (INR HaltException,am',rqs) =>
           (INR HaltException,finalize_pending_deletions am',rqs)
       | failure => failure)
Proof
  rw[call_entry_run_def, call_external_def, call_external_trace_def,
     call_external_function_def] >> gvs[] >> every_case_tac >> gvs[]
QED

Theorem deploy_entry_run_selected:
  !os gobs tops am tx imms am0 cx mut nr args dflts ret fbody.
    initial_immutables (type_env_all_modules [(NONE,tops)]) [(NONE,tops)] =
      SOME imms /\
    am0 = am with <|immutables updated_by CONS (tx.target,imms);
                   exports updated_by CONS (tx.target,[])|> /\
    lookup_function NONE tx.function_name Deploy tops =
      SOME (mut,nr,args,dflts,ret,fbody) /\
    cx = (initial_evaluation_context ((tx.target,[(NONE,tops)])::am0.sources)
            am0.layouts (tx with created_in_tx := T) NONE) with in_deploy := T ==>
    deploy_entry_run os gobs tops am tx =
      fn_entry_run os gobs am0 cx nr mut [(NONE,tops)] args dflts tx.args fbody /\
    load_contract (SOME os) gobs am tx [(NONE,tops)] [] =
      (case call_external_function (SOME os) gobs am0 cx nr mut tops [(NONE,tops)]
              args dflts tx.args fbody ret of
         (INR HaltException,am',rqs) =>
           INL (finalize_pending_deletions am',rqs)
       | (INR e,_,_) => INR e
       | (_,am',rqs) =>
           INL (finalize_pending_deletions
             (am' with sources updated_by CONS (tx.target,[(NONE,tops)])),rqs))
Proof
  rw[deploy_entry_run_def, load_contract_def, load_contract_trace_def,
     call_external_function_def] >> gvs[] >> every_case_tac >> gvs[]
QED

Theorem take_request_outcome_exhausted_replay:
  !rq st.
    take_request_outcome rq (st with outcomes := SOME []) =
    take_request_outcome rq
      (st with outcomes := SOME [failed_outcome rq])
Proof
  rw[take_request_outcome_def, take_outcome_def, failed_outcome_def] >>
  every_case_tac >> simp[]
QED

Theorem take_create_outcome_exhausted_replay:
  !kind value code st.
    take_create_outcome kind value code (st with outcomes := SOME []) =
    take_create_outcome kind value code
      (st with outcomes := SOME
        [failed_outcome (create_outcome_request kind value code st)])
Proof
  simp[take_create_outcome_def, take_outcome_def, failed_outcome_def] >>
  simp[create_outcome_request_def]
QED

Theorem precompile_call_success_exhausted_replay:
  !bt st.
    precompile_builtin bt ==>
    precompile_call_success bt (st with outcomes := SOME []) =
    precompile_call_success bt
      (st with outcomes := SOME [empty_failed_outcome])
Proof
  simp[precompile_call_success_def, empty_failed_outcome_def]
QED

Theorem fn_entry_run_agrees:
  !os gobs am cx nr mut ts all_mods args dflts vals fbody ret res st.
    fn_entry_run os gobs am cx nr mut all_mods args dflts vals fbody =
      SOME (res,st) ==>
    call_external_function (SOME os) gobs am cx nr mut ts all_mods
      args dflts vals fbody ret =
    (case res of
       INL () =>
         (case unlock_if_nr cx nr (is_view_mut mut) st of
            (INL (),s) =>
              (INL NoneV,
               abstract_machine_from_state am.sources am.exports am.layouts s,
               s.requests)
          | (INR e,s) => (INR e,am,s.requests))
     | INR (ReturnException v) =>
         (case unlock_if_nr cx nr (is_view_mut mut) st of
            (INL (),s) =>
              (case evaluate_type (type_env_all_modules all_mods) ret of
                 NONE => (INR (Error (TypeError "eval ret")),am,s.requests)
               | SOME tv =>
                 case safe_cast tv v of
                   NONE => (INR (Error (TypeError "ext cast ret")),am,s.requests)
                 | SOME v' =>
                   (INL v',
                    abstract_machine_from_state am.sources am.exports am.layouts s,
                    s.requests))
          | (INR e,s) => (INR e,am,s.requests))
     | INR HaltException =>
         (INR HaltException,
          abstract_machine_from_state am.sources am.exports am.layouts st,
          st.requests)
     | INR e => (INR e,am,st.requests))
Proof
  rw[fn_entry_run_def, Excl "lock_if_nr_def", Excl "unlock_if_nr_def",
     Excl "is_view_mut_def"] >>
  gvs[AllCaseEqs(), Excl "lock_if_nr_def", Excl "unlock_if_nr_def",
      Excl "is_view_mut_def"] >>
  imp_res_tac evaluate_all_constants_preserves_machine_static_components >>
  qmatch_assum_abbrev_tac `counter_core counter_initial = (res,st)` >>
  `storage_trace_frame counter_core` by
    simp[Abbr`counter_core`, storage_trace_frame_external_entry,
         Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  `counter_initial.storage_trace = []` by
    simp[Abbr`counter_initial`, initial_state_def] >>
  `!p. counter_core (counter_initial with storage_trace := p) =
       (res,st with storage_trace := p ++ st.storage_trace)` by
    (gen_tac >> drule_all storage_trace_frame_result >>
     disch_then (qspec_then `p` mp_tac) >>
     simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"]) >>
  `storage_trace_frame (unlock_if_nr cx nr (is_view_mut mut))` by
    simp[storage_trace_frame_optional_locks, Excl "unlock_if_nr_def",
         Excl "is_view_mut_def"] >>
  qpat_x_assum `storage_trace_frame (unlock_if_nr _ _ _)`
    (assume_tac o PURE_REWRITE_RULE [storage_trace_frame_action]) >>
  Cases_on `evaluate_module_constants_trace cx am cx.txn.target
              (constants_order all_mods)` >>
  fs[evaluate_all_constants_def, evaluate_module_constants_def,
     Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  simp[call_external_function_def, call_external_function_trace_def,
       Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  fs[Abbr`counter_core`, Abbr`counter_initial`,
     Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  Cases_on `res` >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  POP_ASSUM_LIST (K ALL_TAC) >> every_case_tac >>
  gvs[abstract_machine_from_state_storage_trace]
QED

Theorem call_entry_run_requests_agree:
  !os gobs am tx res st.
    call_entry_run os gobs am tx = SOME (res,st) ==>
    (case call_external (SOME os) gobs am tx of
       (result,am',rqs) => rqs = st.requests)
Proof
  rw[call_entry_run_def] >> gvs[AllCaseEqs()] >>
  simp[call_external_def, call_external_trace_def] >>
  qmatch_goalsub_rename_tac
    `call_external_function_trace _ _ _ _ _ _ ts _ _ _ _ _ ret` >>
  qpat_x_assum `fn_entry_run _ _ _ _ _ _ _ _ _ _ _ = _`
    (mp_tac o MATCH_MP
      (INST_TYPE [alpha |-> ``:toplevel list``] fn_entry_run_agrees)) >>
  disch_then (qspecl_then [`ts`,`ret`] mp_tac) >>
  simp[call_external_function_def] >>
  Cases_on `res` >>
  simp[unlock_if_nr_def, release_nonreentrant_lock_def,
      vyperStateTheory.record_storage_event_def,
      vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.return_def, vyperStateTheory.get_transient_storage_def,
      vyperStateTheory.update_transient_def] >>
  every_case_tac >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.bind_def,
      vyperStateTheory.record_storage_event_def,
      vyperStateTheory.get_transient_storage_def,
      vyperStateTheory.update_transient_def]
QED

Theorem entry_calls_within_from_head_cong[local]:
  !k os out run next.
    (!xs. run (out::xs) = next xs) ==>
    (entry_calls_within_from k (out::os) run <=>
     entry_calls_within_from k os next)
Proof
  Induct
  >- (rpt strip_tac >> simp[entry_calls_within_from_def]) >>
  rpt gen_tac >> strip_tac >>
  qmatch_assum_rename_tac `!xs. runner (head::xs) = next xs` >>
  `!p. entry_calls_within_from k (head::p) runner <=>
       entry_calls_within_from k p next` by
    (gen_tac >> first_assum irule >> simp[]) >>
  simp[entry_calls_within_from_def] >> every_case_tac >> gvs[]
QED

Theorem entry_calls_within_head_cong[local]:
  !n os out run next.
    (!xs. run (out::xs) = next xs) ==>
    (entry_calls_within (SUC n) (out::os) run <=>
     entry_calls_within n os next)
Proof
  rpt strip_tac >> simp[entry_calls_within_def] >>
  irule entry_calls_within_from_head_cong >> simp[]
QED

Theorem entry_calls_within_fixed_drop[local]:
  !c n os run.
    (!xs. ?res fin. run xs = SOME (res,fin) /\
                    fin.outcomes = SOME (DROP c xs)) ==>
    (entry_calls_within n os run <=> c < n)
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_assum_rename_tac
    `!xs. ?res fin. runner xs = SOME (res,fin) /\
                   fin.outcomes = SOME (DROP c xs)` >>
  `!k xs. entry_calls_within_from k xs runner <=> c < LENGTH xs + k` by
    (Induct
     >- (gen_tac >>
         qpat_x_assum `!ys. ?res fin. runner ys = SOME (res,fin) /\
                        fin.outcomes = SOME (DROP c ys)`
           (qspec_then `xs` strip_assume_tac) >>
         simp[entry_calls_within_from_def, DROP_EQ_NIL]) >>
     gen_tac >>
     qpat_x_assum `!ys. ?res fin. runner ys = SOME (res,fin) /\
                    fin.outcomes = SOME (DROP c ys)`
       (qspec_then `xs ++ [probe_failed_outcome]` strip_assume_tac) >>
     simp[entry_calls_within_from_def, DROP_EQ_NIL] >> rw[] >> decide_tac) >>
  `LENGTH (TAKE n os) <= n` by
    (simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> rw[] >> decide_tac) >>
  simp[entry_calls_within_def] >> decide_tac
QED

Theorem deploy_entry_run_requests_agree:
  !os gobs tops am tx res st am' rqs.
    deploy_entry_run os gobs tops am tx = SOME (res,st) /\
    load_contract (SOME os) gobs am tx [(NONE,tops)] [] = INL (am',rqs) ==>
    rqs = st.requests
Proof
  rw[deploy_entry_run_def] >> gvs[AllCaseEqs()] >>
  qpat_x_assum `load_contract _ _ _ _ _ _ = _` mp_tac >>
  simp[load_contract_def, load_contract_trace_def] >>
  qmatch_goalsub_rename_tac
    `call_external_function_trace _ _ _ _ _ _ ts _ _ _ _ _ ret` >>
  qpat_x_assum `fn_entry_run _ _ _ _ _ _ _ _ _ _ _ = _`
    (mp_tac o MATCH_MP
      (INST_TYPE [alpha |-> ``:toplevel list``] fn_entry_run_agrees)) >>
  disch_then (qspecl_then [`ts`,`ret`] mp_tac) >>
  simp[call_external_function_def] >>
  Cases_on `res` >>
  simp[unlock_if_nr_def, release_nonreentrant_lock_def,
      vyperStateTheory.record_storage_event_def,
      vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.return_def, vyperStateTheory.get_transient_storage_def,
      vyperStateTheory.update_transient_def] >>
  every_case_tac >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.bind_def,
      vyperStateTheory.record_storage_event_def,
      vyperStateTheory.get_transient_storage_def,
      vyperStateTheory.update_transient_def]
QED

Theorem take_request_outcome_budget_step:
  !n os out rq st res fin k.
    take_request_outcome rq (st with outcomes := SOME [out]) = (res,fin) ==>
    (entry_calls_within (SUC n) (out::os)
       (\xs. SOME ((monad_bind (take_request_outcome rq) k)
                      (st with outcomes := SOME xs))) <=>
     entry_calls_within n os
       (\xs. SOME (case res of
          INL v => k v (fin with outcomes := SOME xs)
        | INR e => (INR e,fin with outcomes := SOME xs))))
Proof
  rpt strip_tac >> irule entry_calls_within_head_cong >> gen_tac >>
  gvs[take_request_outcome_def, take_outcome_def,
      vyperStateTheory.bind_def, AllCaseEqs()] >>
  every_case_tac >> gvs[] >> rpt (PURE_CASE_TAC >> gvs[])
QED

Theorem take_create_outcome_budget_step:
  !n os out kind value code st res fin k.
    take_create_outcome kind value code (st with outcomes := SOME [out]) =
      (res,fin) ==>
    (entry_calls_within (SUC n) (out::os)
       (\xs. SOME ((monad_bind (take_create_outcome kind value code) k)
                      (st with outcomes := SOME xs))) <=>
     entry_calls_within n os
       (\xs. SOME (case res of
          INL v => k v (fin with outcomes := SOME xs)
        | INR e => (INR e,fin with outcomes := SOME xs))))
Proof
  rpt strip_tac >> irule entry_calls_within_head_cong >> gen_tac >>
  gvs[vyperStateTheory.bind_def, take_create_outcome_def,
      take_outcome_def, AllCaseEqs()] >>
  gvs[create_outcome_request_def, vyperStateTheory.bind_def, AllCaseEqs()] >>
  rpt (PURE_CASE_TAC >> gvs[])
QED

Theorem precompile_call_success_budget_step:
  !n os out bt st res fin k.
    precompile_builtin bt /\
    precompile_call_success bt (st with outcomes := SOME [out]) = (res,fin) ==>
    (entry_calls_within (SUC n) (out::os)
       (\xs. SOME ((monad_bind (precompile_call_success bt) k)
                      (st with outcomes := SOME xs))) <=>
     entry_calls_within n os
       (\xs. SOME (case res of
          INL v => k v (fin with outcomes := SOME xs)
        | INR e => (INR e,fin with outcomes := SOME xs))))
Proof
  rpt strip_tac >> irule entry_calls_within_head_cong >> gen_tac >>
  gvs[precompile_call_success_def, vyperStateTheory.check_def,
      vyperStateTheory.assert_def, vyperStateTheory.bind_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def,
      AllCaseEqs()] >> rpt (PURE_CASE_TAC >> gvs[])
QED


Theorem take_request_outcome_budget_unit:
  !n os rq st.
    entry_calls_within n os
      (\xs. SOME (take_request_outcome rq (st with outcomes := SOME xs))) <=>
    1 < n
Proof
  rpt gen_tac >> irule entry_calls_within_fixed_drop >> gen_tac >>
  Cases_on `xs` >>
  simp[take_request_outcome_def, take_outcome_def, DROP_def] >>
  rpt (PURE_CASE_TAC >> gvs[])
QED

Theorem take_create_outcome_budget_unit:
  !n os kind value code st.
    entry_calls_within n os
      (\xs. SOME (take_create_outcome kind value code
                    (st with outcomes := SOME xs))) <=> 1 < n
Proof
  rpt gen_tac >> irule entry_calls_within_fixed_drop >> gen_tac >>
  Cases_on `xs` >>
  simp[take_create_outcome_def, take_outcome_def, DROP_def] >>
  rpt (PURE_CASE_TAC >> gvs[])
QED

Theorem precompile_call_success_budget_unit:
  !n os bt st.
    entry_calls_within n os
      (\xs. SOME (precompile_call_success bt (st with outcomes := SOME xs))) <=>
    (if precompile_builtin bt then 1 < n else 0 < n)
Proof
  rpt gen_tac >> Cases_on `precompile_builtin bt` >> simp[] >>
  irule entry_calls_within_fixed_drop >> gen_tac >> Cases_on `xs` >>
  simp[precompile_call_success_def, vyperStateTheory.check_def,
       vyperStateTheory.assert_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, DROP_def] >>
  rpt (PURE_CASE_TAC >> gvs[])
QED

Theorem fn_entry_run_probe_budget_step:
  !k os gobs am cx nr mut mods args dflts vals fbody res_p st_p o_next.
    fn_entry_run (os ++ [probe_failed_outcome]) gobs am cx nr mut mods
      args dflts vals fbody = SOME (res_p,st_p) /\
    st_p.outcomes = SOME [] /\
    o_next =
      (case fn_entry_run (os ++ [empty_failed_outcome]) gobs am cx
              nr mut mods args dflts vals fbody of
         SOME (res_e,_) =>
           if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
              res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
              ~NULL st_p.requests
           then failed_outcome (LAST st_p.requests)
           else empty_failed_outcome
       | NONE => empty_failed_outcome) ==>
    (entry_calls_within (LENGTH os + SUC k) os
       (\xs. fn_entry_run xs gobs am cx nr mut mods args dflts vals fbody) <=>
     entry_calls_within (LENGTH os + SUC k) (os ++ [o_next])
       (\xs. fn_entry_run xs gobs am cx nr mut mods args dflts vals fbody))
Proof
  rpt strip_tac >>
  `TAKE (LENGTH os + SUC k) os = os` by
    (irule TAKE_LENGTH_TOO_LONG >> decide_tac) >>
  `TAKE (LENGTH os + SUC k) (os ++ [o_next]) = os ++ [o_next]` by
    (irule TAKE_LENGTH_TOO_LONG >> simp[] >> decide_tac) >>
  `LENGTH os + SUC k - LENGTH os = SUC k` by decide_tac >>
  `LENGTH os + SUC k - LENGTH (os ++ [o_next]) = k` by
    (simp[] >> decide_tac) >>
  simp[entry_calls_within_def, entry_calls_within_from_def]
QED

Theorem entry_calls_within_erase_trace_cong:
  !n os run1 run2.
    (!xs. OPTION_MAP (\(r,s). (r,erase_storage_trace s)) (run1 xs) =
          OPTION_MAP (\(r,s). (r,erase_storage_trace s)) (run2 xs)) ==>
    (entry_calls_within n os run1 <=> entry_calls_within n os run2)
Proof
  rpt gen_tac >> strip_tac >>
  `!xs. OPTION_MAP (\(r,s). (r,s.outcomes,s.requests)) (run1 xs) =
        OPTION_MAP (\(r,s). (r,s.outcomes,s.requests)) (run2 xs)` by
    (gen_tac >>
     qpat_x_assum `!ys. OPTION_MAP _ (run1 ys) = _`
       (qspec_then `xs` mp_tac) >>
     Cases_on `run1 xs` >> Cases_on `run2 xs` >>
     simp[OPTION_MAP_DEF] >>
     rename1 `run1 xs = SOME rp1` >>
     rename1 `run2 xs = SOME rp2` >>
     Cases_on `rp1` >> Cases_on `rp2` >>
     gvs[vyperStateTheory.erase_storage_trace_def,
         vyperStateTheory.evaluation_state_component_equality]) >>
  `!k xs. entry_calls_within_from k xs run1 <=>
          entry_calls_within_from k xs run2` by
    (Induct
     >- (gen_tac >>
         qpat_x_assum `!ys. OPTION_MAP (\(r,s). (r,s.outcomes,s.requests)) (run1 ys) = _`
           (qspec_then `xs` mp_tac) >>
         Cases_on `run1 xs` >> Cases_on `run2 xs` >>
         simp[entry_calls_within_from_def, OPTION_MAP_DEF] >>
         every_case_tac >>
         gvs[]) >>
     gen_tac >>
     qpat_assum `!ys. OPTION_MAP (\(r,s). (r,s.outcomes,s.requests)) (run1 ys) = _`
       (qspec_then `xs ++ [probe_failed_outcome]` assume_tac) >>
     qpat_x_assum `!ys. OPTION_MAP (\(r,s). (r,s.outcomes,s.requests)) (run1 ys) = _`
       (qspec_then `xs ++ [empty_failed_outcome]` assume_tac) >>
     simp[entry_calls_within_from_def] >>
     Cases_on `run1 (xs ++ [probe_failed_outcome])` >>
     Cases_on `run2 (xs ++ [probe_failed_outcome])` >>
     gvs[OPTION_MAP_DEF] >>
     rename1 `run1 (xs ++ [probe_failed_outcome]) = SOME probe1` >>
     rename1 `run2 (xs ++ [probe_failed_outcome]) = SOME probe2` >>
     Cases_on `probe1` >> Cases_on `probe2` >> gvs[] >>
     Cases_on `run1 (xs ++ [empty_failed_outcome])` >>
     Cases_on `run2 (xs ++ [empty_failed_outcome])` >>
     gvs[OPTION_MAP_DEF] >>
     rename1 `run1 (xs ++ [empty_failed_outcome]) = SOME empty1` >>
     rename1 `run2 (xs ++ [empty_failed_outcome]) = SOME empty2` >>
     Cases_on `empty1` >> Cases_on `empty2` >> gvs[]) >>
  simp[entry_calls_within_def]
QED

Theorem outcome_prefix_causal_frame[local]:
  !f.
    (!st os. f (st with outcomes := os) =
      (FST (f st),(SND (f st)) with outcomes := os)) ==>
    outcome_prefix_causal f
Proof
  rpt gen_tac >> strip_tac >> rw[outcome_prefix_causal_def] >>
  qpat_x_assum `!s os. _`
    (qspecl_then [`st`,`SOME (prefix ++ next::tail)`] mp_tac) >>
  Cases_on `f st` >> simp[] >> strip_tac >> gvs[APPEND_EQ_SELF]
QED

Theorem outcome_prefix_causal_result_bind[local]:
  !f g.
    outcomes_suffix f /\ outcome_prefix_causal f /\
    (!s r t. f s = (r,t) ==>
       outcomes_suffix (g r) /\ outcome_prefix_causal (g r)) ==>
    outcome_prefix_causal (\st. case f st of (r,t) => g r t)
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once outcome_prefix_causal_def] >>
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `f (st with outcomes := SOME (prefix ++ next::tail))` >>
  rename1 `f (st with outcomes := SOME (prefix ++ next::tail)) = (head_res,mid)` >>
  gvs[] >>
  qpat_x_assum `!s r t. f s = (r,t) ==> _`
    (qspecl_then [`st with outcomes := SOME (prefix ++ next::tail)`,
                  `head_res`,`mid`] mp_tac) >>
  simp[] >> strip_tac >>
  `outcome_suffix (SOME (prefix ++ next::tail)) mid.outcomes` by
    (qpat_x_assum `outcomes_suffix f` mp_tac >>
     simp[outcomes_suffix_def] >>
     disch_then (qspec_then `st with outcomes := SOME (prefix ++ next::tail)`
                  mp_tac) >> simp[]) >>
  `outcome_suffix mid.outcomes (SOME (next::tail))` by
    (qpat_x_assum `outcomes_suffix (g head_res)` mp_tac >>
     simp[outcomes_suffix_def] >>
     disch_then (qspec_then `mid` mp_tac) >> simp[]) >>
  `?used2. mid.outcomes = SOME (used2 ++ next::tail)` by
    (qpat_x_assum `outcome_suffix mid.outcomes (SOME (next::tail))` mp_tac >>
     simp[outcome_suffix_def]) >>
  `?used1. prefix = used1 ++ used2` by
    (qpat_x_assum `outcome_suffix (SOME (prefix ++ next::tail)) mid.outcomes`
       mp_tac >> simp[outcome_suffix_def, APPEND_ASSOC]) >>
  `mid with outcomes := SOME (used2 ++ next::tail) = mid` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_x_assum `outcome_prefix_causal (g head_res)` mp_tac >>
  simp[outcome_prefix_causal_def] >>
  disch_then (qspecl_then [`mid`,`used2`,`next`,`tail`,`res`,`fin`] mp_tac) >>
  simp[] >> disch_then (qspec_then `tail'` assume_tac) >>
  Cases_on `used2`
  >- (qpat_x_assum `outcome_prefix_causal f` mp_tac >>
      simp[outcome_prefix_causal_def] >>
      disch_then (qspecl_then [`st`,`prefix`,`next`,`tail`,`head_res`,`mid`] mp_tac) >>
      simp[] >> disch_then (qspec_then `tail'` mp_tac) >> gvs[]) >>
  rename1 `mid.outcomes = SOME ((out::rest) ++ next::tail)` >>
  qpat_x_assum `prefix = used1 ++ out::rest` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  qpat_x_assum `outcome_prefix_causal f` mp_tac >>
  simp[outcome_prefix_causal_def] >>
  disch_then (qspecl_then [`st`,`used1`,`out`,`rest ++ next::tail`,
                          `head_res`,`mid`] mp_tac) >>
  asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND] >>
  disch_then (qspec_then `out::(rest ++ tail')` mp_tac) >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem outcome_prefix_causal_bind_guarded[local]:
  !f g.
    outcomes_suffix f /\ outcome_prefix_causal f /\
    (!st v mid. f st = (INL v,mid) ==>
       outcomes_suffix (g v) /\ outcome_prefix_causal (g v)) ==>
    outcome_prefix_causal (monad_bind f g)
Proof
  rpt gen_tac >> strip_tac >>
  `monad_bind f g =
    (\st. case f st of (ans,mid) =>
      (case ans of INL v => g v | INR e => raise e) mid)` by
    (simp[FUN_EQ_THM, vyperStateTheory.bind_def] >> gen_tac >>
     Cases_on `f st` >> rename1 `f st = (ans,mid)` >>
     Cases_on `ans` >> simp[vyperStateTheory.raise_def]) >>
  pop_assum SUBST1_TAC >>
  ho_match_mp_tac outcome_prefix_causal_result_bind >>
  simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `f seed = (answer,midpoint)` >>
  Cases_on `answer` >> simp[] >>
  CONV_TAC (DEPTH_CONV ETA_CONV)
  >- (rename1 `f seed = (INL value,midpoint)` >>
      qpat_x_assum `!st v mid. f st = (INL v,mid) ==> _`
        (qspecl_then [`seed`,`value`,`midpoint`] mp_tac) >> simp[]) >>
  conj_tac
  >- simp[outcomes_suffix_def, vyperStateTheory.raise_def] >>
  irule outcome_prefix_causal_frame >>
  simp[vyperStateTheory.raise_def]
QED

Theorem outcome_prefix_causal_bind[local]:
  !f g.
    outcomes_suffix f /\ outcome_prefix_causal f /\
    (!v. outcomes_suffix (g v) /\ outcome_prefix_causal (g v)) ==>
    outcome_prefix_causal (monad_bind f g)
Proof
  rpt gen_tac >> strip_tac >>
  irule outcome_prefix_causal_bind_guarded >> simp[]
QED

Theorem outcome_prefix_causal_primitive_steps[local]:
  (!rq. outcome_prefix_causal (take_request_outcome rq)) /\
  (!kind value code.
     outcome_prefix_causal (take_create_outcome kind value code)) /\
  (!bt. outcome_prefix_causal (precompile_call_success bt))
Proof
  conj_tac
  >- (gen_tac >> rw[outcome_prefix_causal_def] >>
      Cases_on `prefix` >>
      gvs[take_request_outcome_def, take_outcome_def, AllCaseEqs(),
          APPEND_EQ_SELF, vyperStateTheory.evaluation_state_component_equality] >>
      rpt (FULL_CASE_TAC >>
        gvs[APPEND_EQ_SELF, vyperStateTheory.evaluation_state_component_equality])) >>
  conj_tac
  >- (rpt gen_tac >> rw[outcome_prefix_causal_def] >>
      Cases_on `prefix` >>
      gvs[take_create_outcome_def, create_outcome_request_def, take_outcome_def,
          AllCaseEqs(), APPEND_EQ_SELF,
          vyperStateTheory.evaluation_state_component_equality] >>
      rpt (FULL_CASE_TAC >>
        gvs[APPEND_EQ_SELF, vyperStateTheory.evaluation_state_component_equality])) >>
  gen_tac >> rw[outcome_prefix_causal_def] >>
  Cases_on `prefix` >>
  gvs[precompile_call_success_def, vyperStateTheory.check_def,
      vyperStateTheory.assert_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, AllCaseEqs(), APPEND_EQ_SELF,
      vyperStateTheory.evaluation_state_component_equality] >>
  rpt (FULL_CASE_TAC >>
    gvs[APPEND_EQ_SELF, vyperStateTheory.evaluation_state_component_equality])
QED

val PREFIX_RESULT_TAC =
  conj_tac
  >- simp[outcomes_suffix_def, vyperStateTheory.return_def,
          vyperStateTheory.raise_def] >>
  irule outcome_prefix_causal_frame >>
  simp[vyperStateTheory.return_def, vyperStateTheory.raise_def];

val PREFIX_CLEANUP_TAC =
  rewrite_tac[vyperStateTheory.ignore_bind_def] >>
  conj_tac
  >- (match_mp_tac outcomes_suffix_bind_guarded >> conj_tac
      >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >>
      simp[outcomes_suffix_def, vyperStateTheory.return_def,
           vyperStateTheory.raise_def]) >>
  match_mp_tac outcome_prefix_causal_bind >> conj_tac
  >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> gen_tac >> PREFIX_RESULT_TAC;

Theorem outcome_prefix_causal_handlers[local]:
  (!f h.
     outcomes_suffix f /\ outcome_prefix_causal f /\
     (!e. outcomes_suffix (h e) /\ outcome_prefix_causal (h e)) ==>
     outcome_prefix_causal (try f h)) /\
  (!f cleanup.
     outcomes_suffix f /\ outcome_prefix_causal f /\
     outcomes_suffix cleanup /\ outcome_prefix_causal cleanup ==>
     outcome_prefix_causal (finally f cleanup)) /\
  (!f cleanup.
     outcomes_suffix f /\ outcome_prefix_causal f /\
     outcomes_suffix cleanup /\ outcome_prefix_causal cleanup ==>
     outcome_prefix_causal (finally_unless_halt f cleanup))
Proof
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `try f h = (\st. case f st of (ans,mid) =>
         (case ans of INL v => return v | INR e => h e) mid)` by
        (simp[FUN_EQ_THM, vyperStateTheory.try_def] >> gen_tac >>
         Cases_on `f st` >> rename1 `f st = (ans,mid)` >>
         Cases_on `ans` >> simp[vyperStateTheory.return_def]) >>
      pop_assum SUBST1_TAC >>
      ho_match_mp_tac outcome_prefix_causal_result_bind >> simp[] >>
      rpt gen_tac >> strip_tac >> rename1 `f seed = (answer,midpoint)` >>
      Cases_on `answer` >> simp[] >> CONV_TAC (DEPTH_CONV ETA_CONV)
      >- PREFIX_RESULT_TAC >>
      rename1 `f seed = (INR fault,midpoint)` >>
      qpat_x_assum `!e. _ /\ _` (qspec_then `fault` ACCEPT_TAC)) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `finally f cleanup = (\st. case f st of (ans,mid) =>
         (case ans of
            INL v => ignore_bind cleanup (return v)
          | INR e => ignore_bind cleanup (raise e)) mid)` by
        (simp[FUN_EQ_THM, vyperStateTheory.finally_def] >> gen_tac >>
         Cases_on `f st` >> rename1 `f st = (ans,mid)` >>
         Cases_on `ans` >> simp[]) >>
      pop_assum SUBST1_TAC >>
      ho_match_mp_tac outcome_prefix_causal_result_bind >> simp[] >>
      rpt gen_tac >> strip_tac >> rename1 `f seed = (answer,midpoint)` >>
      Cases_on `answer` >> simp[] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      PREFIX_CLEANUP_TAC) >>
  rpt gen_tac >> strip_tac >>
  `finally_unless_halt f cleanup = (\st. case f st of (ans,mid) =>
     (case ans of
        INL v => ignore_bind cleanup (return v)
      | INR e => if e = HaltException then raise HaltException
                 else ignore_bind cleanup (raise e)) mid)` by
    (simp[FUN_EQ_THM, vyperStateTheory.finally_unless_halt_def] >> gen_tac >>
     Cases_on `f st` >> rename1 `f st = (ans,mid)` >>
     Cases_on `ans` >> simp[vyperStateTheory.raise_def] >>
     rename1 `f st = (INR caught_error,mid)` >>
     Cases_on `caught_error` >> simp[vyperStateTheory.raise_def]) >>
  pop_assum SUBST1_TAC >>
  ho_match_mp_tac outcome_prefix_causal_result_bind >> simp[] >>
  rpt gen_tac >> strip_tac >> rename1 `f seed = (answer,midpoint)` >>
  Cases_on `answer` >> simp[] >> CONV_TAC (DEPTH_CONV ETA_CONV)
  >- PREFIX_CLEANUP_TAC >>
  rename1 `f seed = (INR fault,midpoint)` >>
  Cases_on `fault` >> simp[] >> CONV_TAC (DEPTH_CONV ETA_CONV)
  >~ [`outcomes_suffix (raise HaltException) /\ _`] >- PREFIX_RESULT_TAC >>
  PREFIX_CLEANUP_TAC
QED

val prefix_atomic_defs =
  map (fn name => oneline (DB.fetch "vyperState" name))
    ["return_def", "raise_def", "bind_def", "ignore_bind_def",
     "assert_def", "check_def", "type_check_def", "check_not_static_def",
     "record_storage_event_def", "record_storage_backend_def",
     "get_accounts_def", "update_accounts_def", "get_transient_storage_def",
     "update_transient_def", "append_logs_def", "push_log_def",
     "get_pending_deletions_def", "update_pending_deletions_def",
     "get_storage_backend_def", "set_storage_backend_def",
     "read_storage_slot_def", "write_storage_slot_def",
     "get_address_immutables_def", "get_immutables_def",
     "set_address_immutables_def", "set_immutable_def", "set_global_def",
     "lookup_global_def", "lookup_flag_mem_def",
     "get_scopes_def", "set_scopes_def", "push_scope_def", "pop_scope_def",
     "push_scope_with_var_def", "new_variable_def",
     "lift_option_type_def", "lift_option_def", "lift_sum_def",
     "lift_sum_runtime_def", "read_result_def", "read_place_def",
     "place_type_value_def", "write_place_def", "get_place_def",
     "conditional_result_def", "result_array_length_def",
     "extend_storage_place_def", "extend_place_def", "select_result_def",
     "append_place_def", "pop_place_def"] @
  map (fn name => oneline (DB.fetch "vyperInterpreter" name))
    ["frame_call_value_def", "transfer_value_def", "push_function_def",
     "pop_function_def", "handle_loop_exception_def", "handle_function_def",
     "acquire_nonreentrant_lock_def", "release_nonreentrant_lock_def",
     "next_gas_reading_def", "array_iterator_results_def"] @
  [oneline vyperCreateTheory.check_create_blueprint_def,
   oneline adopt_call_outcome_def, extCallOracleTheory.adopt_outcome_def,
   extCallOracleTheory.adopt_outcome_deletions_def];

val prefix_input_facts = List.concat (map (CONJUNCTS o SPEC_ALL)
  [outcomes_replace_return, outcomes_replace_raise, outcomes_replace_basic,
   outcomes_replace_lifts, outcomes_replace_storage_backend,
   outcomes_replace_read_storage_slot, outcomes_replace_write_storage_slot,
   outcomes_replace_get_address_immutables, outcomes_replace_get_immutables,
   outcomes_replace_read_place, outcomes_replace_read_result,
   outcomes_replace_read_results, outcomes_replace_place_type_value,
   outcomes_replace_conditional_result,
   outcomes_replace_set_address_immutables, outcomes_replace_set_immutable,
   outcomes_replace_write_place, outcomes_replace_scopes,
   outcomes_replace_new_variable, outcomes_replace_handlers,
   outcomes_replace_get_place, outcomes_replace_resolve_array_element,
   outcomes_replace_lookup_flag_mem, outcomes_replace_lookup_global,
   outcomes_replace_result_array_length, outcomes_replace_array_iterator_results,
   outcomes_replace_extend_storage_place, outcomes_replace_extend_place,
   outcomes_replace_select_result, outcomes_replace_append_place,
   outcomes_replace_pop_place, outcomes_replace_next_gas_reading]);

val PREFIX_ATOMIC_FRAME_TAC =
  irule outcome_prefix_causal_frame >> rpt gen_tac >>
  FIRST [FIRST (map MATCH_ACCEPT_TAC prefix_input_facts),
    (simp_tac (srw_ss()) prefix_atomic_defs >>
     rpt (FULL_CASE_TAC >>
       gvs (vyperStateTheory.evaluation_state_component_equality ::
            prefix_atomic_defs)))];

Theorem outcome_prefix_causal_basic[local]:
  outcome_prefix_causal (return v) /\
  outcome_prefix_causal (raise e) /\
  outcome_prefix_causal (check b msg) /\
  outcome_prefix_causal (get_storage_backend cx tr) /\
  outcome_prefix_causal (read_result cx r)
Proof
  rpt conj_tac >> PREFIX_ATOMIC_FRAME_TAC
QED

Theorem outcome_prefix_causal_read_results[local]:
  !cx vs. outcome_prefix_causal (read_results cx vs)
Proof
  rpt gen_tac >> irule outcome_prefix_causal_frame >>
  MATCH_ACCEPT_TAC outcomes_replace_read_results
QED

Theorem outcome_prefix_causal_write_place[local]:
  outcome_prefix_causal (write_place cx p v)
Proof
  rpt gen_tac >> irule outcome_prefix_causal_frame >>
  MATCH_ACCEPT_TAC outcomes_replace_write_place
QED

Theorem outcome_prefix_causal_read_place[local]:
  outcome_prefix_causal (read_place cx p)
Proof
  rpt gen_tac >> irule outcome_prefix_causal_frame >>
  MATCH_ACCEPT_TAC outcomes_replace_read_place
QED

Theorem outcome_prefix_causal_place_type[local]:
  outcome_prefix_causal (place_type_value cx p)
Proof
  rpt gen_tac >> irule outcome_prefix_causal_frame >>
  MATCH_ACCEPT_TAC outcomes_replace_place_type_value
QED

Theorem outcome_prefix_causal_place_primitives[local]:
  outcome_prefix_causal (lift_sum x) /\
  outcome_prefix_causal (lift_option_type opt msg) /\
  outcome_prefix_causal (type_check b msg) /\
  outcome_prefix_causal get_scopes /\
  outcome_prefix_causal (set_scopes sc) /\
  outcome_prefix_causal (get_immutables cx src) /\
  outcome_prefix_causal (set_immutable cx src id tv v)
Proof
  rpt conj_tac >> PREFIX_ATOMIC_FRAME_TAC
QED

val prefix_suffix_facts = List.concat (map (CONJUNCTS o SPEC_ALL)
  [eval_outcomes_suffix_with_results, outcomes_suffix_ext_call,
   outcomes_suffix_send, outcomes_suffix_raw_call, outcomes_suffix_create,
   outcomes_suffix_precompile_call_success]) @
  map (GEN_ALL o MATCH_MP outcomes_suffix_frame o SPEC_ALL)
    (List.concat (map (CONJUNCTS o SPEC_ALL)
      [outcomes_frame_read_results, outcomes_frame_places,
       outcomes_frame_write_place, outcomes_frame_append_place,
       outcomes_frame_pop_place, outcomes_frame_resolve_array, outcomes_frame_reads,
       outcomes_frame_primitives, outcomes_frame_handlers,
       outcomes_frame_return, outcomes_frame_raise, outcomes_frame_static,
       outcomes_frame_adopt]));

val prefix_leaf_facts = List.concat (map (CONJUNCTS o SPEC_ALL)
  [outcome_prefix_causal_basic, outcome_prefix_causal_read_results,
   outcome_prefix_causal_write_place,
   outcome_prefix_causal_read_place, outcome_prefix_causal_place_type,
   outcome_prefix_causal_place_primitives,
   outcome_prefix_causal_primitive_steps]);

val prefix_rules = map SPEC_ALL
  ([outcome_prefix_causal_bind_guarded, outcomes_suffix_bind_guarded,
    outcomes_suffix_try, outcomes_suffix_finally,
    outcomes_suffix_finally_unless_halt] @
   CONJUNCTS outcome_prefix_causal_handlers);

val prefix_net = evalWalkLib.walk_net prefix_rules
  (map (fn th => (concl (SPEC_ALL th), MATCH_ACCEPT_TAC th))
    (prefix_leaf_facts @ prefix_suffix_facts));

fun PREFIX_ATOM_TAC (g as (_,w)) =
  let val (prop,args) = strip_comb w
      val computation = hd args
      val head = fst (strip_comb computation)
      val name = #Name (dest_thy_const head)
      val names = map (fn th => #Name (dest_thy_const
        (fst (strip_comb (lhs (concl (SPEC_ALL th))))))) prefix_atomic_defs
  in
    if List.exists (fn n => n = name) names andalso
       not (List.exists (fn n => n = name) ["bind","ignore_bind"])
    then
      (if #Name (dest_thy_const prop) = "outcome_prefix_causal"
       then PREFIX_ATOMIC_FRAME_TAC
       else (simp_tac (srw_ss()) (outcomes_suffix_def :: prefix_atomic_defs) >>
         rpt (FULL_CASE_TAC >> gvs prefix_atomic_defs))) g
    else NO_TAC g
  end;

fun PREFIX_STEP g = FIRST
  [CONV_TAC (HO_REWR_CONV FORALL_PROD), gen_tac,
   evalWalkLib.IH_TAC {stop = K false, normalise = I},
   (fn goal as (_,w) => FIRST (Net.match w prefix_net) goal),
   CONV_TAC (RAND_CONV (CHANGED_CONV evalWalkLib.head_conv)),
   CONV_TAC (RAND_CONV (REWR_CONV vyperStateTheory.ignore_bind_def)),
   CONV_TAC (RAND_CONV (REWR_CONV switch_BoolV_def)),
   CONV_TAC (RAND_CONV (evalWalkLib.unfold_conv
     [oneline vyperStateTheory.append_place_def,
      oneline vyperStateTheory.pop_place_def])),
   CHANGED_TAC PREFIX_ATOM_TAC,
   strip_tac, conj_tac, evalWalkLib.HEAD_CASE_TAC] g;

Theorem source_prefix_joint_bind[local]:
  !f g.
    (outcomes_suffix f /\ outcome_prefix_causal f) /\
    (!v. outcomes_suffix (g v) /\ outcome_prefix_causal (g v)) ==>
    (outcomes_suffix (monad_bind f g) /\
     outcome_prefix_causal (monad_bind f g))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (match_mp_tac outcomes_suffix_bind_guarded >> simp[]) >>
  match_mp_tac outcome_prefix_causal_bind >> simp[]
QED

Theorem source_prefix_joint_bind_guarded[local]:
  !f g.
    (outcomes_suffix f /\ outcome_prefix_causal f) /\
    (!st v mid. f st = (INL v,mid) ==>
       outcomes_suffix (g v) /\ outcome_prefix_causal (g v)) ==>
    (outcomes_suffix (monad_bind f g) /\
     outcome_prefix_causal (monad_bind f g))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (match_mp_tac outcomes_suffix_bind_guarded >> metis_tac[]) >>
  match_mp_tac outcome_prefix_causal_bind_guarded >> metis_tac[]
QED

val joint_leaf_tac =
  conj_tac
  >- FIRST (map MATCH_ACCEPT_TAC prefix_suffix_facts) >>
  FIRST (map MATCH_ACCEPT_TAC prefix_leaf_facts);

fun JOINT_STEP g = FIRST
  [joint_leaf_tac, match_mp_tac source_prefix_joint_bind,
   CONV_TAC (HO_REWR_CONV FORALL_PROD), gen_tac,
   CHANGED_TAC (BETA_TAC >> simp_tac bool_ss []),
   CONV_TAC (BINOP_CONV (RAND_CONV (CHANGED_CONV evalWalkLib.head_conv))),
   CONV_TAC (BINOP_CONV (RAND_CONV
     (REWR_CONV vyperStateTheory.ignore_bind_def))),
   conj_tac] g;

Theorem outcome_prefix_causal_place_actions[local]:
  (!cx p v. outcome_prefix_causal (append_place cx p v)) /\
  (!cx p. outcome_prefix_causal (pop_place cx p))
Proof
  rpt conj_tac >> rpt gen_tac >> irule outcome_prefix_causal_frame >>
  FIRST [MATCH_ACCEPT_TAC outcomes_replace_append_place,
         MATCH_ACCEPT_TAC outcomes_replace_pop_place]
QED

Theorem outcome_prefix_causal_call_steps[local]:
  outcome_prefix_causal (take_call_outcome target calldata value_opt) /\
  outcome_prefix_causal (take_delegate_outcome target calldata value_opt)
Proof
  conj_tac >>
  simp_tac bool_ss [outcome_prefix_causal_def,
    take_call_outcome_def, take_delegate_outcome_def,
    delegate_outcome_request_def, call_outcome_request_def] >>
  rpt gen_tac >> strip_tac >>
  mp_tac (cj 1 outcome_prefix_causal_primitive_steps) >>
  simp_tac bool_ss [outcome_prefix_causal_def] >>
  disch_then (drule_at Any) >> gvs[] >> metis_tac[]
QED

val prefix_net = evalWalkLib.walk_net prefix_rules
  (map (fn th => (concl (SPEC_ALL th), MATCH_ACCEPT_TAC th))
    (CONJUNCTS outcome_prefix_causal_call_steps @
     [outcomes_suffix_take, outcomes_suffix_take_delegate] @
     prefix_leaf_facts @ prefix_suffix_facts));

fun EXTERNAL_STEP g = FIRST
  [(fn goal as (_,w) => FIRST (Net.match w prefix_net) goal),
   PREFIX_STEP] g;

Theorem outcome_prefix_causal_call_oracle[local]:
  outcome_prefix_causal
    (bind (take_call_outcome target calldata value_opt) (\(rq, outcome).
       ignore_bind
         (if call_outcome_success outcome then return ()
          else raise (Error (RevertData (call_outcome_return_data outcome))))
         (ignore_bind (adopt_call_outcome rq outcome)
            (return (call_outcome_return_data outcome)))))
Proof
  rpt EXTERNAL_STEP
QED

Theorem outcome_prefix_causal_call_effects[local]:
  outcome_prefix_causal
    (eval_ext_call_effects cx target calldata value_opt gas accounts)
Proof
  mp_tac outcome_prefix_causal_call_oracle >>
  simp_tac (srw_ss()) [outcome_prefix_causal_def, eval_ext_call_effects_def,
    vyperStateTheory.bind_def, vyperStateTheory.return_def,
    vyperStateTheory.ignore_bind_def]
QED

Theorem source_prefix_suffix_call_effects[local]:
  outcomes_suffix
    (eval_ext_call_effects cx target calldata value_opt gas accounts)
Proof
  simp_tac bool_ss [eval_ext_call_effects_def, LET_THM] >>
  rpt (FIRST [MATCH_ACCEPT_TAC outcomes_suffix_read, EXTERNAL_STEP])
QED

Theorem outcome_prefix_causal_external_primitives[local]:
  outcome_prefix_causal get_accounts /\
  outcome_prefix_causal (frame_call_value cx value_opt) /\
  outcome_prefix_causal (lift_sum_runtime x) /\
  outcome_prefix_causal (lift_option opt msg) /\
  outcome_prefix_causal (adopt_call_outcome rq outcome)
Proof
  rpt conj_tac >> PREFIX_ATOMIC_FRAME_TAC
QED

val external_prefix_leaves =
  CONJUNCTS outcome_prefix_causal_external_primitives @
  CONJUNCTS outcome_prefix_causal_call_steps @
  [outcome_prefix_causal_call_effects] @ prefix_leaf_facts;
val external_suffix_leaves =
  [source_prefix_suffix_call_effects, outcomes_suffix_take,
   outcomes_suffix_take_delegate] @ prefix_suffix_facts;
val external_leaf_net = evalWalkLib.walk_net []
  (map (fn th => (concl (SPEC_ALL th), MATCH_ACCEPT_TAC th))
    (external_suffix_leaves @ external_prefix_leaves));
fun EXTERNAL_LEAF_TAC (g as (_,w)) = FIRST (Net.match w external_leaf_net) g;
val external_joint_leaf_tac = conj_tac
  >- FIRST [EXTERNAL_LEAF_TAC, PREFIX_ATOM_TAC] >>
  FIRST [EXTERNAL_LEAF_TAC, PREFIX_ATOM_TAC];
Theorem source_prefix_extcall_value_joint[local]:
  outcomes_suffix ((if static then return NONE else
    case ext_call_kwarg EKValue opts args of
      NONE => return (SOME 0)
    | SOME v => bind (lift_option_type (dest_NumV v) "ExtCall value not int")
                    (\n. return (SOME n)))) /\
  outcome_prefix_causal ((if static then return NONE else
    case ext_call_kwarg EKValue opts args of
      NONE => return (SOME 0)
    | SOME v => bind (lift_option_type (dest_NumV v) "ExtCall value not int")
                    (\n. return (SOME n))))
Proof
  simp_tac bool_ss [LET_THM] >> Cases_on `static` >>
  simp_tac bool_ss []
  >- external_joint_leaf_tac >>
  Cases_on `ext_call_kwarg EKValue opts args` >> simp_tac (srw_ss()) []
  >- external_joint_leaf_tac >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >>
  gen_tac >> BETA_TAC >> external_joint_leaf_tac
QED

Theorem source_prefix_extcall_return_joint[local]:
  outcomes_suffix ((case (if returnData = [] then ext_call_kwarg EKDefault opts args else NONE) of
       NONE => bind
         (lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ty returnData))
         (\ret_val. return (Value ret_val))
     | SOME default_v => bind get_accounts (\accounts'.
         bind (check (skip_check \/ ext_call_has_code target_addr accounts')
                 "ExtCall target has no code") (\x. return (Value default_v))))) /\
  outcome_prefix_causal ((case (if returnData = [] then ext_call_kwarg EKDefault opts args else NONE) of
       NONE => bind
         (lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ty returnData))
         (\ret_val. return (Value ret_val))
     | SOME default_v => bind get_accounts (\accounts'.
         bind (check (skip_check \/ ext_call_has_code target_addr accounts')
                 "ExtCall target has no code") (\x. return (Value default_v)))))
Proof
  simp_tac bool_ss [LET_THM] >>
  Cases_on `if returnData = [] then ext_call_kwarg EKDefault opts args else NONE` >>
  simp_tac (srw_ss()) []
  >- (match_mp_tac source_prefix_joint_bind >>
      conj_tac >- external_joint_leaf_tac >>
      gen_tac >> BETA_TAC >> external_joint_leaf_tac) >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >>
  gen_tac >> BETA_TAC >> match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >>
  gen_tac >> BETA_TAC >> external_joint_leaf_tac
QED

val external_stage_facts = map (SIMP_RULE bool_ss [LET_THM])
  [source_prefix_extcall_value_joint, source_prefix_extcall_return_joint];
Theorem outcome_prefix_causal_create_oracle[local]:
  outcome_prefix_causal (create_oracle_result salt value code rof)
Proof
  `create_oracle_result salt value code rof =
    bind (take_create_outcome
      (case salt of NONE => CreateCall | SOME s => Create2Call s) value code)
      (\(rq,outcome). bind (adopt_call_outcome rq outcome) (\x.
        if outcome.co_success /\ outcome.co_created <> 0w
        then return (Value (AddressV outcome.co_created))
        else if rof then raise (Error (RevertData outcome.co_returnData))
        else return (Value (AddressV 0w))))` by
    (simp_tac bool_ss [FUN_EQ_THM, vyperCreateTheory.create_oracle_result_def,
       vyperStateTheory.bind_def] >> gen_tac >>
     Cases_on `take_create_outcome
       (case salt of NONE => CreateCall | SOME s => Create2Call s) value code x` >>
     rename1 `take_create_outcome _ _ _ x = (ans,fin)` >>
     Cases_on `ans` >> simp_tac (srw_ss()) [] >>
     rename1 `take_create_outcome _ _ _ x = (INL pair,fin)` >>
     PairCases_on `pair` >>
     simp[adopt_call_outcome_equation, vyperStateTheory.bind_def, COND_RATOR,
       vyperStateTheory.return_def,
       vyperStateTheory.raise_def]) >>
  pop_assum SUBST1_TAC >>
  match_mp_tac outcome_prefix_causal_bind >>
  conj_tac
  >- (simp[outcomes_suffix_def] >> gen_tac >>
      Cases_on `take_create_outcome
        (case salt of NONE => CreateCall | SOME s => Create2Call s) value code st` >>
      drule take_create_outcome_outcome_suffix >> simp[]) >>
  conj_tac >- MATCH_ACCEPT_TAC (cj 2 outcome_prefix_causal_primitive_steps) >>
  CONV_TAC (HO_REWR_CONV FORALL_PROD) >> rpt gen_tac >> simp_tac (srw_ss()) [] >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >> gen_tac >> BETA_TAC >>
  IF_CASES_TAC >> simp_tac bool_ss []
  >- external_joint_leaf_tac >>
  Cases_on `rof` >> simp_tac bool_ss [] >> external_joint_leaf_tac
QED

Theorem source_prefix_rawcall_return_joint[local]:
  outcomes_suffix ((if flags.rcf_revert_on_failure then
    bind (if success then return () else raise (Error (RevertData returnData)))
      (\x. if flags.rcf_max_outsize = 0 then return (Value NoneV)
       else return (Value (BytesV (TAKE flags.rcf_max_outsize returnData))))
    else if flags.rcf_max_outsize = 0 then return (Value (BoolV success))
    else return (Value (ArrayV (TupleV [BoolV success;
      BytesV (TAKE flags.rcf_max_outsize returnData)]))))) /\
  outcome_prefix_causal ((if flags.rcf_revert_on_failure then
    bind (if success then return () else raise (Error (RevertData returnData)))
      (\x. if flags.rcf_max_outsize = 0 then return (Value NoneV)
       else return (Value (BytesV (TAKE flags.rcf_max_outsize returnData))))
    else if flags.rcf_max_outsize = 0 then return (Value (BoolV success))
    else return (Value (ArrayV (TupleV [BoolV success;
      BytesV (TAKE flags.rcf_max_outsize returnData)])))))
Proof
  simp_tac bool_ss [LET_THM] >>
  Cases_on `flags.rcf_revert_on_failure` >> asm_simp_tac bool_ss []
  >- (match_mp_tac source_prefix_joint_bind >>
      conj_tac >- (Cases_on `success` >> simp_tac bool_ss [] >> external_joint_leaf_tac) >>
      gen_tac >> BETA_TAC >> Cases_on `flags.rcf_max_outsize = 0` >>
      asm_simp_tac bool_ss [] >> external_joint_leaf_tac) >>
  Cases_on `flags.rcf_max_outsize = 0` >> asm_simp_tac bool_ss [] >> external_joint_leaf_tac
QED
val rawcall_return_joint = SIMP_RULE bool_ss [LET_THM] source_prefix_rawcall_return_joint;

Theorem outcome_prefix_causal_external_actions:
  (!cx static skip_check sig opts vs.
    outcome_prefix_causal (eval_ext_call cx static skip_check sig opts vs)) /\
  (!cx has_gas vs. outcome_prefix_causal (eval_send cx has_gas vs)) /\
  (!cx flags target calldata amount gas.
    outcome_prefix_causal (eval_raw_call cx flags target calldata amount gas)) /\
  (!cx kind has_salt rof arg_tys vs blueprint_size.
    outcome_prefix_causal (eval_create cx kind has_salt rof arg_tys vs blueprint_size))
Proof
  conj_tac >- suspend "extcall" >>
  conj_tac >- suspend "send" >> conj_tac >- suspend "rawcall" >>
  suspend "create"
QED
Resume outcome_prefix_causal_external_actions[extcall]:
  rpt gen_tac >> PairCases_on `sig` >> Cases_on `vs`
  >- simp[eval_ext_call_def, outcome_prefix_causal_basic] >>
  simp_tac bool_ss [eval_ext_call_def, LET_THM,
    vyperStateTheory.ignore_bind_def] >>
  match_mp_tac outcome_prefix_causal_bind >>
  conj_tac >- FIRST (map MATCH_ACCEPT_TAC external_suffix_leaves) >>
  conj_tac >- FIRST (map MATCH_ACCEPT_TAC external_prefix_leaves) >>
  gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >>
  gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- MATCH_ACCEPT_TAC (hd external_stage_facts) >>
  gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >>
  gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >>
  gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >>
  gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >>
  gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >>
  gen_tac >> BETA_TAC >> MATCH_ACCEPT_TAC (el 2 external_stage_facts)
QED
Resume outcome_prefix_causal_external_actions[send]:
  rpt gen_tac >> Cases_on `vs`
  >- simp[eval_send_def, outcome_prefix_causal_basic] >>
  rename1 `h::t` >> Cases_on `t`
  >- simp[eval_send_def, outcome_prefix_causal_basic] >>
  simp_tac bool_ss [eval_send_def, LET_THM,
    vyperStateTheory.ignore_bind_def] >>
  match_mp_tac outcome_prefix_causal_bind >>
  conj_tac >- EXTERNAL_LEAF_TAC >>
  conj_tac >- EXTERNAL_LEAF_TAC >> gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >> gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >> gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >> gen_tac >> BETA_TAC >>
  conj_tac
  >- (match_mp_tac outcomes_suffix_bind_guarded >>
      conj_tac >- MATCH_ACCEPT_TAC outcomes_suffix_read >>
      rpt gen_tac >> strip_tac >> Cases_on `v''` >>
      simp_tac (srw_ss()) []
      >- suspend "send_native_suffix" >>
      suspend "send_oracle_suffix") >>
  `outcome_prefix_causal
    (bind (take_call_outcome v [] v') (\(rq,outcome).
      bind (check outcome.co_success "send failed") (\x.
        bind (adopt_call_outcome rq outcome) (\x. return (Value NoneV)))))`
    by (match_mp_tac outcome_prefix_causal_bind >>
        conj_tac >- EXTERNAL_LEAF_TAC >>
        conj_tac >- EXTERNAL_LEAF_TAC >>
        CONV_TAC (HO_REWR_CONV FORALL_PROD) >>
        rpt gen_tac >> simp_tac (srw_ss()) [] >>
        match_mp_tac source_prefix_joint_bind >>
        conj_tac >- external_joint_leaf_tac >>
        gen_tac >> BETA_TAC >>
        match_mp_tac source_prefix_joint_bind >>
        conj_tac >- external_joint_leaf_tac >>
        gen_tac >> BETA_TAC >> external_joint_leaf_tac) >>
  pop_assum mp_tac >>
  simp_tac (srw_ss()) [outcome_prefix_causal_def,
    vyperStateTheory.bind_def, vyperStateTheory.return_def]
QED
(* Bounded suffix composition for the native send spine. *)
val EXTERNAL_SUFFIX_BIND_TAC =
  match_mp_tac outcomes_suffix_bind_guarded >>
  conj_tac >- FIRST [EXTERNAL_LEAF_TAC, PREFIX_ATOM_TAC] >>
  rpt gen_tac >> strip_tac >> BETA_TAC;

Resume outcome_prefix_causal_external_actions[send_native_suffix]:
  EXTERNAL_SUFFIX_BIND_TAC >>
  EXTERNAL_SUFFIX_BIND_TAC >>
  EXTERNAL_SUFFIX_BIND_TAC >>
  EXTERNAL_SUFFIX_BIND_TAC >>
  EXTERNAL_SUFFIX_BIND_TAC >>
  EXTERNAL_SUFFIX_BIND_TAC >>
  EXTERNAL_SUFFIX_BIND_TAC >>
  EXTERNAL_SUFFIX_BIND_TAC >>
  EXTERNAL_SUFFIX_BIND_TAC >> EXTERNAL_LEAF_TAC
QED
Resume outcome_prefix_causal_external_actions[send_oracle_suffix]:
  match_mp_tac outcomes_suffix_bind_guarded >>
  conj_tac >- EXTERNAL_LEAF_TAC >>
  rpt gen_tac >> strip_tac >> PairCases_on `v''` >>
  simp_tac (srw_ss()) [] >>
  EXTERNAL_SUFFIX_BIND_TAC >> EXTERNAL_SUFFIX_BIND_TAC >> EXTERNAL_LEAF_TAC
QED
Resume outcome_prefix_causal_external_actions[rawcall]:
  rpt gen_tac >>
  simp_tac bool_ss [eval_raw_call_def, LET_THM,
    vyperStateTheory.ignore_bind_def] >>
  match_mp_tac outcome_prefix_causal_bind >>
  conj_tac >- EXTERNAL_LEAF_TAC >>
  conj_tac >- EXTERNAL_LEAF_TAC >> gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >> gen_tac >> BETA_TAC >>
  conj_tac >- suspend "rawcall_dispatch_suffix" >>
  `outcome_prefix_causal
    (bind
      (bind (if flags.rcf_is_delegate then take_delegate_outcome target calldata v
             else take_call_outcome target calldata v)
        (\(rq,outcome). bind (adopt_call_outcome rq outcome)
          (\x. return (outcome.co_success,outcome.co_returnData))))
      (\(success,returnData).
        if flags.rcf_revert_on_failure then
          bind (if success then return () else raise (Error (RevertData returnData)))
            (\x. if flags.rcf_max_outsize = 0 then return (Value NoneV)
             else return (Value (BytesV (TAKE flags.rcf_max_outsize returnData))))
        else if flags.rcf_max_outsize = 0 then return (Value (BoolV success))
        else return (Value (ArrayV (TupleV [BoolV success;
          BytesV (TAKE flags.rcf_max_outsize returnData)])))))`
    by suspend "rawcall_oracle_prefix" >>
  pop_assum mp_tac >>
  simp_tac (srw_ss()) [outcome_prefix_causal_def,
    vyperStateTheory.bind_def, vyperStateTheory.return_def]
QED
Resume outcome_prefix_causal_external_actions[rawcall_oracle_prefix]:
  match_mp_tac outcome_prefix_causal_bind >>
  conj_tac >- suspend "rawcall_oracle_effect_suffix" >>
  conj_tac
  >- (match_mp_tac outcome_prefix_causal_bind >>
      conj_tac >- (Cases_on `flags.rcf_is_delegate` >> asm_simp_tac bool_ss [] >> EXTERNAL_LEAF_TAC) >>
      conj_tac >- (Cases_on `flags.rcf_is_delegate` >> asm_simp_tac bool_ss [] >> EXTERNAL_LEAF_TAC) >>
      CONV_TAC (HO_REWR_CONV FORALL_PROD) >> rpt gen_tac >> simp_tac (srw_ss()) [] >>
      match_mp_tac source_prefix_joint_bind >>
      conj_tac >- external_joint_leaf_tac >>
      gen_tac >> BETA_TAC >> external_joint_leaf_tac) >>
  CONV_TAC (HO_REWR_CONV FORALL_PROD) >> rpt gen_tac >> simp_tac (srw_ss()) [] >>
  MATCH_ACCEPT_TAC rawcall_return_joint
QED
Resume outcome_prefix_causal_external_actions[rawcall_oracle_effect_suffix]:
  match_mp_tac outcomes_suffix_bind_guarded >>
  conj_tac >- (Cases_on `flags.rcf_is_delegate` >> asm_simp_tac bool_ss [] >> EXTERNAL_LEAF_TAC) >>
  rpt gen_tac >> strip_tac >> PairCases_on `v'` >> simp_tac (srw_ss()) [] >>
  EXTERNAL_SUFFIX_BIND_TAC >> EXTERNAL_LEAF_TAC
QED
Resume outcome_prefix_causal_external_actions[rawcall_dispatch_suffix]:
  match_mp_tac outcomes_suffix_bind_guarded >>
  conj_tac >- MATCH_ACCEPT_TAC outcomes_suffix_read >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  match_mp_tac outcomes_suffix_bind_guarded >>
  conj_tac >- suspend "rawcall_effect_suffix" >>
  rpt gen_tac >> strip_tac >> PairCases_on `v''` >> simp_tac (srw_ss()) [] >>
  MATCH_ACCEPT_TAC (CONJUNCT1 rawcall_return_joint)
QED
Resume outcome_prefix_causal_external_actions[rawcall_effect_suffix]:
  Cases_on `IS_SOME v'` >> asm_simp_tac bool_ss []
  >- (match_mp_tac outcomes_suffix_bind_guarded >>
      conj_tac >- (Cases_on `flags.rcf_is_delegate` >> asm_simp_tac bool_ss [] >> EXTERNAL_LEAF_TAC) >>
      rpt gen_tac >> strip_tac >> PairCases_on `v''` >> simp_tac (srw_ss()) [] >>
      EXTERNAL_SUFFIX_BIND_TAC >> EXTERNAL_LEAF_TAC) >>
  EXTERNAL_SUFFIX_BIND_TAC >> EXTERNAL_SUFFIX_BIND_TAC >>
  EXTERNAL_SUFFIX_BIND_TAC >> EXTERNAL_SUFFIX_BIND_TAC >>
  EXTERNAL_SUFFIX_BIND_TAC >>
  match_mp_tac outcomes_suffix_bind_guarded >>
  conj_tac
  >- (rename1 `outcomes_suffix (if ok then record_storage_backend else return ())` >>
      Cases_on `ok` >> asm_simp_tac bool_ss [] >>
      FIRST [EXTERNAL_LEAF_TAC, PREFIX_ATOM_TAC]) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  EXTERNAL_SUFFIX_BIND_TAC >> EXTERNAL_SUFFIX_BIND_TAC >> EXTERNAL_LEAF_TAC
QED
Resume outcome_prefix_causal_external_actions[create]:
  rpt gen_tac >>
  simp_tac bool_ss [vyperCreateTheory.eval_create_def, LET_THM, vyperStateTheory.ignore_bind_def] >>
  match_mp_tac outcome_prefix_causal_bind >>
  conj_tac >- EXTERNAL_LEAF_TAC >>
  conj_tac >- EXTERNAL_LEAF_TAC >> gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >> gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >> gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >> gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >> gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >> gen_tac >> BETA_TAC >>
  match_mp_tac source_prefix_joint_bind >>
  conj_tac >- external_joint_leaf_tac >> gen_tac >> BETA_TAC >>
  conj_tac >- suspend "create_dispatch_suffix" >>
  `outcome_prefix_causal (create_oracle_result v.co_salt v.co_value v'.cc_initcode rof)`
    by MATCH_ACCEPT_TAC outcome_prefix_causal_create_oracle >>
  pop_assum mp_tac >>
  simp_tac (srw_ss()) [outcome_prefix_causal_def, vyperStateTheory.bind_def]
QED
Resume outcome_prefix_causal_external_actions[create_dispatch_suffix]:
  match_mp_tac outcomes_suffix_bind_guarded >>
  conj_tac >- simp[outcomes_suffix_def] >>
  qx_gen_tac `seed` >> qx_gen_tac `mode` >> qx_gen_tac `fin` >> strip_tac >>
  BETA_TAC >> Cases_on `mode` >> simp_tac bool_ss []
  >- MATCH_ACCEPT_TAC outcomes_suffix_create_oracle >>
  EXTERNAL_SUFFIX_BIND_TAC >>
  IF_CASES_TAC
  >- (Cases_on `rof` >> simp[outcomes_suffix_def, vyperCreateTheory.create_soft_failure_def,
       vyperStateTheory.raise_def, vyperStateTheory.return_def]) >>
  IF_CASES_TAC
  >- (EXTERNAL_SUFFIX_BIND_TAC >>
      Cases_on `rof` >> simp[outcomes_suffix_def, vyperCreateTheory.create_soft_failure_def,
        vyperStateTheory.raise_def, vyperStateTheory.return_def]) >>
  EXTERNAL_SUFFIX_BIND_TAC >> EXTERNAL_SUFFIX_BIND_TAC >>
  EXTERNAL_SUFFIX_BIND_TAC >> EXTERNAL_SUFFIX_BIND_TAC >>
  qmatch_goalsub_abbrev_tac `run_create_evm a b c d e f g h` >>
  Cases_on `run_create_evm a b c d e f g h` >> simp_tac (srw_ss()) []
  >- (EXTERNAL_SUFFIX_BIND_TAC >> Cases_on `rof` >>
      simp[outcomes_suffix_def, vyperCreateTheory.create_soft_failure_def,
        vyperStateTheory.raise_def, vyperStateTheory.return_def]) >>
  PairCases_on `x` >> simp_tac (srw_ss()) [] >>
  EXTERNAL_SUFFIX_BIND_TAC >> EXTERNAL_SUFFIX_BIND_TAC >>
  EXTERNAL_SUFFIX_BIND_TAC >> EXTERNAL_SUFFIX_BIND_TAC >>
  Cases_on `x0` >> simp_tac (srw_ss()) []
  >- (Cases_on `rof` >> simp_tac bool_ss [] >> EXTERNAL_LEAF_TAC) >>
  EXTERNAL_SUFFIX_BIND_TAC >> EXTERNAL_LEAF_TAC
QED
Finalise outcome_prefix_causal_external_actions[local]

Theorem source_prefix_extend_joint[local]:
  !cx res sb. outcomes_suffix (extend_place cx res sb) /\
               outcome_prefix_causal (extend_place cx res sb)
Proof
  rpt gen_tac >> conj_tac
  >- (irule outcomes_suffix_frame >> MATCH_ACCEPT_TAC (cj 3 outcomes_frame_places)) >>
  irule outcome_prefix_causal_frame >>
  MATCH_ACCEPT_TAC outcomes_replace_extend_place
QED

Theorem source_prefix_select_joint[local]:
  !cx ty res sb. outcomes_suffix (select_result cx ty res sb) /\
                 outcome_prefix_causal (select_result cx ty res sb)
Proof
  rpt gen_tac >> conj_tac
  >- (irule outcomes_suffix_frame >> simp[outcomes_frame_reads]) >>
  irule outcome_prefix_causal_frame >>
  MATCH_ACCEPT_TAC outcomes_replace_select_result
QED

Theorem source_prefix_array_length_joint[local]:
  !cx res. outcomes_suffix (result_array_length cx res) /\
           outcome_prefix_causal (result_array_length cx res)
Proof
  rpt gen_tac >> conj_tac
  >- (irule outcomes_suffix_frame >> simp[outcomes_frame_reads]) >>
  irule outcome_prefix_causal_frame >>
  MATCH_ACCEPT_TAC outcomes_replace_result_array_length
QED

Theorem source_prefix_lock_joint:
  (!cx nr view. outcomes_suffix (lock_if_nr cx nr view) /\
                 outcome_prefix_causal (lock_if_nr cx nr view)) /\
  (!cx nr view. outcomes_suffix (unlock_if_nr cx nr view) /\
                 outcome_prefix_causal (unlock_if_nr cx nr view))
Proof
  conj_tac >> rpt gen_tac >> Cases_on `nr` >>
  simp_tac (srw_ss()) [lock_if_nr_def, unlock_if_nr_def,
                       vyperStateTheory.ignore_bind_def] >>
  rpt JOINT_STEP >> suspend "lock_branch"
QED
Resume source_prefix_lock_joint[lock_branch]:
  markerLib.RESUME_TAC >> evalWalkLib.HEAD_CASE_TAC >>
  simp_tac (srw_ss()) [] >> rpt JOINT_STEP >> suspend "lock_leaf"
QED
Resume source_prefix_lock_joint[lock_leaf]:
  markerLib.RESUME_TAC >> rpt PREFIX_STEP
QED
Finalise source_prefix_lock_joint[local]

Theorem source_prefix_push[local]:
  !fn env cx. outcome_prefix_causal (push_function fn env cx)
Proof
  rpt gen_tac >> PREFIX_ATOM_TAC
QED
Theorem source_prefix_pop[local]:
  !sc. outcome_prefix_causal (pop_function sc)
Proof
  rpt gen_tac >> PREFIX_ATOM_TAC
QED
Theorem source_prefix_function_handler[local]:
  !ex. outcome_prefix_causal (handle_function ex)
Proof
  rpt gen_tac >> PREFIX_ATOM_TAC
QED

(* Full source evaluator prefix law, with the reviewed eleven-function API.
 * Constructor proofs below use checked action interfaces and guarded composition. *)
Theorem eval_outcome_prefix_causal_mutual:
  (!cx s. outcome_prefix_causal (eval_stmt cx s)) /\
  (!cx ss. outcome_prefix_causal (eval_stmts cx ss)) /\
  (!cx it. outcome_prefix_causal (eval_iterator cx it)) /\
  (!cx tyv id fbody vs. outcome_prefix_causal (eval_for cx tyv id fbody vs)) /\
  (!cx e. outcome_prefix_causal (eval_expr cx e)) /\
  (!cx es. outcome_prefix_causal (eval_exprs cx es)) /\
  (!cx t. outcome_prefix_causal (eval_base_place cx t)) /\
  (!cx t. outcome_prefix_causal (eval_target_place cx t)) /\
  (!cx g v. outcome_prefix_causal (assign_tuple_targets cx g v)) /\
  (!cx gs vs. outcome_prefix_causal (assign_tuple_target_list cx gs vs)) /\
  (!cx es. outcome_prefix_causal (eval_expr_results cx es))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac
  >- suspend "c01" >- suspend "c02" >- suspend "c03"
  >- suspend "c04" >- suspend "c05" >- suspend "c06"
  >- suspend "c07" >- suspend "c08" >- suspend "c09"
  >- suspend "c10" >- suspend "c11" >- suspend "c12"
  >- suspend "c13" >- suspend "c14" >- suspend "c15"
  >- suspend "c16" >- suspend "c17" >- suspend "c18"
  >- suspend "c19" >- suspend "c20" >- suspend "c21"
  >- suspend "c22" >- suspend "c23" >- suspend "c24"
  >- suspend "c25" >- suspend "c26" >- suspend "c27"
  >- suspend "c28" >- suspend "c29" >- suspend "c30"
  >- suspend "c31" >- suspend "c32" >- suspend "c33"
  >- suspend "c34" >- suspend "c35" >- suspend "c36"
  >- suspend "c37" >- suspend "c38" >- suspend "c39"
  >- suspend "c40" >- suspend "c41" >- suspend "c42"
  >- suspend "c43" >- suspend "c44" >- suspend "c45"
  >- suspend "c46" >- suspend "c47" >- suspend "c48"
  >- suspend "c49" >- suspend "c50" >- suspend "c51"
  >- suspend "c52" >- suspend "c53" >- suspend "c54"
  >- suspend "c55" >- suspend "c56" >- suspend "c57"
  >- suspend "c58" >- suspend "c59" >- suspend "c60"
  >- suspend "c61" >- suspend "c62" >> suspend "c63"
QED

(* Assembly uses checked action interfaces rather than unfolding compound actions. *)
val prefix_assembly_facts = List.concat (map (CONJUNCTS o SPEC_ALL)
  [outcome_prefix_causal_place_actions,
   outcome_prefix_causal_external_actions,
   source_prefix_select_joint, source_prefix_extend_joint,
   source_prefix_array_length_joint, cj 1 source_prefix_lock_joint,
   cj 2 source_prefix_lock_joint, source_prefix_push, source_prefix_pop,
   source_prefix_function_handler]);
val prefix_assembly_net = evalWalkLib.walk_net prefix_rules
  (map (fn th => (concl (SPEC_ALL th), MATCH_ACCEPT_TAC th))
    (prefix_assembly_facts @ prefix_leaf_facts @ prefix_suffix_facts));
fun PREFIX_STEP g = FIRST
  [CONV_TAC (HO_REWR_CONV FORALL_PROD), gen_tac,
   evalWalkLib.IH_TAC {stop = K false, normalise = I},
   (fn goal as (_,w) => FIRST (Net.match w prefix_assembly_net) goal),
   conj_tac,
   CONV_TAC (RAND_CONV (CHANGED_CONV evalWalkLib.head_conv)),
   CONV_TAC (RAND_CONV (REWR_CONV vyperStateTheory.ignore_bind_def)),
   CONV_TAC (RAND_CONV (REWR_CONV switch_BoolV_def)),
   CHANGED_TAC PREFIX_ATOM_TAC,
   strip_tac, conj_tac, evalWalkLib.HEAD_CASE_TAC] g;

val PREFIX_CONSTRUCTOR_TAC = rpt strip_tac >>
  simp_tac bool_ss [Once evaluate_def] >> rpt PREFIX_STEP;

Resume eval_outcome_prefix_causal_mutual[c01]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c02]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c03]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c04]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c05]:
  rpt strip_tac >> simp_tac bool_ss [Once evaluate_def] >>
  rpt PREFIX_STEP
QED
Resume eval_outcome_prefix_causal_mutual[c06]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c07]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c08]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c09]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c10]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c11]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c12]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c13]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c14]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c15]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c16]:
  rpt strip_tac >> simp_tac bool_ss [Once evaluate_def] >>
  rpt PREFIX_STEP
QED
Resume eval_outcome_prefix_causal_mutual[c17]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c18]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c19]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c20]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c21]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c22]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c23]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c24]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c25]:
  rpt strip_tac >> simp_tac bool_ss [Once evaluate_def] >>
  match_mp_tac outcome_prefix_causal_bind_guarded >>
  conj_tac >- MATCH_ACCEPT_TAC (cj 5 eval_outcomes_suffix_with_results) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  rpt (FIRST [MATCH_ACCEPT_TAC
    (MATCH_MP outcome_prefix_causal_frame outcomes_replace_array_iterator_results),
    PREFIX_STEP])
QED
Resume eval_outcome_prefix_causal_mutual[c26]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c27]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c28]:
  PREFIX_CONSTRUCTOR_TAC >> metis_tac[]
QED
Resume eval_outcome_prefix_causal_mutual[c29]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c30]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c31]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c32]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c33]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c34]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c35]:
  rpt strip_tac >> simp_tac bool_ss [Once evaluate_def] >>
  match_mp_tac outcome_prefix_causal_bind_guarded >>
  conj_tac >- MATCH_ACCEPT_TAC (cj 5 eval_outcomes_suffix_with_results) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  conj_tac >- suspend "subscript_suffix" >>
  match_mp_tac outcome_prefix_causal_bind_guarded >>
  conj_tac >- (IF_CASES_TAC >> rpt PREFIX_STEP) >>
  conj_tac >- (IF_CASES_TAC >> rpt PREFIX_STEP) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  rpt PREFIX_STEP
QED
Resume eval_outcome_prefix_causal_mutual[subscript_suffix]:
  match_mp_tac outcomes_suffix_bind_guarded >>
  conj_tac >- (IF_CASES_TAC >> rpt PREFIX_STEP) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >> rpt PREFIX_STEP
QED
Resume eval_outcome_prefix_causal_mutual[c36]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c37]:
  rpt strip_tac >> simp_tac bool_ss [Once evaluate_def,
    vyperStateTheory.ignore_bind_def] >>
  match_mp_tac outcome_prefix_causal_bind_guarded >>
  conj_tac >- (FIRST (map MATCH_ACCEPT_TAC prefix_suffix_facts)) >>
  conj_tac >- (FIRST (map MATCH_ACCEPT_TAC prefix_leaf_facts)) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  conj_tac >- suspend "builtin_suffix" >>
  match_mp_tac outcome_prefix_causal_bind_guarded >>
  conj_tac >- suspend "builtin_value_suffix" >>
  conj_tac >- suspend "builtin_value_prefix" >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  simp[outcome_prefix_causal_basic, outcomes_suffix_def, vyperStateTheory.return_def]
QED
Resume eval_outcome_prefix_causal_mutual[builtin_value_prefix]:
  IF_CASES_TAC >- suspend "builtin_len" >>
  IF_CASES_TAC >- suspend "builtin_in" >>
  IF_CASES_TAC >- suspend "builtin_gas" >>
  suspend "builtin_other"
QED
Resume eval_outcome_prefix_causal_mutual[builtin_len]:
  simp_tac bool_ss [] >> rpt PREFIX_STEP
QED
Resume eval_outcome_prefix_causal_mutual[builtin_in]:
  simp_tac bool_ss [] >> rpt PREFIX_STEP
QED
Resume eval_outcome_prefix_causal_mutual[builtin_gas]:
  simp_tac bool_ss [] >> rpt PREFIX_STEP
QED
Resume eval_outcome_prefix_causal_mutual[builtin_other]:
  simp_tac bool_ss [] >> rpt PREFIX_STEP
QED
Resume eval_outcome_prefix_causal_mutual[builtin_value_suffix]:
  IF_CASES_TAC >- (simp_tac bool_ss [] >> rpt PREFIX_STEP) >>
  IF_CASES_TAC >- (simp_tac bool_ss [] >> rpt PREFIX_STEP) >>
  IF_CASES_TAC >- (simp_tac bool_ss [] >> rpt PREFIX_STEP) >>
  simp_tac bool_ss [] >> rpt PREFIX_STEP
QED
Resume eval_outcome_prefix_causal_mutual[builtin_suffix]:
  match_mp_tac outcomes_suffix_bind_guarded >>
  conj_tac >- suspend "builtin_value_suffix" >>
  rpt gen_tac >> strip_tac >> BETA_TAC >> rpt PREFIX_STEP
QED
Resume eval_outcome_prefix_causal_mutual[c38]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c39]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c40]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c41]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c42]:
  rpt strip_tac >> simp_tac bool_ss [Once evaluate_def] >>
  simp_tac bool_ss [vyperStateTheory.ignore_bind_def] >>
  match_mp_tac outcome_prefix_causal_bind_guarded >>
  conj_tac >- (FIRST (map MATCH_ACCEPT_TAC prefix_suffix_facts)) >>
  conj_tac >- (FIRST (map MATCH_ACCEPT_TAC prefix_leaf_facts)) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  conj_tac >- suspend "intcall_suffix1" >>
  match_mp_tac outcome_prefix_causal_bind_guarded >>
  conj_tac >- (FIRST (map MATCH_ACCEPT_TAC prefix_suffix_facts)) >>
  conj_tac >- (FIRST (map MATCH_ACCEPT_TAC prefix_leaf_facts)) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  conj_tac >- suspend "intcall_suffix2" >>
  match_mp_tac outcome_prefix_causal_bind_guarded >>
  conj_tac >- FIRST (map MATCH_ACCEPT_TAC prefix_suffix_facts) >>
  conj_tac >- FIRST (map MATCH_ACCEPT_TAC prefix_leaf_facts) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  simp_tac bool_ss [LET_THM] >> suspend "intcall_body"
QED
Resume eval_outcome_prefix_causal_mutual[c43]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c44]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c45]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c46]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c47]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c48]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c49]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c50]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c51]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c52]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c53]:
  rpt strip_tac >> simp_tac bool_ss [Once evaluate_def] >>
  rpt PREFIX_STEP
QED
Resume eval_outcome_prefix_causal_mutual[c54]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c55]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c56]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c57]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c58]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c59]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c60]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c61]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c62]:
  PREFIX_CONSTRUCTOR_TAC
QED
Resume eval_outcome_prefix_causal_mutual[c63]:
  PREFIX_CONSTRUCTOR_TAC
QED

Resume eval_outcome_prefix_causal_mutual[intcall_suffix1]:
  rpt PREFIX_STEP
QED
Resume eval_outcome_prefix_causal_mutual[intcall_suffix2]:
  rpt PREFIX_STEP
QED
fun INTERNAL_JOINT_STEP g = FIRST
  [match_mp_tac source_prefix_joint_bind_guarded,
   (fn goal as (_,w) => FIRST (Net.match w prefix_assembly_net) goal),
   evalWalkLib.IH_TAC {stop = K false,
     normalise = PURE_REWRITE_RULE [vyperStateTheory.ignore_bind_def]},
   CONV_TAC (HO_REWR_CONV FORALL_PROD), gen_tac,
   CHANGED_TAC (BETA_TAC >> simp_tac bool_ss []),
   CONV_TAC (BINOP_CONV (RAND_CONV (CHANGED_CONV evalWalkLib.head_conv))),
   CONV_TAC (RAND_CONV (CHANGED_CONV evalWalkLib.head_conv)),
   strip_tac, conj_tac, evalWalkLib.HEAD_CASE_TAC] g;

Resume eval_outcome_prefix_causal_mutual[intcall_body]:
  rpt INTERNAL_JOINT_STEP
QED
Finalise eval_outcome_prefix_causal_mutual

Theorem eval_stmts_outcome_prefix_causal:
  !cx fbody. outcome_prefix_causal (eval_stmts cx fbody)
Proof
  simp[eval_outcome_prefix_causal_mutual]
QED

Theorem eval_external_defaults_outcome_prefix_causal:
  !cx dflts. outcome_prefix_causal (eval_external_defaults cx dflts)
Proof
  rpt gen_tac >> simp_tac bool_ss [eval_external_defaults_def] >>
  rpt PREFIX_STEP >> simp[eval_outcome_prefix_causal_mutual]
QED

Theorem fn_entry_run_outcome_prefix:
  !os next tail tail' gobs am cx nr mut mods args dflts vals fbody res st.
    fn_entry_run (os ++ next::tail) gobs am cx nr mut mods args dflts vals fbody =
      SOME (res,st) /\ st.outcomes = SOME (next::tail) ==>
    fn_entry_run (os ++ tail') gobs am cx nr mut mods args dflts vals fbody =
      SOME (res,st with outcomes := SOME tail')
Proof
  rpt gen_tac >> simp_tac bool_ss [fn_entry_run_def, LET_THM] >>
  IF_CASES_TAC >> simp_tac (srw_ss()) [] >>
  Cases_on `if cx.in_deploy then
    evaluate_all_constants cx am cx.txn.target mods else SOME am` >>
  simp_tac (srw_ss()) [] >>
  qmatch_goalsub_abbrev_tac `entry_core (initial_state x [FEMPTY] with
    <|outcomes := SOME (os ++ next::tail); requests := []; gas_obs := gobs|>)` >>
  `outcome_prefix_causal entry_core` by
    (qunabbrev_tac `entry_core` >>
     simp_tac bool_ss [send_call_value_def, eval_external_defaults_def, LET_THM] >>
     rpt PREFIX_STEP >>
     simp[eval_outcome_prefix_causal_mutual,
          eval_outcomes_suffix_with_results]) >>
  strip_tac >>
  qpat_x_assum `outcome_prefix_causal entry_core`
    (mp_tac o Q.SPECL
      [`initial_state x [FEMPTY] with <|requests := []; gas_obs := gobs|>`,
       `os`, `next`, `tail`, `res`, `st`] o
      REWRITE_RULE [outcome_prefix_causal_def]) >>
  simp[] >> disch_then (qspec_then `tail'` ACCEPT_TAC)
QED

Theorem outcome_prefix_causal_truncate[local]:
  !f seed os n res fin.
    outcomes_suffix f /\ outcome_prefix_causal f /\
    n <= LENGTH os /\
    f (seed with outcomes := SOME os) = (res,fin) /\
    (SND (f (seed with outcomes := SOME (TAKE n os)))).outcomes <> SOME [] ==>
    ?rest. rest <> [] /\
      f (seed with outcomes := SOME (TAKE n os)) =
        (res,fin with outcomes := SOME rest) /\
      fin.outcomes = SOME (rest ++ DROP n os)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `f (seed with outcomes := SOME (TAKE n os))` >>
  rename1 `f (seed with outcomes := SOME (TAKE n os)) = (short_res,short_fin)` >>
  qpat_x_assum `outcomes_suffix f`
    (mp_tac o REWRITE_RULE [outcomes_suffix_def]) >>
  disch_then (qspec_then `seed with outcomes := SOME (TAKE n os)` mp_tac) >>
  simp[outcome_suffix_def] >>
  disch_then (qx_choose_then `used` (qx_choose_then `rest` strip_assume_tac)) >>
  Cases_on `rest` >- gvs[] >>
  rename1 `short_fin.outcomes = SOME (next::tail)` >>
  `used ++ ((next::tail) ++ DROP n os) = os` by
    metis_tac[TAKE_DROP, APPEND_ASSOC] >>
  `f (seed with outcomes := SOME (used ++ next::tail)) = (short_res,short_fin)` by
    metis_tac[] >>
  qpat_x_assum `outcome_prefix_causal f`
    (mp_tac o Q.SPECL [`seed`,`used`,`next`,`tail`,`short_res`,`short_fin`] o
      REWRITE_RULE [outcome_prefix_causal_def]) >>
  simp[] >> disch_then (qspec_then `(next::tail) ++ DROP n os` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  simp[vyperStateTheory.evaluation_state_component_equality]
QED

Theorem fn_entry_run_truncate[local]:
  !n os gobs am cx nr mut mods args dflts vals fbody res fin.
    n <= LENGTH os /\
    entry_calls_within n os
      (\xs. fn_entry_run xs gobs am cx nr mut mods args dflts vals fbody) /\
    fn_entry_run os gobs am cx nr mut mods args dflts vals fbody =
      SOME (res,fin) ==>
    ?rest. rest <> [] /\
      fn_entry_run (TAKE n os) gobs am cx nr mut mods args dflts vals fbody =
        SOME (res,fin with outcomes := SOME rest) /\
      fin.outcomes = SOME (rest ++ DROP n os)
Proof
  rpt gen_tac >> strip_tac >>
  `n - LENGTH (TAKE n os) = 0` by
    (simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> rw[] >> decide_tac) >>
  fs[entry_calls_within_def, entry_calls_within_from_def] >>
  Cases_on `LENGTH vals > LENGTH args \/ LENGTH args - LENGTH vals > LENGTH dflts`
  >- gvs[fn_entry_run_def] >>
  Cases_on `if cx.in_deploy then
    evaluate_all_constants cx am cx.txn.target mods else SOME am`
  >- gvs[fn_entry_run_def] >>
  gvs[fn_entry_run_def, LET_THM] >>
  qmatch_assum_abbrev_tac `entry_core entry_seed = (res,fin)` >>
  `outcomes_suffix entry_core /\ outcome_prefix_causal entry_core` by
    (conj_tac >> qunabbrev_tac `entry_core` >>
     simp_tac bool_ss [send_call_value_def, eval_external_defaults_def, LET_THM] >>
     rpt PREFIX_STEP >>
     simp[eval_outcome_prefix_causal_mutual, eval_outcomes_suffix_with_results]) >>
  fs[entry_calls_within_from_def] >>
  mp_tac (Q.SPECL [`entry_core`,`entry_seed`,`os`,`n`,`res`,`fin`]
    (INST_TYPE [alpha |-> ``:unit + exception``]
      outcome_prefix_causal_truncate)) >>
  simp[Abbr `entry_seed`] >>
  Cases_on `entry_core (initial_state x [FEMPTY] with
    <|outcomes := SOME (TAKE n os); requests := []; gas_obs := gobs|>)` >>
  gvs[]
QED

Theorem source_calls_within_truncate:
  !n am tx os gobs res st.
    n <= LENGTH os /\ source_calls_within n am tx os gobs /\
    call_entry_run os gobs am tx = SOME (res,st) ==>
    ?rest. rest <> [] /\
      call_entry_run (TAKE n os) gobs am tx =
        SOME (res,st with outcomes := SOME rest) /\
      st.outcomes = SOME (rest ++ DROP n os)
Proof
  rpt gen_tac >>
  simp_tac bool_ss [source_calls_within_def, call_entry_run_def, LET_THM] >>
  rpt TOP_CASE_TAC >> simp[] >> metis_tac[fn_entry_run_truncate]
QED

Theorem deploy_source_calls_within_truncate:
  !n tops am tx os gobs res st.
    n <= LENGTH os /\ deploy_source_calls_within n tops am tx os gobs /\
    deploy_entry_run os gobs tops am tx = SOME (res,st) ==>
    ?rest. rest <> [] /\
      deploy_entry_run (TAKE n os) gobs tops am tx =
        SOME (res,st with outcomes := SOME rest) /\
      st.outcomes = SOME (rest ++ DROP n os)
Proof
  rpt gen_tac >>
  simp_tac bool_ss
    [deploy_source_calls_within_def, deploy_entry_run_def, LET_THM] >>
  rpt TOP_CASE_TAC >> simp[] >> metis_tac[fn_entry_run_truncate]
QED

(* Bind closure of the consumption cut.  All semantic suppliers are premises. *)
Theorem source_replay_cut_bind[local]:
  !f g.
    (!s os r t.
      f (s with outcomes := SOME (os ++ [probe_failed_outcome])) = (r,t) ==>
      ((?pre. t.outcomes = SOME (pre ++ [probe_failed_outcome]) /\
         !tail. f (s with outcomes := SOME (os ++ tail)) =
           (r,t with outcomes := SOME (pre ++ tail))) \/
       (t.outcomes = SOME [] /\
        (\(r,s). (r,erase_storage_trace s)) (r,t) =
          (\(r,s). (r,erase_storage_trace s))
            (f (s with outcomes := SOME (os ++ [empty_failed_outcome]))) /\
        (\(r,s). (r,erase_storage_trace s)) (r,t) =
          (\(r,s). (r,erase_storage_trace s))
            (f (s with outcomes := SOME os))) \/
       (t.outcomes = SOME [] /\
        r = INR (Error (RuntimeError "create outcome accounts")) /\
        ~NULL t.requests /\
        FST (f (s with outcomes := SOME (os ++ [empty_failed_outcome]))) <>
          INR (Error (RuntimeError "create outcome accounts")) /\
        f (s with outcomes := SOME os) =
        f (s with outcomes := SOME (os ++ [failed_outcome (LAST t.requests)])) /\
        (!re u. f (s with outcomes := SOME (os ++ [empty_failed_outcome])) = (re,u) ==>
          u.outcomes = SOME [] /\ accounts_runtime_well_typed u.accounts)))) /\
    (!v s os r t.
      g v (s with outcomes := SOME (os ++ [probe_failed_outcome])) = (r,t) ==>
      ((?pre. t.outcomes = SOME (pre ++ [probe_failed_outcome]) /\
         !tail. g v (s with outcomes := SOME (os ++ tail)) =
           (r,t with outcomes := SOME (pre ++ tail))) \/
       (t.outcomes = SOME [] /\
        (\(r,s). (r,erase_storage_trace s)) (r,t) =
          (\(r,s). (r,erase_storage_trace s))
            (g v (s with outcomes := SOME (os ++ [empty_failed_outcome]))) /\
        (\(r,s). (r,erase_storage_trace s)) (r,t) =
          (\(r,s). (r,erase_storage_trace s))
            (g v (s with outcomes := SOME os))) \/
       (t.outcomes = SOME [] /\
        r = INR (Error (RuntimeError "create outcome accounts")) /\
        ~NULL t.requests /\
        FST (g v (s with outcomes := SOME (os ++ [empty_failed_outcome]))) <>
          INR (Error (RuntimeError "create outcome accounts")) /\
        g v (s with outcomes := SOME os) =
        g v (s with outcomes := SOME (os ++ [failed_outcome (LAST t.requests)])) /\
        (!re u. g v (s with outcomes := SOME (os ++ [empty_failed_outcome])) = (re,u) ==>
          u.outcomes = SOME [] /\ accounts_runtime_well_typed u.accounts)))) /\
    (!v. outcomes_suffix (g v)) /\
    (!a b s t.
      (\(r,s). (r,erase_storage_trace s)) (a s) =
      (\(r,s). (r,erase_storage_trace s)) (b t) ==>
      (\(r,s). (r,erase_storage_trace s)) (bind a g s) =
      (\(r,s). (r,erase_storage_trace s)) (bind b g t)) /\
    (!v s r t.
      s.outcomes = SOME [] /\ accounts_runtime_well_typed s.accounts /\
      g v s = (r,t) ==>
      r <> INR (Error (RuntimeError "create outcome accounts")) /\
      t.outcomes = SOME [] /\ accounts_runtime_well_typed t.accounts) ==>
    !s os r t.
      bind f g (s with outcomes := SOME (os ++ [probe_failed_outcome])) = (r,t) ==>
      ((?pre. t.outcomes = SOME (pre ++ [probe_failed_outcome]) /\
         !tail. bind f g (s with outcomes := SOME (os ++ tail)) =
           (r,t with outcomes := SOME (pre ++ tail))) \/
       (t.outcomes = SOME [] /\
        (\(r,s). (r,erase_storage_trace s)) (r,t) =
          (\(r,s). (r,erase_storage_trace s))
            (bind f g (s with outcomes := SOME (os ++ [empty_failed_outcome]))) /\
        (\(r,s). (r,erase_storage_trace s)) (r,t) =
          (\(r,s). (r,erase_storage_trace s))
            (bind f g (s with outcomes := SOME os))) \/
       (t.outcomes = SOME [] /\
        r = INR (Error (RuntimeError "create outcome accounts")) /\
        ~NULL t.requests /\
        FST (bind f g (s with outcomes := SOME (os ++ [empty_failed_outcome]))) <>
          INR (Error (RuntimeError "create outcome accounts")) /\
        bind f g (s with outcomes := SOME os) =
        bind f g (s with outcomes := SOME (os ++ [failed_outcome (LAST t.requests)])) /\
        (!re u. bind f g (s with outcomes := SOME (os ++ [empty_failed_outcome])) = (re,u) ==>
          u.outcomes = SOME [] /\ accounts_runtime_well_typed u.accounts)))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `f (s with outcomes := SOME (os ++ [probe_failed_outcome]))` >>
  rename1 `f (s with outcomes := SOME (os ++ [probe_failed_outcome])) = (rf,sf)` >>
  qpat_x_assum `!s os r t. f _ = _ ==> _` drule >>
  strip_tac
  >- suspend "unconsumed"
  >- suspend "ordinary"
  >> suspend "create"
QED
Resume source_replay_cut_bind[unconsumed]:
  reverse (Cases_on `rf`)
  >- (gvs[vyperStateTheory.bind_def] >> disj1_tac >>
      qexists_tac `pre` >> simp[vyperStateTheory.bind_def]) >>
  gvs[vyperStateTheory.bind_def] >>
  rename1 `g v sf = (r,t)` >>
  `g v (sf with outcomes := SOME (pre ++ [probe_failed_outcome])) = (r,t)` by
    simp[] >>
  qpat_x_assum `!v s os r t. g v _ = _ ==> _` drule >>
  qpat_assum `!tail. f _ = _`
    (qspec_then `[]` (fn th => rewrite_tac[REWRITE_RULE [APPEND_NIL] th])) >>
  simp[] >> strip_tac >> gvs[]
QED
Resume source_replay_cut_bind[ordinary]:
  disj2_tac >> disj1_tac >> conj_tac
  >- (Cases_on `rf` >> gvs[vyperStateTheory.bind_def] >>
      rename1 `g v sf = (r,t)` >>
      qpat_x_assum `!v. outcomes_suffix (g v)` (qspec_then `v` mp_tac) >>
      simp[outcomes_suffix_def] >>
      disch_then (qspec_then `sf` mp_tac) >> simp[outcome_suffix_def]) >>
  qpat_assum `bind f g _ = (r,t)` (fn th => rewrite_tac[GSYM th]) >>
  conj_tac >> first_x_assum irule >> gvs[]
QED
Resume source_replay_cut_bind[create]:
  `r = INR (Error (RuntimeError "create outcome accounts")) /\ t = sf` by
    gvs[vyperStateTheory.bind_def] >>
  disj2_tac >> disj2_tac >> gvs[] >>
  conj_tac
  >- (Cases_on `f (s with outcomes := SOME (os ++ [empty_failed_outcome]))` >>
      rename1 `f (s with outcomes := SOME (os ++ [empty_failed_outcome])) = (re,se)` >>
      Cases_on `re` >> gvs[vyperStateTheory.bind_def] >>
      first_x_assum drule >> strip_tac >>
      Cases_on `g x se` >>
      first_x_assum drule >> simp[] >> strip_tac >>
      first_x_assum drule >> simp[]) >>
  conj_tac >- simp[vyperStateTheory.bind_def] >>
  rpt gen_tac >>
  Cases_on `f (s with outcomes := SOME (os ++ [empty_failed_outcome]))` >>
  rename1 `f (s with outcomes := SOME (os ++ [empty_failed_outcome])) = (rx,sx)` >>
  Cases_on `rx` >> gvs[vyperStateTheory.bind_def] >>
  metis_tac[]
QED
Finalise source_replay_cut_bind[local]

(* Consumption-cut probes: no premise on the original accounts or requests. *)
Theorem source_replay_unconsumed_cut[local]:
  !f st os r t.
    outcomes_suffix f /\ outcome_prefix_causal f /\
    f (st with outcomes := SOME (os ++ [probe_failed_outcome])) = (r,t) /\
    t.outcomes <> SOME [] ==>
    ?pre. t.outcomes = SOME (pre ++ [probe_failed_outcome]) /\
      !tail. f (st with outcomes := SOME (os ++ tail)) =
        (r,t with outcomes := SOME (pre ++ tail))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all outcomes_suffix_result >> simp[outcome_suffix_def] >>
  disch_then (qx_choose_then `used` (qx_choose_then `rest` strip_assume_tac)) >>
  qspec_then `rest` strip_assume_tac SNOC_CASES >> gvs[] >>
  gvs[GSYM SNOC_APPEND] >>
  Cases_on `l` >> gvs[outcome_prefix_causal_def, SNOC_APPEND] >>
  gvs[rich_listTheory.APPEND_ASSOC_CONS]
QED


Theorem source_replay_trace_transport[local]:
  !f s t.
    storage_trace_frame f /\ erase_storage_trace s = erase_storage_trace t ==>
    (\(r,s). (r,erase_storage_trace s)) (f s) =
    (\(r,s). (r,erase_storage_trace s)) (f t)
Proof
  rpt gen_tac >> strip_tac >>
  drule storage_trace_frame_erasure >>
  disch_then (qspec_then `s` assume_tac) >>
  drule storage_trace_frame_erasure >>
  disch_then (qspec_then `t` assume_tac) >>
  Cases_on `f s` >> Cases_on `f t` >> gvs[] >> metis_tac[]
QED

Theorem source_replay_bind_transport[local]:
  !f h g s t.
    (!v. storage_trace_frame (g v)) /\
    (\(r,s). (r,erase_storage_trace s)) (f s) =
    (\(r,s). (r,erase_storage_trace s)) (h t) ==>
    (\(r,s). (r,erase_storage_trace s)) (bind f g s) =
    (\(r,s). (r,erase_storage_trace s)) (bind h g t)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `f s` >> Cases_on `h t` >> gvs[] >>
  rename1 `erase_storage_trace a = erase_storage_trace b` >>
  Cases_on `q` >> gvs[vyperStateTheory.bind_def] >>
  irule source_replay_trace_transport >> simp[]
QED


Theorem source_ordinary_probe_cut[local]:
  !rq k st oc.
    storage_trace_frame (k (rq,failed_outcome rq)) /\
    k (rq,probe_failed_outcome) = k (rq,failed_outcome rq) /\
    k (rq,empty_failed_outcome) = k (rq,failed_outcome rq) /\
    (oc = probe_failed_outcome \/ oc = empty_failed_outcome) ==>
    (\(r,s). (r,erase_storage_trace s))
      (bind (take_request_outcome rq) k (st with outcomes := SOME [oc])) =
    (\(r,s). (r,erase_storage_trace s))
      (bind (take_request_outcome rq) k (st with outcomes := SOME []))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[vyperStateTheory.bind_def, take_request_outcome_def,
    take_outcome_def, probe_failed_outcome_def, empty_failed_outcome_def,
    failed_outcome_def] >>
  Cases_on `computed_precompile rq` >>
  Cases_on `precompile_result rq.cr_target rq.cr_data` >>
  Cases_on `THE (precompile_result rq.cr_target rq.cr_data)` >> gvs[] >>
  irule source_replay_trace_transport >>
  simp[vyperStateTheory.erase_storage_trace_def]
QED

Theorem source_replay_internal_cleanup[local]:
  !f cx nr view prev st r t.
    f st = (r,t) ==>
    (FST (finally_unless_halt
      (finally (try f handle_function) (pop_function prev))
      (unlock_if_nr cx nr view) st) =
      INR (Error (RuntimeError "create outcome accounts")) <=>
      r = INR (Error (RuntimeError "create outcome accounts"))) /\
    (SND (finally_unless_halt
      (finally (try f handle_function) (pop_function prev))
      (unlock_if_nr cx nr view) st)).requests = t.requests
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `nr` >> Cases_on `view` >> Cases_on `cx.nonreentrant_slot` >>
  Cases_on `r` >>
  gvs[vyperStateTheory.try_def, vyperStateTheory.finally_def,
    vyperStateTheory.finally_unless_halt_def,
    vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
    pop_function_def, vyperStateTheory.set_scopes_def,
    vyperStateTheory.return_def, unlock_if_nr_def,
    release_nonreentrant_lock_def, vyperStateTheory.update_transient_def,
    vyperStateTheory.get_transient_storage_def, vyperStateTheory.raise_def,
    vyperStateTheory.record_storage_event_def] >>
  rename1 `f st = (INR ex,t)` >> Cases_on `ex` >>
  simp[handle_function_def, vyperStateTheory.raise_def,
    vyperStateTheory.return_def, vyperStateTheory.bind_def,
    vyperStateTheory.finally_def, vyperStateTheory.finally_unless_halt_def,
    vyperStateTheory.ignore_bind_def, pop_function_def,
    vyperStateTheory.set_scopes_def]
QED

(* Parser-only cut notation; expands without introducing a logical constant. *)
val _ = overload_on ("source_wrapper_cut_at", ``\f s os.
  !r t.
    f (s with outcomes := SOME (os ++ [probe_failed_outcome])) = (r,t) ==>
    ((?pre. t.outcomes = SOME (pre ++ [probe_failed_outcome]) /\
       !tail. f (s with outcomes := SOME (os ++ tail)) =
         (r,t with outcomes := SOME (pre ++ tail))) \/
     (t.outcomes = SOME [] /\
      (\(r,s). (r,erase_storage_trace s)) (r,t) =
        (\(r,s). (r,erase_storage_trace s))
          (f (s with outcomes := SOME (os ++ [empty_failed_outcome]))) /\
      (\(r,s). (r,erase_storage_trace s)) (r,t) =
        (\(r,s). (r,erase_storage_trace s)) (f (s with outcomes := SOME os))) \/
     (t.outcomes = SOME [] /\
      r = INR (Error (RuntimeError "create outcome accounts")) /\
      ~NULL t.requests /\
      FST (f (s with outcomes := SOME (os ++ [empty_failed_outcome]))) <>
        INR (Error (RuntimeError "create outcome accounts")) /\
      f (s with outcomes := SOME os) =
        f (s with outcomes := SOME (os ++ [failed_outcome (LAST t.requests)])) /\
      (!q u. f (s with outcomes := SOME (os ++ [empty_failed_outcome])) = (q,u) ==>
         u.outcomes = SOME [] /\ accounts_runtime_well_typed u.accounts)))``);

Theorem source_replay_cut_postprocess:
  !K f s os.
    ((!r t xs. K (r,t with outcomes := xs) =
       (FST (K (r,t)), (SND (K (r,t))) with outcomes := xs)) /\
     (!x y. (\(r,s). (r,erase_storage_trace s)) x =
            (\(r,s). (r,erase_storage_trace s)) y ==>
       (\(r,s). (r,erase_storage_trace s)) (K x) =
       (\(r,s). (r,erase_storage_trace s)) (K y)) /\
     (!r t. (SND (K (r,t))).outcomes = t.outcomes) /\
     (!r t. accounts_runtime_well_typed t.accounts ==>
       accounts_runtime_well_typed (SND (K (r,t))).accounts) /\
     (FST (K (f (s with outcomes := SOME (os ++ [probe_failed_outcome])))) =
        INR (Error (RuntimeError "create outcome accounts")) <=>
      FST (f (s with outcomes := SOME (os ++ [probe_failed_outcome]))) =
        INR (Error (RuntimeError "create outcome accounts"))) /\
     (FST (K (f (s with outcomes := SOME (os ++ [empty_failed_outcome])))) =
        INR (Error (RuntimeError "create outcome accounts")) <=>
      FST (f (s with outcomes := SOME (os ++ [empty_failed_outcome]))) =
        INR (Error (RuntimeError "create outcome accounts"))) /\
     (!r t. (SND (K (r,t))).requests = t.requests)) ==>
    source_wrapper_cut_at f s os ==>
    source_wrapper_cut_at (\s. K (f s)) s os
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `f (s with outcomes := SOME (os ++ [probe_failed_outcome]))` >>
  rename1 `f (s with outcomes := SOME (os ++ [probe_failed_outcome])) = (rf,sf)` >>
  qpat_x_assum `!r t. (rf,sf) = (r,t) ==> _`
    (qspecl_then [`rf`,`sf`] mp_tac) >> simp_tac bool_ss [] >> strip_tac
  >- (disj1_tac >> qexists_tac `pre` >> gvs[] >>
      qpat_x_assum `!r t. (SND (_ (r,t))).outcomes = _`
        (qspecl_then [`rf`,`sf`] mp_tac) >> simp[])
  >- (disj2_tac >> disj1_tac >> gvs[] >> conj_tac
      >- (qpat_x_assum `!r t. (SND (_ (r,t))).outcomes = _`
            (qspecl_then [`rf`,`sf`] mp_tac) >> simp[]) >>
      rename1 `post (rf,sf) = (r,t)` >>
      qpat_x_assum `!x y. _ = _ ==> _ = _`
        (qspec_then `(rf,sf)` mp_tac) >> simp[] >>
      disch_then (fn th => conj_tac >> irule th >> simp[])) >>
  disj2_tac >> disj2_tac >> gvs[] >>
  Cases_on `f (s with outcomes := SOME (os ++ [empty_failed_outcome]))` >>
  gvs[] >>
  qpat_assum `!r t. (SND (_ (r,t))).outcomes = _`
    (qspecl_then [`INR (Error (RuntimeError "create outcome accounts"))`,`sf`] assume_tac) >>
  qpat_assum `!r t. (SND (_ (r,t))).requests = _`
    (qspecl_then [`INR (Error (RuntimeError "create outcome accounts"))`,`sf`] assume_tac) >>
  qpat_assum `_ (_,sf) = (_,t)` (fn th => fs[th]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!r t. (SND (_ (r,t))).outcomes = _`
    (qspecl_then [`q`,`r`] assume_tac) >>
  qpat_assum `!r t. accounts_runtime_well_typed _ ==> _`
    (qspecl_then [`q`,`r`] assume_tac) >>
  qpat_assum `_ (q,r) = (_,_)` (fn th => fs[th])
QED

Theorem source_replay_cut_wrappers[local]:
  (!f s os.
    ~NULL (SND (f (s with outcomes := SOME (os ++ [probe_failed_outcome])))).scopes /\
    ~NULL (SND (f (s with outcomes := SOME (os ++ [empty_failed_outcome])))).scopes /\
    source_wrapper_cut_at f s os ==>
    source_wrapper_cut_at (finally f pop_scope) s os) /\
  (!f prev s os. source_wrapper_cut_at f s os ==>
    source_wrapper_cut_at (finally f (set_scopes prev)) s os) /\
  (!f s os.
    ~NULL (SND (f (s with outcomes := SOME (os ++ [probe_failed_outcome])))).scopes /\
    ~NULL (SND (f (s with outcomes := SOME (os ++ [empty_failed_outcome])))).scopes /\
    source_wrapper_cut_at f s os ==>
    source_wrapper_cut_at (finally (try f handle_loop_exception) pop_scope) s os) /\
  (!(f:evaluation_state -> value evaluation_result) cx nr view prev s os.
    (!(h:evaluation_state -> value evaluation_result) st r t. h st = (r,t) ==>
      (FST (finally_unless_halt
        (finally (try h handle_function) (pop_function prev))
        (unlock_if_nr cx nr view) st) =
        INR (Error (RuntimeError "create outcome accounts")) <=>
        r = INR (Error (RuntimeError "create outcome accounts"))) /\
      (SND (finally_unless_halt
        (finally (try h handle_function) (pop_function prev))
        (unlock_if_nr cx nr view) st)).requests = t.requests) /\
    source_wrapper_cut_at f s os ==>
    source_wrapper_cut_at (finally_unless_halt
      (finally (try f handle_function) (pop_function prev))
      (unlock_if_nr cx nr view)) s os)
Proof
  conj_tac >- suspend "pop" >>
  conj_tac >- suspend "set" >>
  conj_tac >- suspend "loop" >>
  suspend "internal"
QED

Resume source_replay_cut_wrappers[set]:
  rpt gen_tac >> strip_tac >>
  `finally f (set_scopes prev) = (\s. (\(r,t). (r,t with scopes := prev)) (f s))`
    by (simp[FUN_EQ_THM] >> gen_tac >> Cases_on `f s'` >>
        Cases_on `q` >>
        simp[vyperStateTheory.finally_def, vyperStateTheory.set_scopes_def,
          vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
          vyperStateTheory.return_def, vyperStateTheory.raise_def]) >>
  pop_assum SUBST1_TAC >>
  qspecl_then [`\(r,t). (r,t with scopes := prev)`,`f`,`s`,`os`]
    mp_tac source_replay_cut_postprocess >>
  impl_tac
  >- (simp[] >> conj_tac
      >- (rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >>
          simp[vyperStateTheory.erase_storage_trace_def] >> metis_tac[]) >>
      Cases_on `f (s with outcomes := SOME (os ++ [probe_failed_outcome]))` >>
      Cases_on `f (s with outcomes := SOME (os ++ [empty_failed_outcome]))` >> simp[]) >>
  simp[]
QED

Theorem source_replay_cut_pop[local]:
  !f s os.
    ~NULL (SND (f (s with outcomes := SOME (os ++ [probe_failed_outcome])))).scopes /\
    ~NULL (SND (f (s with outcomes := SOME (os ++ [empty_failed_outcome])))).scopes /\
    source_wrapper_cut_at f s os ==>
    source_wrapper_cut_at (finally f pop_scope) s os
Proof
  rpt gen_tac >> strip_tac >>
  `finally f pop_scope = (\s. (\(r,t).
      case t.scopes of [] => (INR (Error (TypeError "pop_scope")),t)
        | h::tl => (r,t with scopes := tl)) (f s))`
    by (simp[FUN_EQ_THM] >> gen_tac >> Cases_on `f s'` >>
        Cases_on `q` >> Cases_on `r.scopes` >>
        simp[vyperStateTheory.finally_def, vyperStateTheory.pop_scope_def,
          vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
          vyperStateTheory.return_def, vyperStateTheory.raise_def]) >>
  pop_assum SUBST1_TAC >>
  qspecl_then [`\(r,t). case t.scopes of
      [] => (INR (Error (TypeError "pop_scope")),t)
      | h::tl => (r,t with scopes := tl)`,`f`,`s`,`os`]
    mp_tac source_replay_cut_postprocess >>
  impl_tac
  >- (rpt conj_tac
      >- (rpt gen_tac >> Cases_on `t.scopes` >> simp[])
      >- (rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >>
          simp[] >> strip_tac >>
          `x1.scopes = y1.scopes` by
            (qpat_x_assum `erase_storage_trace _ = _` mp_tac >>
             simp[vyperStateTheory.erase_storage_trace_def,
               vyperStateTheory.evaluation_state_component_equality]) >>
          Cases_on `x1.scopes` >> fs[] >>
          fs[vyperStateTheory.erase_storage_trace_def] >>
          qpat_x_assum `_ = y1.scopes` (SUBST1_TAC o SYM) >> simp[])
      >- (rpt gen_tac >> Cases_on `t.scopes` >> simp[])
      >- (rpt gen_tac >> Cases_on `t.scopes` >> simp[])
      >- (Cases_on `f (s with outcomes := SOME (os ++ [probe_failed_outcome]))` >>
          Cases_on `r.scopes` >> gvs[])
      >- (Cases_on `f (s with outcomes := SOME (os ++ [empty_failed_outcome]))` >>
          Cases_on `r.scopes` >> gvs[]) >>
      rpt gen_tac >> Cases_on `t.scopes` >> simp[]) >>
  simp[]
QED

Resume source_replay_cut_wrappers[pop]:
  simp[source_replay_cut_pop]
QED

Resume source_replay_cut_wrappers[loop]:
  rpt gen_tac >> strip_tac >>
  qspecl_then [`try f handle_loop_exception`,`s`,`os`]
    mp_tac source_replay_cut_pop >>
  reverse impl_tac >- simp[] >>
  `!st. SND (try f handle_loop_exception st) = SND (f st)` by
    (gen_tac >> Cases_on `f st` >> Cases_on `q` >>
     simp[vyperStateTheory.try_def] >>
     Cases_on `y` >>
     simp[handle_loop_exception_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def]) >>
  simp[] >>
  `try f handle_loop_exception = (\s. (\(r,t).
    case r of INL v => (INL v,t) | INR ex =>
      if ex = ContinueException then (INL F,t)
      else if ex = BreakException then (INL T,t) else (INR ex,t)) (f s))`
    by (simp[FUN_EQ_THM] >> gen_tac >> Cases_on `f s'` >> Cases_on `q` >>
        simp[vyperStateTheory.try_def, handle_loop_exception_def,
          vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
        Cases_on `y` >> simp[vyperStateTheory.return_def, vyperStateTheory.raise_def]) >>
  pop_assum SUBST1_TAC >>
  qspecl_then [`\(r,t). case r of INL v => (INL v,t) | INR ex =>
      if ex = ContinueException then (INL F,t)
      else if ex = BreakException then (INL T,t) else (INR ex,t)`,
      `f`,`s`,`os`] mp_tac source_replay_cut_postprocess >>
  impl_tac
  >- (rpt conj_tac
      >- (rpt gen_tac >> Cases_on `r` >> simp[] >> Cases_on `y` >> simp[])
      >- (rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >>
          simp[] >> strip_tac >> gvs[] >> Cases_on `x0` >> simp[] >>
          Cases_on `y` >> simp[])
      >- (rpt gen_tac >> Cases_on `r` >> simp[] >> Cases_on `y` >> simp[])
      >- (rpt gen_tac >> Cases_on `r` >> simp[] >> Cases_on `y` >> simp[])
      >- (Cases_on `f (s with outcomes := SOME (os ++ [probe_failed_outcome]))` >>
          Cases_on `q` >> simp[] >> Cases_on `y` >> simp[])
      >- (Cases_on `f (s with outcomes := SOME (os ++ [empty_failed_outcome]))` >>
          Cases_on `q` >> simp[] >> Cases_on `y` >> simp[]) >>
      rpt gen_tac >> Cases_on `r` >> simp[] >> Cases_on `y` >> simp[]) >>
  simp[]
QED

Resume source_replay_cut_wrappers[internal]:
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `post = \(r,t). finally_unless_halt
    (finally (try (\st. (r,t)) handle_function) (pop_function prev))
    (unlock_if_nr cx nr view) t` >>
  `finally_unless_halt (finally (try f handle_function) (pop_function prev))
      (unlock_if_nr cx nr view) = (\st. post (f st))` by
    (simp[FUN_EQ_THM, Abbr `post`] >> gen_tac >> Cases_on `f st` >>
     simp[vyperStateTheory.finally_unless_halt_def, vyperStateTheory.finally_def,
       vyperStateTheory.try_def]) >>
  pop_assum SUBST1_TAC >>
  qspecl_then [`post`,`f`,`s`,`os`] mp_tac source_replay_cut_postprocess >>
  reverse impl_tac >- simp[] >>
  rpt conj_tac
  >- (rpt gen_tac >> simp[Abbr `post`] >>
      Cases_on `nr` >> Cases_on `view` >> Cases_on `cx.nonreentrant_slot` >>
      Cases_on `r` >>
      simp[vyperStateTheory.try_def, vyperStateTheory.finally_def,
        vyperStateTheory.finally_unless_halt_def, vyperStateTheory.ignore_bind_def,
        vyperStateTheory.bind_def, pop_function_def, vyperStateTheory.set_scopes_def,
        vyperStateTheory.return_def, vyperStateTheory.raise_def,
        unlock_if_nr_def, release_nonreentrant_lock_def,
        vyperStateTheory.update_transient_def, vyperStateTheory.get_transient_storage_def,
        vyperStateTheory.record_storage_event_def] >>
      Cases_on `y` >> simp[handle_function_def, vyperStateTheory.return_def,
        vyperStateTheory.raise_def, vyperStateTheory.ignore_bind_def,
        vyperStateTheory.bind_def])
  >- (rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >>
      simp[] >> strip_tac >> gvs[] >>
      simp[Abbr `post`] >>
      Cases_on `nr` >> Cases_on `view` >> Cases_on `cx.nonreentrant_slot` >>
      Cases_on `x0` >>
      simp[vyperStateTheory.try_def, vyperStateTheory.finally_def,
        vyperStateTheory.finally_unless_halt_def, vyperStateTheory.ignore_bind_def,
        vyperStateTheory.bind_def, pop_function_def, vyperStateTheory.set_scopes_def,
        vyperStateTheory.return_def, vyperStateTheory.raise_def,
        unlock_if_nr_def, release_nonreentrant_lock_def,
        vyperStateTheory.update_transient_def, vyperStateTheory.get_transient_storage_def,
        vyperStateTheory.record_storage_event_def] >>
      fs[vyperStateTheory.erase_storage_trace_def,
        vyperStateTheory.evaluation_state_component_equality] >>
      Cases_on `y` >>
      simp[handle_function_def, vyperStateTheory.return_def,
        vyperStateTheory.raise_def, vyperStateTheory.ignore_bind_def,
        vyperStateTheory.bind_def, vyperStateTheory.finally_def,
        vyperStateTheory.finally_unless_halt_def, pop_function_def,
        vyperStateTheory.set_scopes_def] >>
      fs[vyperStateTheory.erase_storage_trace_def,
        vyperStateTheory.evaluation_state_component_equality])
  >- (rpt gen_tac >> simp[Abbr `post`] >>
      Cases_on `nr` >> Cases_on `view` >> Cases_on `cx.nonreentrant_slot` >>
      Cases_on `r` >>
      simp[vyperStateTheory.try_def, vyperStateTheory.finally_def,
        vyperStateTheory.finally_unless_halt_def, vyperStateTheory.ignore_bind_def,
        vyperStateTheory.bind_def, pop_function_def, vyperStateTheory.set_scopes_def,
        vyperStateTheory.return_def, vyperStateTheory.raise_def,
        unlock_if_nr_def, release_nonreentrant_lock_def,
        vyperStateTheory.update_transient_def, vyperStateTheory.get_transient_storage_def,
        vyperStateTheory.record_storage_event_def] >>
      Cases_on `y` >> simp[handle_function_def, vyperStateTheory.return_def,
        vyperStateTheory.raise_def, vyperStateTheory.ignore_bind_def,
        vyperStateTheory.bind_def])
  >- (rpt gen_tac >> simp[Abbr `post`] >> strip_tac >>
      Cases_on `nr` >> Cases_on `view` >> Cases_on `cx.nonreentrant_slot` >>
      Cases_on `r` >>
      simp[vyperStateTheory.try_def, vyperStateTheory.finally_def,
        vyperStateTheory.finally_unless_halt_def, vyperStateTheory.ignore_bind_def,
        vyperStateTheory.bind_def, pop_function_def, vyperStateTheory.set_scopes_def,
        vyperStateTheory.return_def, vyperStateTheory.raise_def,
        unlock_if_nr_def, release_nonreentrant_lock_def,
        vyperStateTheory.update_transient_def, vyperStateTheory.get_transient_storage_def,
        vyperStateTheory.record_storage_event_def] >>
      Cases_on `y` >> simp[handle_function_def, vyperStateTheory.return_def,
        vyperStateTheory.raise_def, vyperStateTheory.ignore_bind_def,
        vyperStateTheory.bind_def])
  >- (Cases_on `f (s with outcomes := SOME (os ++ [probe_failed_outcome]))` >>
      simp[Abbr `post`] >>
      pop_last_assum (qspecl_then [`\st. (q,r)`,`r`,`q`,`r`] mp_tac) >> simp[])
  >- (Cases_on `f (s with outcomes := SOME (os ++ [empty_failed_outcome]))` >>
      simp[Abbr `post`] >>
      pop_last_assum (qspecl_then [`\st. (q,r)`,`r`,`q`,`r`] mp_tac) >> simp[]) >>
  rpt gen_tac >> simp[Abbr `post`] >>
  first_x_assum (qspecl_then [`\st. (r,t)`,`t`,`r`,`t`] mp_tac) >> simp[]
QED

Finalise source_replay_cut_wrappers[local]

(* Keep the parser-only cut notation through the mutual lift. *)

Theorem source_create_empty_cut_state[local]:
  !salt value code rof k st re se.
    (!v s r t. s.outcomes = SOME [] /\
      accounts_runtime_well_typed s.accounts /\ k v s = (r,t) ==>
      t.outcomes = SOME [] /\ accounts_runtime_well_typed t.accounts) /\
    bind (create_oracle_result salt value code rof) k
      (st with outcomes := SOME [empty_failed_outcome]) = (re,se) ==>
    se.outcomes = SOME [] /\ accounts_runtime_well_typed se.accounts
Proof
  rpt gen_tac >> strip_tac >>
  `accounts_runtime_well_typed empty_failed_outcome.co_accounts` by
    simp[empty_failed_outcome_def, accounts_runtime_well_typed_def,
      vfmStateTheory.lookup_account_def] >>
  gvs[vyperStateTheory.bind_def, vyperCreateTheory.create_oracle_result_def,
      take_create_outcome_def, take_outcome_def, record_request_def,
      create_outcome_request_def, computed_precompile_def] >>
  Cases_on `salt` >> gvs[] >> Cases_on `rof` >>
  gvs[empty_failed_outcome_def, adopt_call_outcome_equation] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem source_create_probe_cut[local]:
  !salt value code rof k st rp sp.
    (!v s. s.outcomes = SOME [] /\ accounts_runtime_well_typed s.accounts ==>
      FST (k v s) <> INR (Error (RuntimeError "create outcome accounts"))) /\
    bind (create_oracle_result salt value code rof) k
      (st with outcomes := SOME [probe_failed_outcome]) = (rp,sp) ==>
    rp = INR (Error (RuntimeError "create outcome accounts")) /\
    ~NULL sp.requests /\
    LAST sp.requests = create_outcome_request
      (case salt of NONE => CreateCall | SOME s => Create2Call s) value code st /\
    FST (bind (create_oracle_result salt value code rof) k
      (st with outcomes := SOME [empty_failed_outcome])) <>
      INR (Error (RuntimeError "create outcome accounts")) /\
    bind (create_oracle_result salt value code rof) k
      (st with outcomes := SOME []) =
    bind (create_oracle_result salt value code rof) k
      (st with outcomes := SOME [failed_outcome (LAST sp.requests)])
Proof
  rpt gen_tac >> strip_tac >>
  `~accounts_runtime_well_typed probe_failed_outcome.co_accounts` by
    simp[probe_failed_outcome_def, empty_failed_outcome_def,
      accounts_runtime_well_typed_def, account_runtime_well_typed_def,
      vfmStateTheory.lookup_account_def] >>
  `accounts_runtime_well_typed empty_failed_outcome.co_accounts` by
    simp[empty_failed_outcome_def, accounts_runtime_well_typed_def,
      vfmStateTheory.lookup_account_def] >>
  gvs[vyperStateTheory.bind_def, vyperCreateTheory.create_oracle_result_def,
      take_create_outcome_def, take_outcome_def, record_request_def,
      create_outcome_request_def, computed_precompile_def] >>
  Cases_on `salt` >> gvs[] >>
  Cases_on `rof` >>
  gvs[empty_failed_outcome_def, adopt_call_outcome_equation] >>
  first_x_assum irule >>
  simp[accounts_runtime_well_typed_def, vfmStateTheory.lookup_account_def]
QED

(* Exhausted-mode primitive interfaces. *)
Theorem source_exhausted_create_oracle_safety[local]:
  !salt value code rof s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    create_oracle_result salt value code rof s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  drule (GEN_ALL (REWRITE_RULE [GSYM AND_IMP_INTRO]
    take_create_outcome_exhausted)) >>
  simp[] >>
  disch_tac >>
  Cases_on `salt` >> Cases_on `rof` >>
  gvs[vyperCreateTheory.create_oracle_result_def, adopt_call_outcome_equation,
      failed_outcome_def, create_outcome_request_def]
QED

Theorem source_exhausted_create_safety[local]:
  !cx kind has_salt rof tys vs cs s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    eval_create cx kind has_salt rof tys vs cs s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dest_create_args kind has_salt vs` >>
  gvs[vyperCreateTheory.eval_create_def, vyperStateTheory.bind_def,
      vyperStateTheory.ignore_bind_def, vyperStateTheory.lift_option_type_def,
      vyperStateTheory.lift_option_def, vyperStateTheory.raise_def,
      vyperStateTheory.return_def] >>
  Cases_on `create_arg_ctor_types kind has_salt tys` >>
  gvs[vyperStateTheory.get_accounts_def, vyperStateTheory.lift_option_type_def,
      vyperStateTheory.lift_option_def, vyperStateTheory.raise_def,
      vyperStateTheory.return_def] >>
  Cases_on `build_create_code (get_tenv cx) kind x s.accounts x' cs` >>
  gvs[vyperStateTheory.lift_option_type_def, vyperStateTheory.lift_option_def,
      vyperStateTheory.raise_def, vyperStateTheory.return_def,
      vyperStateTheory.check_def, vyperStateTheory.assert_def,
      vyperStateTheory.check_not_static_def, AllCaseEqs()] >>
  drule_all source_exhausted_create_oracle_safety >> simp[]
QED

Theorem source_exhausted_send_safety[local]:
  !cx gas vs s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    eval_send cx gas vs s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `vs`
  >- gvs[eval_send_def, vyperStateTheory.raise_def] >>
  rename1 `h::tl` >> Cases_on `tl`
  >- gvs[eval_send_def, vyperStateTheory.raise_def] >>
  Cases_on `dest_AddressV h` >> Cases_on `dest_NumV h'` >>
  Cases_on `cx.txn.is_static` >>
  gvs[eval_send_def, vyperStateTheory.bind_def,
      vyperStateTheory.ignore_bind_def, vyperStateTheory.type_check_def,
      vyperStateTheory.assert_def, vyperStateTheory.check_def,
      vyperStateTheory.lift_option_type_def, vyperStateTheory.raise_def,
      vyperStateTheory.return_def, frame_call_value_def,
      AllCaseEqs()] >>
  gvs[take_call_outcome_def, take_request_outcome_def, take_outcome_def,
      failed_outcome_def, vyperStateTheory.bind_def,
      vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
      vyperStateTheory.assert_def, vyperStateTheory.raise_def,
      vyperStateTheory.return_def, AllCaseEqs()]
QED

Theorem source_exhausted_raw_call_safety[local]:
  !cx flags addr data amount gas s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    eval_raw_call cx flags addr data amount gas s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `cx.txn.is_static` >> Cases_on `flags.rcf_is_static` >>
  Cases_on `flags.rcf_is_delegate` >>
  gvs[eval_raw_call_def, frame_call_value_def,
      vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.type_check_def, vyperStateTheory.check_def,
      vyperStateTheory.assert_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, take_call_outcome_def,
      take_delegate_outcome_def, take_request_outcome_def, take_outcome_def,
      failed_outcome_def, adopt_call_outcome_equation,
      call_outcome_request_def, delegate_outcome_request_def, AllCaseEqs()] >>
  Cases_on `flags.rcf_revert_on_failure` >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.raise_def,
      vyperStateTheory.return_def]
QED

Theorem source_exhausted_ext_call_safety[local]:
  !cx static skip sig opts vs s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    eval_ext_call cx static skip sig opts vs s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >> PairCases_on `sig` >> Cases_on `vs`
  >- gvs[eval_ext_call_def, vyperStateTheory.raise_def] >>
  Cases_on `static` >> Cases_on `dest_AddressV h` >>
  Cases_on `cx.txn.is_static` >>
  gvs[eval_ext_call_def, vyperStateTheory.bind_def,
      vyperStateTheory.ignore_bind_def, vyperStateTheory.type_check_def,
      vyperStateTheory.assert_def, vyperStateTheory.check_def,
      vyperStateTheory.lift_option_type_def, vyperStateTheory.raise_def,
      vyperStateTheory.return_def, vyperStateTheory.get_accounts_def,
      AllCaseEqs()] >>
  gvs[COND_RATOR, vyperMiscTheory.option_CASE_rator,
      vyperMiscTheory.sum_CASE_rator, vyperStateTheory.raise_def,
      vyperStateTheory.return_def, AllCaseEqs()] >>
  gvs[frame_call_value_def, eval_ext_call_effects_def,
      take_call_outcome_def, take_request_outcome_def, take_outcome_def,
      failed_outcome_def, vyperStateTheory.bind_def,
      vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
      vyperStateTheory.assert_def, vyperStateTheory.raise_def,
      vyperStateTheory.return_def, AllCaseEqs()] >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperStateTheory.raise_def,
      vyperStateTheory.return_def, AllCaseEqs()] >>
  gvs[take_call_outcome_def, take_request_outcome_def, take_outcome_def,
      failed_outcome_def, vyperStateTheory.bind_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED

Theorem source_exhausted_transfer_safety[local]:
  !a b n s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    transfer_value a b n s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  `accounts_runtime_well_typed t.accounts` by
    (drule (REWRITE_RULE
       [GSYM vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed]
       vyperTypeExtCallSoundnessTheory.transfer_value_accounts_well_typed) >>
     disch_then (qspecl_then [`a`,`b`,`n`] mp_tac) >> simp[]) >>
  gvs[transfer_value_def, vyperStateTheory.bind_def,
      vyperStateTheory.ignore_bind_def, vyperStateTheory.get_accounts_def,
      vyperStateTheory.check_def, vyperStateTheory.assert_def,
      vyperStateTheory.update_accounts_def, vyperStateTheory.raise_def,
      vyperStateTheory.return_def, COND_RATOR, AllCaseEqs()]
QED

Theorem source_exhausted_selfdestruct_update_safety[local]:
  !a s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    update_accounts (\acc. update_account a
      (lookup_account a acc with balance := 0) acc) s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[vyperStateTheory.update_accounts_def, vyperStateTheory.return_def] >>
  rewrite_tac[vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
  irule vyperTypeExtCallSoundnessTheory.accounts_well_typed_update_account >>
  gvs[vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
  gvs[vyperTypeInvariantsTheory.accounts_well_typed_def,
      vyperTypeInvariantsTheory.account_well_typed_def] >>
  first_x_assum (qspec_then `a` mp_tac) >> simp[]
QED

Theorem source_exhausted_effect_safety[local]:
  (!cx gas vs s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    eval_send cx gas vs s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx static skip sig opts vs s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    eval_ext_call cx static skip sig opts vs s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx flags addr data amount gas s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    eval_raw_call cx flags addr data amount gas s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx kind salt rof tys vs cs s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    eval_create cx kind salt rof tys vs cs s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!a b n s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    transfer_value a b n s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!a s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    update_accounts (\acc. update_account a
      (lookup_account a acc with balance := 0) acc) s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts")))
Proof
  rpt conj_tac >> FIRST (map MATCH_ACCEPT_TAC
    [source_exhausted_send_safety, source_exhausted_ext_call_safety,
     source_exhausted_raw_call_safety, source_exhausted_create_safety,
     source_exhausted_transfer_safety, source_exhausted_selfdestruct_update_safety])
QED

(* Reviewed exhausted-oracle replay: erase only synthetic ghost traces.
 * The original actual storage certificates retain their original traces. *)
Theorem source_array_set_excludes_create_error[local]:
  !tv av i v. array_set_index tv av i v <>
    INR (RuntimeError "create outcome accounts")
Proof
  rpt gen_tac >> Cases_on `av` >>
  simp[vyperValueOperationTheory.array_set_index_def] >>
  rpt (CASE_TAC >> gvs[])
QED

Theorem source_assign_subscripts_excludes_create_error[local]:
  !path tv v op.
    assign_subscripts tv v path op <>
      INR (RuntimeError "create outcome accounts")
Proof
  Induct_on `path`
  >- (rpt gen_tac >> Cases_on `op` >> Cases_on `v` >>
      simp[vyperStateTheory.assign_subscripts_def,
           oneline vyperValueOperationTheory.append_element_def,
           oneline vyperValueOperationTheory.pop_element_def] >>
      rpt (CASE_TAC >> gvs[])) >>
  rpt gen_tac >> Cases_on `h`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >>
      simp[vyperStateTheory.assign_subscripts_def] >>
      Cases_on `v` >> simp[vyperStateTheory.assign_subscripts_def] >>
      qmatch_goalsub_rename_tac `array_index tv av idx` >>
      Cases_on `array_index tv av idx` >> simp[] >>
      qmatch_goalsub_abbrev_tac `assign_subscripts etv elem path op` >>
      Cases_on `assign_subscripts etv elem path op` >>
      gvs[source_array_set_excludes_create_error] >> metis_tac[]) >>
  Cases_on `v` >> simp[vyperStateTheory.assign_subscripts_def] >>
  qmatch_goalsub_rename_tac `ALOOKUP fields id` >>
  Cases_on `ALOOKUP fields id` >> simp[] >>
  qmatch_goalsub_abbrev_tac `assign_subscripts ftv elem path op` >>
  Cases_on `assign_subscripts ftv elem path op` >> gvs[] >> metis_tac[]
QED

Theorem source_write_place_excludes_create_error[local]:
  !cx p v s r t.
    write_place cx p v s = (r,t) ==>
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> Cases_on `p` >> strip_tac >>
  gvs prefix_atomic_defs >>
  rpt (FULL_CASE_TAC >>
    gvs (prefix_atomic_defs @
      [vyperStateTheory.replace_memory_entry_def, AllCaseEqs()])) >>
  gvs (prefix_atomic_defs @ [vyperStateTheory.replace_memory_entry_def,
    vyperMiscTheory.prod_CASE_rator, vyperMiscTheory.sum_CASE_rator,
    vyperMiscTheory.option_CASE_rator, AllCaseEqs()])
  >~ [`find_containing_scope _ _ = SOME parts`]
  >- (PairCases_on `parts` >>
      gvs (prefix_atomic_defs @ [vyperStateTheory.replace_memory_entry_def,
        AllCaseEqs()]) >>
      rpt (FULL_CASE_TAC >> gvs (prefix_atomic_defs @ [AllCaseEqs()])) >>
      metis_tac[source_assign_subscripts_excludes_create_error]) >>
  metis_tac[source_assign_subscripts_excludes_create_error]
QED

Theorem source_exhausted_write_place_safety[local]:
  !cx p v s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    write_place cx p v s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  `accounts_runtime_well_typed t.accounts` by
    (gvs[vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
     drule_all vyperPlaceWriteSoundnessTheory.write_place_preserves_accounts_well_typed >>
     simp[]) >>
  `t.outcomes = SOME []` by
    (mp_tac (MATCH_MP outcomes_suffix_frame
       (SPEC_ALL outcomes_frame_write_place)) >>
     simp[outcomes_suffix_def] >> disch_then (qspec_then `s` mp_tac) >>
     simp[outcome_suffix_def]) >>
  drule source_write_place_excludes_create_error >> simp[]
QED

Theorem source_read_place_excludes_create_error[local]:
  !cx p s r t. read_place cx p s = (r,t) ==>
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> Cases_on `p` >> strip_tac >>
  gvs prefix_atomic_defs >>
  rpt (FULL_CASE_TAC >> gvs (prefix_atomic_defs @ [AllCaseEqs()]))
  >~ [`read_memory_path _ _ = INR _`]
  >- (drule vyperStateTheory.read_memory_path_error_shape >> strip_tac >> gvs[]) >>
  drule vyperStateTheory.evaluate_subscripts_error_shape >> strip_tac >> gvs[]
QED

Theorem source_exhausted_read_place_safety[local]:
  !cx p s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    read_place cx p s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  drule vyperStateTheory.read_place_state >> strip_tac >> gvs[] >>
  drule source_read_place_excludes_create_error >> simp[]
QED

Theorem source_exhausted_write_storage_safety[local]:
  !cx tr slot tv v s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    write_storage_slot cx tr slot tv v s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  irule source_exhausted_write_place_safety >>
  qexistsl_tac [`cx`,`StoragePlace tr slot tv`,`s`,`v`] >>
  simp[vyperStateTheory.write_place_def]
QED

Theorem source_exhausted_place_type_safety[local]:
  !cx p s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    place_type_value cx p s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> Cases_on `p` >> strip_tac >>
  gvs prefix_atomic_defs >>
  rpt (FULL_CASE_TAC >> gvs (prefix_atomic_defs @ [AllCaseEqs()]))
QED

Theorem source_append_element_excludes_create_error[local]:
  !tv old v. append_element tv old v <> INR (RuntimeError "create outcome accounts")
Proof
  rpt gen_tac >> Cases_on `old` >>
  simp[oneline vyperValueOperationTheory.append_element_def] >>
  rpt (CASE_TAC >> gvs[])
QED

Theorem source_append_fallback_safety[local]:
  !cx p v s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    bind (place_type_value cx p) (\tv.
      bind (read_place cx p) (\old.
        bind (lift_sum (append_element tv old v)) (\updated. write_place cx p updated))) s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[vyperStateTheory.bind_def, AllCaseEqs()] >>
  imp_res_tac vyperStateTheory.place_type_value_state >>
  imp_res_tac vyperStateTheory.read_place_state >> gvs[] >>
  gvs[vyperStateTheory.lift_sum_def, vyperMiscTheory.sum_CASE_rator,
      vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()]
  >~ [`write_place _ _ _ _ = (_,_)`]
  >- (drule_all source_exhausted_write_place_safety >> simp[]) >>
  metis_tac[source_exhausted_place_type_safety,
    source_exhausted_read_place_safety, source_append_element_excludes_create_error]
QED

Theorem source_exhausted_append_place_safety[local]:
  !cx p v s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    append_place cx p v s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> Cases_on `p`
  >- (rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
      simp_tac bool_ss [vyperStateTheory.append_place_def] >>
      all_tac
      >~ [`ArrayTV tv bd`]
      >- (Cases_on `bd` >>
          simp_tac bool_ss [vyperStateTheory.append_place_def] >> strip_tac
          >- (gvs[ETA_THM] >> drule_all source_append_fallback_safety >> simp[]) >>
          gvs[vyperStorageBackendTheory.get_storage_backend_eq,
              vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
              vyperStateTheory.check_def, vyperStateTheory.assert_def,
              vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
          drule_all source_exhausted_write_storage_safety >> strip_tac >>
          gvs[] >> drule_all source_exhausted_write_storage_safety >> simp[]) >>
      simp[ETA_THM] >> metis_tac[source_append_fallback_safety]) >>
  simp_tac bool_ss [vyperStateTheory.append_place_def] >>
  simp[ETA_THM] >> metis_tac[source_append_fallback_safety]
QED

Theorem source_pop_values_exclude_create_error[local]:
  (!v. popped_value v <> INR (RuntimeError "create outcome accounts")) /\
  (!v. pop_element v <> INR (RuntimeError "create outcome accounts"))
Proof
  conj_tac >> gen_tac >> Cases_on `v` >>
  simp[oneline vyperValueOperationTheory.popped_value_def,
       oneline vyperValueOperationTheory.pop_element_def] >>
  rpt (CASE_TAC >> gvs[])
QED

Theorem source_exhausted_pop_place_safety[local]:
  !cx p s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    pop_place cx p s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> Cases_on `p`
  >- (rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
      simp_tac bool_ss [vyperStateTheory.pop_place_def]
      >~ [`ArrayTV tv bd`]
      >- (Cases_on `bd` >>
          simp_tac bool_ss [vyperStateTheory.pop_place_def] >> strip_tac >>
          gvs[vyperStorageBackendTheory.get_storage_backend_eq,
              vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
              vyperStateTheory.check_def, vyperStateTheory.assert_def,
              vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
          drule_all source_exhausted_write_storage_safety >> simp[]) >>
      rpt strip_tac >> gvs[vyperStateTheory.raise_def]) >>
  strip_tac >> gvs prefix_atomic_defs >>
  rpt (FULL_CASE_TAC >> gvs (prefix_atomic_defs @ [AllCaseEqs()])) >>
  all_tac
  >~ [`find_containing_scope _ _ = SOME parts`]
  >- (PairCases_on `parts` >>
      gvs (prefix_atomic_defs @ [AllCaseEqs()]) >>
      gvs (prefix_atomic_defs @ [vyperMiscTheory.sum_CASE_rator,
        vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator, AllCaseEqs()]) >>
      all_tac
      >~ [`read_memory_path _ _ = INR _`]
      >- (drule vyperStateTheory.read_memory_path_error_shape >> strip_tac >> gvs[])
      >~ [`evaluate_subscripts _ _ _ = INR _`]
      >- (drule vyperStateTheory.evaluate_subscripts_error_shape >> strip_tac >> gvs[]) >>
      metis_tac[source_assign_subscripts_excludes_create_error,
        source_pop_values_exclude_create_error]) >>
  gvs (prefix_atomic_defs @ [vyperMiscTheory.sum_CASE_rator,
    vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator, AllCaseEqs()]) >>
  all_tac
  >~ [`evaluate_subscripts _ _ _ = INR _`]
  >- (drule vyperStateTheory.evaluate_subscripts_error_shape >> strip_tac >> gvs[]) >>
  metis_tac[source_assign_subscripts_excludes_create_error,
    source_pop_values_exclude_create_error]
QED

Theorem source_exhausted_read_result_safety[local]:
  !cx v s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    read_result cx v s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> Cases_on `v` >>
  simp_tac bool_ss [vyperStateTheory.read_result_def] >> strip_tac
  >- gvs[vyperStateTheory.return_def]
  >- (drule_all source_exhausted_read_place_safety >> simp[]) >>
  gvs[vyperStateTheory.raise_def]
QED

Theorem source_exhausted_read_results_safety[local]:
  !cx vs s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    read_results cx vs s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  gen_tac >> Induct >> rpt gen_tac >> strip_tac
  >- gvs[vyperStateTheory.read_results_def, vyperStateTheory.return_def] >>
  gvs[vyperStateTheory.read_results_def, vyperStateTheory.bind_def,
      vyperStateTheory.return_def, AllCaseEqs()] >>
  drule_all source_exhausted_read_result_safety >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem source_exhausted_get_place_safety[local]:
  !pv s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    get_place pv s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> Cases_on `pv` >>
  simp[vyperStateTheory.get_place_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def] >> rpt strip_tac >> gvs[]
QED

Theorem source_exhausted_conditional_safety[local]:
  !cx pv s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    conditional_result cx pv s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> Cases_on `pv` >> strip_tac >>
  gvs[vyperStateTheory.conditional_result_def, vyperStateTheory.bind_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
  imp_res_tac vyperStateTheory.place_type_value_state >> gvs[] >>
  all_tac
  >~ [`place_type_value _ _ _ = (INR _,_)`]
  >- (drule_all source_exhausted_place_type_safety >> simp[]) >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  IF_CASES_TAC >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all source_exhausted_read_place_safety >> simp[]
QED

Theorem source_exhausted_length_safety[local]:
  !cx pv s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    result_array_length cx pv s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[oneline vyperStateTheory.result_array_length_def,
      vyperStateTheory.eval_result_CASE_rator,
      vyperStateTheory.place_CASE_rator,
      vyperValueTheory.type_value_CASE_rator,
      vyperASTTheory.bound_CASE_rator, AllCaseEqs()] >>
  gvs[vyperStorageBackendTheory.get_storage_backend_eq,
      vyperStateTheory.bind_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, AllCaseEqs()] >>
  drule_all source_exhausted_read_result_safety >> strip_tac >> gvs[] >>
  rpt (FULL_CASE_TAC >>
    gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def])
QED

Theorem source_exhausted_extend_storage_safety[local]:
  !cx tr slot tv sb s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    extend_storage_place cx tr slot tv sb s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  drule vyperPlaceFramesTheory.extend_storage_place_state >> strip_tac >> gvs[] >>
  Cases_on `tv` >> Cases_on `sb` >>
  gvs[vyperStateTheory.extend_storage_place_def,
      vyperStateTheory.raise_def] >>
  rpt (qpat_x_assum `extend_storage_place _ _ _ _ (ValueSubscript _) _ = _` mp_tac >>
       rename1 `ValueSubscript v` >> Cases_on `v` >> strip_tac >>
       gvs[vyperStateTheory.extend_storage_place_def,
           vyperStateTheory.raise_def]) >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.check_def, vyperStateTheory.assert_def,
      vyperStateTheory.lift_option_type_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt (FULL_CASE_TAC >>
    gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def]) >>
  gvs[pairTheory.UNCURRY, vyperStateTheory.return_def] >>
  Cases_on `b` >>
  fs[Once vyperStateTheory.resolve_array_element_def] >>
  Cases_on `t` >> fs[Once vyperStateTheory.resolve_array_element_def] >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.check_def, vyperStateTheory.assert_def,
      vyperStorageBackendTheory.get_storage_backend_eq,
      vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
  fs[Once vyperStateTheory.resolve_array_element_def,
     vyperStateTheory.return_def]
QED

Theorem source_exhausted_extend_place_safety[local]:
  !cx pv sb s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    extend_place cx pv sb s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> Cases_on `pv` >> strip_tac >>
  gvs[vyperStateTheory.extend_place_def, vyperStateTheory.raise_def] >>
  all_tac
  >~ [`extend_place cx (PlaceR p) sb s = _`]
  >- (Cases_on `p` >>
      gvs[vyperStateTheory.extend_place_def, vyperStateTheory.bind_def,
          vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
          vyperStateTheory.lift_sum_def, AllCaseEqs()] >>
      imp_res_tac vyperStateTheory.place_type_value_state >>
      imp_res_tac vyperStateTheory.read_place_state >> gvs[] >>
      all_tac
      >~ [`extend_storage_place _ _ _ _ _ _ = _`]
      >- (drule_all source_exhausted_extend_storage_safety >> simp[]) >>
      all_tac
      >~ [`extend_storage_place _ _ _ _ _ _ = _`]
      >- (drule_all source_exhausted_extend_storage_safety >> simp[]) >>
      all_tac
      >>~- ([`place_type_value _ _ _ = (INR _,_)`],
            drule_all source_exhausted_place_type_safety >> simp[]) >>
      all_tac
      >>~- ([`read_place _ _ _ = (INR _,_)`],
            drule_all source_exhausted_read_place_safety >> simp[]) >>
      rpt (FULL_CASE_TAC >>
        gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def]) >>
      drule vyperStateTheory.evaluate_subscripts_error_shape >> strip_tac >> gvs[]) >>
  Cases_on `sb` >>
  gvs[vyperStateTheory.extend_place_def, vyperStateTheory.raise_def] >>
  Cases_on `v` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.lift_option_type_def,
      vyperStateTheory.record_storage_event_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt (FULL_CASE_TAC >>
    gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def])
QED

Theorem source_exhausted_select_safety[local]:
  !cx ty pv sb s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    select_result cx ty pv sb s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> Cases_on `pv` >> strip_tac >>
  gvs[vyperStateTheory.select_result_def]
  >- (gvs[vyperStateTheory.bind_def, vyperStateTheory.lift_option_type_def,
          vyperStateTheory.lift_sum_def, vyperStateTheory.return_def,
          vyperStateTheory.raise_def, AllCaseEqs()] >>
      rpt (FULL_CASE_TAC >>
        gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def]) >>
      drule vyperStateTheory.evaluate_subscripts_error_shape >> strip_tac >> gvs[]) >>
  drule_all source_exhausted_extend_place_safety >> simp[]
QED

Theorem source_exhausted_flag_safety[local]:
  !cx fid mid s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    lookup_flag_mem cx fid mid s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> PairCases_on `fid` >> strip_tac >>
  gvs[vyperStateTheory.lookup_flag_mem_def] >>
  rpt (FULL_CASE_TAC >>
    gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def])
QED

Theorem source_exhausted_global_safety[local]:
  !cx src id s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    lookup_global cx src id s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[vyperStateTheory.lookup_global_def,
      vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.lift_option_type_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt (FULL_CASE_TAC >>
    gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
        vyperStateTheory.lift_option_type_def,
        vyperStateTheory.record_storage_event_def,
        vyperStateTheory.return_def, vyperStateTheory.raise_def]) >>
  imp_res_tac vyperStatePreservationTheory.get_immutables_state >> gvs[] >>
  gvs[vyperStateTheory.get_immutables_def,
      vyperStateTheory.get_address_immutables_def,
      vyperStateTheory.bind_def, vyperStateTheory.lift_option_type_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt (FULL_CASE_TAC >>
    gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def])
QED

Theorem source_exhausted_place_safety[local]:
  (!cx p s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    read_place cx p s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx p v s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    write_place cx p v s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx p v s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    append_place cx p v s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx p s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    pop_place cx p s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx tr slot tv v s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    write_storage_slot cx tr slot tv v s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx p s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    place_type_value cx p s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx pv s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    read_result cx pv s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx pvs s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    read_results cx pvs s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!pv s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    get_place pv s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx pv s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    conditional_result cx pv s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx pv s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    result_array_length cx pv s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx tr slot tv sb s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    extend_storage_place cx tr slot tv sb s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx pv sb s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    extend_place cx pv sb s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx ty pv sb s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    select_result cx ty pv sb s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx src id s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    lookup_global cx src id s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts"))) /\
  (!cx fid mid s r t. accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    lookup_flag_mem cx fid mid s = (r,t) ==> accounts_runtime_well_typed t.accounts /\
    t.outcomes = SOME [] /\ r <> INR (Error (RuntimeError "create outcome accounts")))
Proof
  rpt conj_tac >> FIRST (map MATCH_ACCEPT_TAC
    [source_exhausted_read_place_safety, source_exhausted_write_place_safety,
     source_exhausted_append_place_safety, source_exhausted_pop_place_safety,
     source_exhausted_write_storage_safety, source_exhausted_place_type_safety,
     source_exhausted_read_result_safety, source_exhausted_read_results_safety,
     source_exhausted_get_place_safety, source_exhausted_conditional_safety,
     source_exhausted_length_safety, source_exhausted_extend_storage_safety,
     source_exhausted_extend_place_safety, source_exhausted_select_safety,
     source_exhausted_global_safety, source_exhausted_flag_safety])
QED

Theorem source_range_excludes_create_error[local]:
  !v1 v2. get_range_limits v1 v2 <>
    INR (RuntimeError "create outcome accounts")
Proof
  rpt gen_tac >> Cases_on `v1` >> Cases_on `v2` >>
  simp[vyperInterpreterTheory.get_range_limits_def] >>
  rpt (CASE_TAC >> gvs[])
QED

Theorem source_binop_excludes_create_error[local]:
  !u tv bop v1 v2. evaluate_binop u tv bop v1 v2 <>
    INR (RuntimeError "create outcome accounts")
Proof
  rpt gen_tac >> Cases_on `bop` >>
  simp[vyperValueOperationTheory.evaluate_binop_def,
       vyperValueOperationTheory.binop_negate_def,
       vyperValueOperationTheory.bounded_int_op_def,
       vyperValueOperationTheory.bounded_decimal_op_def,
       vyperValueOperationTheory.wrapped_int_op_def,
       AllCaseEqs()] >>
  simp[oneline vyperValueOperationTheory.binop_negate_def, AllCaseEqs()]
QED

Theorem source_concat_loop_excludes_create_error[local]:
  !n v sa ba vs. evaluate_concat_loop n v sa ba vs <>
    INR (RuntimeError "create outcome accounts")
Proof
  recInduct vyperValueOperationTheory.evaluate_concat_loop_ind >>
  rpt strip_tac >>
  gvs[vyperValueOperationTheory.evaluate_concat_loop_def, AllCaseEqs()]
QED

Theorem source_builtin_delegates_exclude_create_error[local]:
  (!n vs. evaluate_concat n vs <> INR (RuntimeError "create outcome accounts")) /\
  (!v sv lv n. evaluate_slice v sv lv n <> INR (RuntimeError "create outcome accounts")) /\
  (!dn v. evaluate_as_wei_value dn v <> INR (RuntimeError "create outcome accounts")) /\
  (!tx n. evaluate_block_hash tx n <> INR (RuntimeError "create outcome accounts"))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[vyperValueOperationTheory.evaluate_concat_def,
       source_concat_loop_excludes_create_error,
       vyperValueOperationTheory.evaluate_slice_def,
       vyperValueOperationTheory.evaluate_as_wei_value_def,
       vyperContextTheory.evaluate_block_hash_def, AllCaseEqs()]
QED

Theorem source_ec_delegates_exclude_create_error[local]:
  (!vs. evaluate_ecrecover vs <> INR (RuntimeError "create outcome accounts")) /\
  (!vs. evaluate_ecadd vs <> INR (RuntimeError "create outcome accounts")) /\
  (!vs. evaluate_ecmul vs <> INR (RuntimeError "create outcome accounts"))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[oneline vyperContextTheory.evaluate_ecrecover_def,
       oneline vyperContextTheory.evaluate_ecadd_def,
       oneline vyperContextTheory.evaluate_ecmul_def, AllCaseEqs()]
QED

Theorem source_builtin_excludes_create_error[local]:
  (!u tv bop v1 v2. evaluate_binop u tv bop v1 v2 <>
    INR (RuntimeError "create outcome accounts")) ==>
  !cx acc ty bt tys vs. evaluate_builtin cx acc ty bt tys vs <>
    INR (RuntimeError "create outcome accounts")
Proof
  strip_tac >> rpt gen_tac >> Cases_on `bt` >>
  simp[vyperContextTheory.evaluate_builtin_def,
       vyperContextTheory.evaluate_calldata_slice_def,
       source_builtin_delegates_exclude_create_error,
       source_ec_delegates_exclude_create_error,
       vyperValueOperationTheory.bounded_int_op_def,
       vyperValueOperationTheory.bounded_decimal_op_def, AllCaseEqs()]
QED

Theorem source_ordinary_pure_exclusions[local]:
  (!u tv bop v1 v2. evaluate_binop u tv bop v1 v2 <>
    INR (RuntimeError "create outcome accounts")) ==>
  (!cx acc ty bt tys vs. evaluate_builtin cx acc ty bt tys vs <>
    INR (RuntimeError "create outcome accounts")) /\
  (!cx acc self cty aty avs. evaluate_code_source cx acc self cty aty avs <>
    INR (RuntimeError "create outcome accounts")) /\
  (!tv neg v1 v2. evaluate_membership tv neg v1 v2 <>
    INR (RuntimeError "create outcome accounts"))
Proof
  strip_tac >>
  `!cx acc ty bt tys vs. evaluate_builtin cx acc ty bt tys vs <>
     INR (RuntimeError "create outcome accounts")` by
    (irule source_builtin_excludes_create_error >> simp[]) >>
  rpt conj_tac >> rpt gen_tac >>
  simp[vyperContextTheory.evaluate_code_source_def,
       vyperValueOperationTheory.evaluate_membership_def, AllCaseEqs()]
QED

Theorem source_convert_excludes_create_error[local]:
  !env v ty. evaluate_convert env v ty <>
    INR (RuntimeError "create outcome accounts")
Proof
  rpt gen_tac >>
  simp[oneline vyperValueOperationTheory.evaluate_convert_def,
       vyperValueOperationTheory.bounded_decimal_op_def, AllCaseEqs()]
QED

Theorem source_convert_from_excludes_create_error[local]:
  !env from_ty v ty. evaluate_convert_from env from_ty v ty <>
    INR (RuntimeError "create outcome accounts")
Proof
  rpt gen_tac >>
  simp[vyperValueOperationTheory.evaluate_convert_from_def,
       source_convert_excludes_create_error, AllCaseEqs()]
QED

Theorem source_extract32_excludes_create_error[local]:
  !bs n bt. evaluate_extract32 bs n bt <>
    INR (RuntimeError "create outcome accounts")
Proof
  rpt gen_tac >>
  simp[vyperContextTheory.evaluate_extract32_def,
       source_convert_excludes_create_error, AllCaseEqs()]
QED

val source_type_builtin_eq = oneline vyperContextTheory.evaluate_type_builtin_def;

Theorem source_type_pure_exclusions[local]:
  (!env ty bs. evaluate_abi_decode env ty bs <> INR "create outcome accounts") ==>
  !cx tb typ tys vs. evaluate_type_builtin cx tb typ tys vs <>
    INR (RuntimeError "create outcome accounts")
Proof
  strip_tac >> rpt gen_tac >> Cases_on `tb` >>
  simp[source_type_builtin_eq,
       source_convert_from_excludes_create_error,
       source_extract32_excludes_create_error,
       oneline vyperValueOperationTheory.evaluate_max_value_def,
       oneline vyperValueOperationTheory.evaluate_min_value_def,
       vyperABITheory.evaluate_abi_encode_bytes_def, AllCaseEqs()]
QED

Theorem source_abi_decode_excludes_create_error[local]:
  !env ty bs. evaluate_abi_decode env ty bs <> INR "create outcome accounts"
Proof
  simp[vyperABITheory.evaluate_abi_decode_def,
       vyperABITheory.decode_abi_value_def, AllCaseEqs()]
QED

(* Parser abbreviation only: no additional semantic constant. *)
val _ = overload_on ("source_exhausted_safe",
  ``\f. !s r t. accounts_runtime_well_typed s.accounts /\
       s.outcomes = SOME [] /\ f s = (r,t) ==>
       accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
       r <> INR (Error (RuntimeError "create outcome accounts"))``);

Theorem source_exhausted_bind_safety[local]:
  source_exhausted_safe f /\
  (!s v t. f s = (INL v,t) ==> source_exhausted_safe (g v)) ==>
  source_exhausted_safe (bind f g)
Proof
  simp_tac bool_ss [] >> ntac 2 strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp_tac bool_ss [vyperStateTheory.bind_def] >>
  Cases_on `f s` >> rename1 `f s = (a,u)` >>
  qpat_x_assum `source_exhausted_safe f`
    (qspecl_then [`s`, `a`, `u`] mp_tac) >>
  simp[] >> strip_tac >> Cases_on `a` >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`s`, `x`, `u`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`u`, `r`, `t`] mp_tac) >> simp[]
QED

Theorem source_exhausted_try_guarded_safety[local]:
  source_exhausted_safe f /\
  (!s e t. f s = (INR e,t) /\
     e <> Error (RuntimeError "create outcome accounts") ==>
     source_exhausted_safe (h e)) ==>
  source_exhausted_safe (try f h)
Proof
  simp_tac bool_ss [] >> ntac 2 strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `try _ _ _ = _` mp_tac >>
  simp_tac bool_ss [vyperStateTheory.try_def] >>
  Cases_on `f s` >> rename1 `f s = (a,u)` >>
  qpat_x_assum `source_exhausted_safe f`
    (qspecl_then [`s`, `a`, `u`] mp_tac) >>
  simp[] >> strip_tac >> Cases_on `a` >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`s`, `y`, `u`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`u`, `r`, `t`] mp_tac) >> simp[]
QED

Theorem source_exhausted_finally_safety[local]:
  source_exhausted_safe f /\ source_exhausted_safe g ==>
  source_exhausted_safe (finally f g)
Proof
  simp_tac bool_ss [] >> ntac 2 strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp_tac bool_ss [vyperStateTheory.finally_def] >>
  Cases_on `f s` >> rename1 `f s = (a,u)` >>
  qpat_x_assum `source_exhausted_safe f`
    (qspecl_then [`s`, `a`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `source_exhausted_safe g` (qspec_then `u` mp_tac) >>
  Cases_on `g u` >> rename1 `g u = (b,w)` >>
  disch_then (qspecl_then [`b`, `w`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `a` >> Cases_on `b` >>
  simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  strip_tac >> gvs[]
QED

Theorem source_exhausted_finally_unless_halt_safety[local]:
  source_exhausted_safe f /\ source_exhausted_safe g ==>
  source_exhausted_safe (finally_unless_halt f g)
Proof
  simp_tac bool_ss [] >> ntac 2 strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `finally_unless_halt _ _ _ = _` mp_tac >>
  simp_tac bool_ss [vyperStateTheory.finally_unless_halt_def] >>
  Cases_on `f s` >> rename1 `f s = (a,u)` >>
  qpat_x_assum `source_exhausted_safe f`
    (qspecl_then [`s`, `a`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `source_exhausted_safe g` (qspec_then `u` mp_tac) >>
  Cases_on `g u` >> rename1 `g u = (b,w)` >>
  disch_then (qspecl_then [`b`, `w`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `a` >> Cases_on `b` >>
  simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  rpt (CASE_TAC >> gvs[]) >> strip_tac >> gvs[]
QED

(* Select only the computation in the expanded parser abbreviation. *)
fun exhausted_computation tm =
  let val body = snd (strip_forall tm)
      val pre = fst (dest_imp body)
      val equation = List.last (strip_conj pre)
  in rator (lhs equation) end;

fun exhausted_at c = STRIP_QUANT_CONV
  (LAND_CONV (RAND_CONV (RAND_CONV (LAND_CONV (RATOR_CONV c)))));

Theorem source_exhausted_new_variable_safety[local]:
  !id tv v. source_exhausted_safe (new_variable id tv v)
Proof
  rpt gen_tac >> strip_tac >>
  drule vyperTypeStatePreservationTheory.new_variable_accounts >> strip_tac >>
  `t.outcomes = s.outcomes` by
    (qspecl_then [`s`, `s.outcomes`] mp_tac
       (Q.INST [`nm` |-> `id`, `ty` |-> `tv`] outcomes_replace_new_variable) >>
     simp[] >> disch_then (mp_tac o Q.AP_TERM `\st. st.outcomes`) >> simp[]) >>
  simp[] >>
  qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [vyperStateTheory.new_variable_def,
    vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
    vyperStateTheory.get_scopes_def, vyperStateTheory.type_check_def,
    vyperStateTheory.assert_def, vyperStateTheory.set_scopes_def,
    vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  Cases_on `lookup_scopes id s.scopes = NONE` >>
  Cases_on `s.scopes` >>
  simp[vyperStateTheory.return_def, vyperStateTheory.raise_def,
       vyperStateTheory.set_scopes_def] >> strip_tac >> gvs[]
QED

Theorem source_exhausted_scope_safety[local]:
  source_exhausted_safe push_scope /\
  source_exhausted_safe pop_scope /\
  (!nm tv v. source_exhausted_safe (push_scope_with_var nm tv v))
Proof
  conj_tac
  >- (rpt strip_tac >> gvs[vyperStateTheory.push_scope_def,
        vyperStateTheory.return_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `s.scopes` >>
      gvs[vyperStateTheory.pop_scope_def, vyperStateTheory.return_def,
          vyperStateTheory.raise_def]) >>
  rpt strip_tac >> gvs[vyperStateTheory.push_scope_with_var_def,
    vyperStateTheory.return_def]
QED

Theorem source_exhausted_array_iterator_safety[local]:
  !cx ty pv s r t.
    accounts_runtime_well_typed s.accounts /\ s.outcomes = SOME [] /\
    array_iterator_results cx ty pv s = (r,t) ==>
    accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
    r <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  drule array_iterator_results_state >> strip_tac >> gvs[] >>
  qpat_x_assum `array_iterator_results _ _ _ _ = _` mp_tac >>
  simp[oneline array_iterator_results_def,
       vyperStateTheory.eval_result_CASE_rator,
       vyperStateTheory.place_CASE_rator,
       vyperValueTheory.type_value_CASE_rator, vyperMiscTheory.option_CASE_rator,
       vyperASTTheory.bound_CASE_rator, AllCaseEqs(), LET_THM,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.check_def, vyperStateTheory.assert_def,
       vyperStateTheory.lift_option_type_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), vyperStateTheory.return_def, vyperStateTheory.raise_def,
      LET_THM] >>
  metis_tac[source_exhausted_length_safety,
            source_exhausted_read_result_safety]
QED

Theorem source_exhausted_return_safety[local]:
  !x. source_exhausted_safe (return x)
Proof
  rpt strip_tac >> gvs[vyperStateTheory.return_def]
QED

Theorem source_exhausted_internal_call_safety:
  (!cx nr view. source_exhausted_safe (lock_if_nr cx nr view)) /\
  (!cx nr view. source_exhausted_safe (unlock_if_nr cx nr view)) /\
  (!fn sc cx. source_exhausted_safe (push_function fn sc cx)) /\
  (!prev. source_exhausted_safe (pop_function prev))
Proof
  rpt conj_tac
  >- (rpt gen_tac >> Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
      Cases_on `view` >>
      simp[lock_if_nr_def, acquire_nonreentrant_lock_def,
        vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
        vyperStateTheory.record_storage_event_def,
        vyperStateTheory.get_transient_storage_def,
        vyperStateTheory.update_transient_def, vyperStateTheory.check_not_static_def,
        vyperStateTheory.check_def, vyperStateTheory.assert_def,
        vyperStateTheory.return_def, vyperStateTheory.raise_def,
        AllCaseEqs()] >> rpt strip_tac >>
      gvs[COND_RATOR, AllCaseEqs(), vyperStateTheory.raise_def,
        vyperStateTheory.return_def, vyperStateTheory.update_transient_def])
  >- (rpt gen_tac >> Cases_on `nr` >> Cases_on `view` >>
      Cases_on `cx.nonreentrant_slot` >>
      simp[unlock_if_nr_def, release_nonreentrant_lock_def,
        vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
        vyperStateTheory.record_storage_event_def,
        vyperStateTheory.get_transient_storage_def,
        vyperStateTheory.update_transient_def,
        vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
      rpt strip_tac >> gvs[])
  >- (rpt strip_tac >> gvs[push_function_def, vyperStateTheory.return_def]) >>
  rpt strip_tac >> gvs[pop_function_def, vyperStateTheory.set_scopes_def,
    vyperStateTheory.return_def]
QED

val exhausted_safety_leaves =
  CONJUNCTS source_exhausted_internal_call_safety @
  [source_exhausted_return_safety, source_exhausted_array_iterator_safety] @
  CONJUNCTS source_exhausted_scope_safety @
  [source_exhausted_new_variable_safety] @
  CONJUNCTS source_exhausted_place_safety @
  CONJUNCTS source_exhausted_effect_safety;
val exhausted_safety_rules =
  [source_exhausted_bind_safety, source_exhausted_try_guarded_safety,
   source_exhausted_finally_safety, source_exhausted_finally_unless_halt_safety];
val exhausted_safety_net = List.foldl (fn ((tm,tac),net) => Net.insert (tm,tac) net)
  Net.empty
  (map (fn th => (exhausted_computation (concl th), MATCH_ACCEPT_TAC th))
      exhausted_safety_leaves @
   map (fn th => (exhausted_computation (snd (dest_imp (concl (BETA_RULE th)))),
      MATCH_MP_TAC (BETA_RULE th) >> conj_tac)) exhausted_safety_rules);

val exhausted_safety_pattern = ``source_exhausted_safe f``;
fun is_exhausted_safety tm = can (match_term exhausted_safety_pattern) tm;

fun EXHAUSTED_IH_TAC (asl,w) =
  let
    fun terminal tm =
      if is_exhausted_safety tm then tm
      else if is_forall tm then terminal (snd (dest_forall tm))
      else terminal (snd (dest_imp tm))
    val candidates = List.mapPartial
      (total (fn a => PART_MATCH terminal (ASSUME a) w)) asl
    fun close th = POP_ASSUM_LIST (fn facts =>
      map_every assume_tac (List.filter (is_eq o concl) facts) >>
      metis_tac [th])
  in FIRST (first_assum MATCH_ACCEPT_TAC :: map close candidates) (asl,w) end;

Theorem exhausted_truth_wrapper[local]:
  !p. p = (p = T)
Proof
  simp[]
QED

fun exhausted_wrap_conv tm =
  if is_exhausted_safety tm then REWR_CONV exhausted_truth_wrapper tm
  else if is_forall tm then BINDER_CONV exhausted_wrap_conv tm
  else if is_imp tm then RAND_CONV exhausted_wrap_conv tm
  else ALL_CONV tm;

fun EXHAUSTED_RECURSIVE_TAC (g as (asl,w)) =
  let val name = fst (dest_const (fst (strip_comb (exhausted_computation w))))
  in if List.exists (fn n => n = name)
    ["eval_stmt", "eval_stmts", "eval_iterator", "eval_for", "eval_expr",
     "eval_exprs", "eval_base_place", "eval_target_place", "assign_tuple_targets",
     "assign_tuple_target_list", "eval_expr_results"]
    then (RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] o
        CONV_RULE exhausted_wrap_conv o
          SIMP_RULE bool_ss (vyperStateTheory.return_def ::
            map ASSUME (List.filter (fn a => not (is_forall a) andalso not (is_eq a)) asl))) >>
      CONV_TAC exhausted_wrap_conv >>
      pure_rewrite_tac [GSYM AND_IMP_INTRO] >>
      evalWalkLib.IH_TAC {stop = K false, normalise = I}) g
    else NO_TAC g
  end;

fun EXHAUSTED_SAFETY_STEP g = FIRST
  [first_assum MATCH_ACCEPT_TAC,
   (fn goal as (_,w) => FIRST
      (Net.match (exhausted_computation w) exhausted_safety_net) goal),
   EXHAUSTED_RECURSIVE_TAC,
   CONV_TAC (exhausted_at (CHANGED_CONV evalWalkLib.head_conv)),
   CONV_TAC (exhausted_at (evalWalkLib.unfold_conv
     [vyperStateTheory.ignore_bind_def, switch_BoolV_def,
      vyperStateTheory.type_check_def, vyperStateTheory.check_def,
      vyperStateTheory.assert_def, handle_loop_exception_def, handle_function_def,
      vyperStateTheory.lift_option_type_def, vyperStateTheory.lift_option_def,
      vyperStateTheory.lift_sum_def])),
   (fn (asl,w) => CHANGED_TAC (simp_tac (srw_ss())
     ([vyperStateTheory.return_def, vyperStateTheory.raise_def,
       source_binop_excludes_create_error] @
      map ASSUME (List.filter (fn tm => is_eq tm orelse
        (is_neg tm andalso is_eq (dest_neg tm))) asl))) (asl,w)),
   (fn goal as (_,w) =>
     let val c = exhausted_computation w in
       if TypeBase.is_case c orelse is_cond c
       then evalWalkLib.HEAD_CASE_TAC goal else NO_TAC goal end),
   gen_tac, DISCH_THEN STRIP_ASSUME_TAC,
   (fn goal as (_,w) => if is_forall w orelse is_imp w then NO_TAC goal
     else (POP_ASSUM_LIST (fn facts =>
       map_every assume_tac (List.filter (fn th => not (is_forall (concl th))) facts)) >>
       CHANGED_TAC (gvs[vyperStateTheory.get_scopes_def,
         vyperStateTheory.set_scopes_def, vyperStateTheory.get_accounts_def,
         vyperStateTheory.update_pending_deletions_def,
         vyperStateTheory.assert_def, vyperStateTheory.return_def,
         vyperStateTheory.raise_def, AllCaseEqs()])) goal)] g;

fun EXHAUSTED_HEAD_STEP g = FIRST
  [first_assum MATCH_ACCEPT_TAC,
   (fn goal as (_,w) =>
      if List.exists (fn n => n = fst (dest_const
           (fst (strip_comb (exhausted_computation w)))))
           ["raise", "assert", "get_scopes", "set_scopes", "get_accounts"]
      then (POP_ASSUM_LIST (fn facts =>
        map_every assume_tac (List.filter (fn th => not (is_forall (concl th))) facts)) >>
        simp[vyperStateTheory.raise_def, vyperStateTheory.assert_def,
          vyperStateTheory.return_def, vyperStateTheory.get_scopes_def,
          vyperStateTheory.set_scopes_def, vyperStateTheory.get_accounts_def,
          AllCaseEqs()] >> NO_TAC) goal
      else NO_TAC goal),
   (fn goal as (_,w) => FIRST
      (Net.match (exhausted_computation w) exhausted_safety_net) goal),
   EXHAUSTED_RECURSIVE_TAC,
   CONV_TAC (exhausted_at (CHANGED_CONV
     (REPEATC (CHANGED_CONV evalWalkLib.head_conv)))),
   CONV_TAC (exhausted_at (evalWalkLib.unfold_conv
     [vyperStateTheory.ignore_bind_def, vyperStateTheory.type_check_def,
      vyperStateTheory.check_def, vyperStateTheory.assert_def,
      oneline handle_function_def, vyperStateTheory.lift_option_type_def,
      vyperStateTheory.lift_option_def, vyperStateTheory.lift_sum_def])),
   (fn goal as (_,w) =>
     let val c = exhausted_computation w in
       if TypeBase.is_case c orelse is_cond c
       then evalWalkLib.HEAD_CASE_TAC goal else NO_TAC goal end),
   gen_tac, DISCH_THEN STRIP_ASSUME_TAC] g;

Theorem source_exhausted_assert_reason_safety[local]:
  source_exhausted_safe f /\
  (!s v t. f s = (INL v,t) ==> source_exhausted_safe h) ==>
  source_exhausted_safe
    (bind f (\pv. switch_BoolV cx pv (return ())
      (bind h (\stv. bind (read_result cx stv) (\sv.
        bind (lift_option_type (dest_StringV sv) "not StringV")
          (\str. raise (AssertException str)))))))
Proof
  strip_tac >> MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `source_exhausted_safe h` by
    (first_x_assum drule >> simp[]) >>
  qpat_x_assum `!s v t. f s = _ ==> _` kall_tac >>
  CONV_TAC (exhausted_at (BETA_CONV THENC REWR_CONV switch_BoolV_def)) >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- MATCH_ACCEPT_TAC source_exhausted_read_result_safety >>
  rpt gen_tac >> strip_tac >>
  rpt EXHAUSTED_SAFETY_STEP
QED

Theorem source_exhausted_eval_safety_mutual:
  (!cx stmt. source_exhausted_safe (eval_stmt cx stmt)) /\
  (!cx stmts. source_exhausted_safe (eval_stmts cx stmts)) /\
  (!cx it. source_exhausted_safe (eval_iterator cx it)) /\
  (!cx tyv id fbody vs. source_exhausted_safe (eval_for cx tyv id fbody vs)) /\
  (!cx e. source_exhausted_safe (eval_expr cx e)) /\
  (!cx es. source_exhausted_safe (eval_exprs cx es)) /\
  (!cx t. source_exhausted_safe (eval_base_place cx t)) /\
  (!cx t. source_exhausted_safe (eval_target_place cx t)) /\
  (!cx g v. source_exhausted_safe (assign_tuple_targets cx g v)) /\
  (!cx gs vs. source_exhausted_safe (assign_tuple_target_list cx gs vs)) /\
  (!cx es. source_exhausted_safe (eval_expr_results cx es))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac
  >- suspend "c01" >- suspend "c02" >- suspend "c03"
  >- suspend "c04" >- suspend "c05" >- suspend "c06"
  >- suspend "c07" >- suspend "c08" >- suspend "c09"
  >- suspend "c10" >- suspend "c11" >- suspend "c12"
  >- suspend "c13" >- suspend "c14" >- suspend "c15"
  >- suspend "c16" >- suspend "c17" >- suspend "c18"
  >- suspend "c19" >- suspend "c20" >- suspend "c21"
  >- suspend "c22" >- suspend "c23" >- suspend "c24"
  >- suspend "c25" >- suspend "c26" >- suspend "c27"
  >- suspend "c28" >- suspend "c29" >- suspend "c30"
  >- suspend "c31" >- suspend "c32" >- suspend "c33"
  >- suspend "c34" >- suspend "c35" >- suspend "c36"
  >- suspend "c37" >- suspend "c38" >- suspend "c39"
  >- suspend "c40" >- suspend "c41" >- suspend "c42"
  >- suspend "c43" >- suspend "c44" >- suspend "c45"
  >- suspend "c46" >- suspend "c47" >- suspend "c48"
  >- suspend "c49" >- suspend "c50" >- suspend "c51"
  >- suspend "c52" >- suspend "c53" >- suspend "c54"
  >- suspend "c55" >- suspend "c56" >- suspend "c57"
  >- suspend "c58" >- suspend "c59" >- suspend "c60"
  >- suspend "c61" >- suspend "c62" >> suspend "c63"
QED

fun exhausted_conclusion_conv c tm =
  if can exhausted_computation tm then exhausted_at c tm
  else if is_forall tm then QUANT_CONV (exhausted_conclusion_conv c) tm
  else RAND_CONV (exhausted_conclusion_conv c) tm;

val EXHAUSTED_CONSTRUCTOR_TAC =
  CONV_TAC (exhausted_conclusion_conv
    (evalWalkLib.unfold_conv [evaluate_def])) >> rpt EXHAUSTED_SAFETY_STEP;

Resume source_exhausted_eval_safety_mutual[c01]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c02]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c03]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c04]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c05]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c06]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c07]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c08]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c09]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c10]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c11]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c12]:
  ntac 3 gen_tac >> strip_tac >>
  CONV_TAC (exhausted_at (REWR_CONV (cj 12 evaluate_def))) >>
  BETA_TAC >> MATCH_MP_TAC (BETA_RULE source_exhausted_assert_reason_safety) >>
  conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
Resume source_exhausted_eval_safety_mutual[c13]:
  ntac 3 gen_tac >> strip_tac >>
  CONV_TAC (exhausted_at (REWR_CONV (cj 13 evaluate_def))) >>
  EXHAUSTED_SAFETY_STEP >- first_assum MATCH_ACCEPT_TAC >>
  ntac 3 gen_tac >> strip_tac >>
  CONV_TAC (exhausted_at (BETA_CONV THENC REWR_CONV switch_BoolV_def)) >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- MATCH_ACCEPT_TAC source_exhausted_read_result_safety >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  Cases_on `v' = BoolV T` >- simp[vyperStateTheory.return_def] >>
  Cases_on `v' = BoolV F`
  >- (asm_rewrite_tac [] >> Cases_on `err` >>
      rename1 `CustomError id positional kwargs` >>
      CONV_TAC (exhausted_at evalWalkLib.head_conv) >>
      Cases_on `get_module_code cx (FST id)`
      >- gvs[vyperStateTheory.raise_def] >>
      rename1 `get_module_code cx (FST id) = SOME tops` >>
      Cases_on `lookup_custom_error_args_in (SND id) tops`
      >- gvs[vyperStateTheory.raise_def] >>
      rename1 `lookup_custom_error_args_in (SND id) tops = SOME params` >>
      Cases_on `order_custom_error_args params (CustomError id positional kwargs)`
      >- gvs[vyperStateTheory.raise_def] >>
      gvs[] >> rpt EXHAUSTED_SAFETY_STEP) >>
  simp[vyperStateTheory.raise_def]
QED
Resume source_exhausted_eval_safety_mutual[c14]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c15]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c16]:
  ntac 3 gen_tac >> strip_tac >>
  CONV_TAC (exhausted_at (REWR_CONV (cj 16 evaluate_def))) >>
  rpt EXHAUSTED_SAFETY_STEP
QED
Resume source_exhausted_eval_safety_mutual[c17]:
  ntac 3 gen_tac >> strip_tac >>
  CONV_TAC (exhausted_at (REWR_CONV (cj 17 evaluate_def))) >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- MATCH_ACCEPT_TAC source_exhausted_read_result_safety >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- ((metis_tac[])) >>
  rpt EXHAUSTED_SAFETY_STEP
QED
Resume source_exhausted_eval_safety_mutual[c18]:
  ntac 3 gen_tac >> strip_tac >>
  CONV_TAC (exhausted_at (REWR_CONV (cj 18 evaluate_def))) >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- MATCH_ACCEPT_TAC source_exhausted_read_result_safety >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >> metis_tac[]
QED
Resume source_exhausted_eval_safety_mutual[c19]:
  ntac 5 gen_tac >> strip_tac >>
  CONV_TAC (exhausted_at (REWR_CONV (cj 19 evaluate_def))) >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- MATCH_ACCEPT_TAC source_exhausted_read_place_safety >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- rpt EXHAUSTED_SAFETY_STEP >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- metis_tac[] >>
  qpat_x_assum `!s p t s' cur t' s'' ptv t''. _` kall_tac >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  rpt EXHAUSTED_SAFETY_STEP >> metis_tac[source_binop_excludes_create_error]
QED
Resume source_exhausted_eval_safety_mutual[c20]:
  ntac 4 gen_tac >> strip_tac >>
  CONV_TAC (exhausted_at (REWR_CONV (cj 20 evaluate_def))) >>
  EXHAUSTED_SAFETY_STEP >- first_assum MATCH_ACCEPT_TAC >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  CONV_TAC (exhausted_at (REWR_CONV vyperStateTheory.ignore_bind_def)) >>
  EXHAUSTED_SAFETY_STEP >- MATCH_ACCEPT_TAC (cj 1 source_exhausted_scope_safety) >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_finally_safety) >> reverse conj_tac
  >- MATCH_ACCEPT_TAC (cj 2 source_exhausted_scope_safety) >>
  CONV_TAC (exhausted_at (REWR_CONV switch_BoolV_def)) >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- MATCH_ACCEPT_TAC source_exhausted_read_result_safety >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  Cases_on `v'' = BoolV T` >- (asm_rewrite_tac [] >> EXHAUSTED_IH_TAC) >>
  Cases_on `v'' = BoolV F` >- (asm_rewrite_tac [] >> EXHAUSTED_IH_TAC) >>
  asm_rewrite_tac [] >> POP_ASSUM_LIST (K all_tac) >>
  simp[vyperStateTheory.raise_def]
QED
Resume source_exhausted_eval_safety_mutual[c21]:
  ntac 6 gen_tac >> strip_tac >>
  CONV_TAC (exhausted_at (REWR_CONV (cj 21 evaluate_def))) >>
  CONV_TAC (exhausted_at (evalWalkLib.head_conv THENC BETA_CONV)) >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- rpt EXHAUSTED_SAFETY_STEP >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- EXHAUSTED_IH_TAC >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  CONV_TAC (exhausted_at (REWR_CONV vyperStateTheory.ignore_bind_def)) >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- (POP_ASSUM_LIST (K all_tac) >>
      simp[vyperStateTheory.check_def, vyperStateTheory.assert_def,
           vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
      Cases_on `compatible_bound (Dynamic n) (LENGTH v')` >> simp[]) >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >> EXHAUSTED_IH_TAC
QED
Resume source_exhausted_eval_safety_mutual[c22]:
  EXHAUSTED_CONSTRUCTOR_TAC >>
  qpat_x_assum `source_exhausted_safe _` kall_tac >>
  gvs[vyperStateTheory.assert_def, AllCaseEqs()]
QED
Resume source_exhausted_eval_safety_mutual[c23]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c24]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c25]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c26]:
  EXHAUSTED_CONSTRUCTOR_TAC >>
  qpat_x_assum `get_range_limits _ _ = _` mp_tac >>
  simp[oneline get_range_limits_def, AllCaseEqs()]
QED
Resume source_exhausted_eval_safety_mutual[c27]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c28]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c29]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c30]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c31]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c32]:
  ntac 5 gen_tac >> strip_tac >>
  CONV_TAC (exhausted_at (REWR_CONV (cj 32 evaluate_def))) >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  `source_exhausted_safe (eval_expr cx e')` by metis_tac[] >>
  `source_exhausted_safe (eval_expr cx e'')` by metis_tac[] >>
  qpat_x_assum `!s tv t. _ ==> source_exhausted_safe (eval_expr cx e')` kall_tac >>
  qpat_x_assum `!s tv t. _ ==> source_exhausted_safe (eval_expr cx e'')` kall_tac >>
  rpt EXHAUSTED_SAFETY_STEP
QED
Resume source_exhausted_eval_safety_mutual[c33]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c34]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c35]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c36]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c37]:
  ntac 4 gen_tac >> strip_tac >>
  CONV_TAC (exhausted_at (REWR_CONV (cj 37 evaluate_def) THENC
    REWR_CONV vyperStateTheory.ignore_bind_def)) >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- (POP_ASSUM_LIST (K all_tac) >> rpt EXHAUSTED_SAFETY_STEP) >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  Cases_on `bt = Len` >- (asm_rewrite_tac [] >> rpt EXHAUSTED_SAFETY_STEP) >>
  Cases_on `bt = Bop In \/ bt = Bop NotIn`
  >- (asm_rewrite_tac [] >>
      `source_exhausted_safe (eval_exprs cx es)` by
        (qpat_x_assum `!s x t. _ /\ _ /\ (bt = Bop In \/ bt = Bop NotIn) ==> _`
           mp_tac >> metis_tac[]) >>
      POP_ASSUM_LIST (fn facts => map_every assume_tac
        (List.filter (fn th => not (is_forall (concl th)) orelse
          is_exhausted_safety (concl th)) facts)) >>
      rpt EXHAUSTED_SAFETY_STEP >>
      metis_tac[MP source_ordinary_pure_exclusions source_binop_excludes_create_error]) >>
  Cases_on `bt = Env MsgGas`
  >- (asm_rewrite_tac [] >> rpt EXHAUSTED_SAFETY_STEP >>
      gvs[next_gas_reading_def, vyperStateTheory.raise_def,
          vyperStateTheory.return_def, AllCaseEqs()]) >>
  Cases_on `code_slice_source bt es`
  >- (asm_rewrite_tac [] >>
      `source_exhausted_safe (eval_exprs cx es)` by
        (qpat_x_assum `!s x t. _ /\ _ /\ _ /\ _ /\ NONE = NONE ==> _`
          mp_tac >> metis_tac[]) >>
      POP_ASSUM_LIST (fn facts => map_every assume_tac
        (List.filter (fn th => not (is_forall (concl th)) orelse
          is_exhausted_safety (concl th)) facts)) >>
      rpt EXHAUSTED_SAFETY_STEP >>
      gvs[MP source_ordinary_pure_exclusions source_binop_excludes_create_error] >>
      gvs[precompile_call_success_def, vyperStateTheory.check_def,
          vyperStateTheory.assert_def, vyperStateTheory.return_def,
          vyperStateTheory.raise_def, AllCaseEqs()]) >>
  PairCases_on `x` >>
  `source_exhausted_safe (eval_exprs cx (TL es))` by
    (qpat_x_assum `!s x t v code_ty addr. _ ==> _` mp_tac >> metis_tac[]) >>
  qpat_x_assum `!s x t v code_ty addr. _ ==> source_exhausted_safe (eval_exprs cx (TL es))` kall_tac >>
  qpat_x_assum `!s x t. _ ==> source_exhausted_safe (eval_exprs cx es)` kall_tac >>
  qpat_x_assum `!s x t. _ ==> source_exhausted_safe (eval_exprs cx es)` kall_tac >>
  qpat_x_assum `!s x t. _ ==> source_exhausted_safe (eval_expr cx (HD es))` kall_tac >>
  `!u vs w. eval_exprs cx (TL es) u = (INL vs,w) ==>
     source_exhausted_safe (eval_exprs cx [x1])` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!s x t v code_ty addr u vs w. _ ==> _` mp_tac >> metis_tac[]) >>
  qpat_x_assum `!s x t v code_ty addr u vs w. _ ==> _` kall_tac >>
  asm_rewrite_tac [] >> rpt EXHAUSTED_SAFETY_STEP >>
  gvs[MP source_ordinary_pure_exclusions source_binop_excludes_create_error,
      precompile_call_success_def, vyperStateTheory.check_def,
      vyperStateTheory.assert_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, AllCaseEqs()]
QED
Resume source_exhausted_eval_safety_mutual[c38]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c39]:
  EXHAUSTED_CONSTRUCTOR_TAC >>
  gvs[MP source_type_pure_exclusions source_abi_decode_excludes_create_error]
QED
Resume source_exhausted_eval_safety_mutual[c40]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c41]:
  rpt gen_tac >> strip_tac >>
  CONV_TAC (exhausted_at (REWR_CONV (cj 41 evaluate_def))) >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  `source_exhausted_safe (eval_exprs cx (TAKE (LENGTH (FST (SND sig))) (DROP 1 es)))` by
    (qpat_x_assum `!s target t nargs. _ ==> _` mp_tac >> metis_tac[]) >>
  qpat_x_assum `!s target t nargs. _ ==> _` kall_tac >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  `source_exhausted_safe (eval_exprs cx (DROP (1 + LENGTH (FST (SND sig))) es))` by
    (qpat_x_assum `!s target t nargs u vs w. _ ==> _` mp_tac >> metis_tac[]) >>
  qpat_x_assum `!s target t nargs u vs w. _ ==> _` kall_tac >>
  rpt EXHAUSTED_SAFETY_STEP
QED
Resume source_exhausted_eval_safety_mutual[c42]:
  rpt gen_tac >> strip_tac >>
  CONV_TAC (exhausted_at (REWR_CONV (cj 42 evaluate_def))) >>
  CONV_TAC (exhausted_at (REWR_CONV vyperStateTheory.ignore_bind_def)) >>
  MATCH_MP_TAC (BETA_RULE source_exhausted_bind_safety) >> conj_tac
  >- (POP_ASSUM_LIST (K all_tac) >> rpt EXHAUSTED_SAFETY_STEP) >>
  ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss []) >>
  rpt EXHAUSTED_HEAD_STEP
QED
Resume source_exhausted_eval_safety_mutual[c43]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c44]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c45]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c46]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c47]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c48]:
  rpt gen_tac >> strip_tac >> Cases_on `kind` >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [create_kind_distinct,
    GSYM create_kind_distinct, create_kind_11]) >>
  CONV_TAC (exhausted_conclusion_conv
    (evalWalkLib.unfold_conv [evaluate_def])) >> rpt EXHAUSTED_HEAD_STEP >>
  gvs[vyperCreateTheory.check_create_blueprint_def,
    vyperStateTheory.bind_def, vyperStateTheory.get_accounts_def,
    vyperStateTheory.return_def, vyperStateTheory.raise_def,
    vyperStateTheory.lift_option_def, vyperMiscTheory.option_CASE_rator,
    AllCaseEqs()]
QED
Resume source_exhausted_eval_safety_mutual[c49]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c50]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c51]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c52]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c53]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c54]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c55]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c56]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c57]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c58]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c59]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c60]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c61]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c62]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Resume source_exhausted_eval_safety_mutual[c63]:
  EXHAUSTED_CONSTRUCTOR_TAC
QED
Finalise source_exhausted_eval_safety_mutual

Theorem source_replay_cleanup_scopes[local]:
  (!cx tv ss1 ss2 s r t.
    s.scopes <> [] /\
    switch_BoolV cx tv (eval_stmts cx ss1) (eval_stmts cx ss2) s = (r,t) ==>
    t.scopes <> []) /\
  (!cx body s r t.
    s.scopes <> [] /\
    (do eval_stmts cx body; return F od) s = (r,t) ==>
    t.scopes <> []) /\
  (!cx body s r t.
    s.scopes <> [] /\
    (try (do eval_stmts cx body; return F od) handle_loop_exception) s = (r,t) ==>
    t.scopes <> [])
Proof
  conj_tac
  >- (rpt strip_tac >>
      gvs[switch_BoolV_def, vyperStateTheory.bind_def,
          COND_RATOR, vyperStateTheory.raise_def, AllCaseEqs()] >>
      imp_res_tac vyperScopePreservationTheory.read_result_scopes >>
      imp_res_tac eval_stmts_preserves_scopes_len >>
      metis_tac[LENGTH_NIL]) >>
  conj_tac >> rpt strip_tac >>
  gvs[vyperStateTheory.try_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.bind_def, vyperStateTheory.return_def,
      handle_loop_exception_def, COND_RATOR,
      vyperStateTheory.raise_def, AllCaseEqs()] >>
  imp_res_tac eval_stmts_preserves_scopes_len >>
  gvs[] >> metis_tac[LENGTH_NIL]
QED

Theorem source_replay_cut_bind_reachable:
  !f g s os.
    source_wrapper_cut_at f s os /\
    (!v u pre.
      f (s with outcomes := SOME (os ++ [probe_failed_outcome])) = (INL v,u) /\
      u.outcomes = SOME (pre ++ [probe_failed_outcome]) ==>
      source_wrapper_cut_at (g v) u pre) /\
    (!v. outcomes_suffix (g v) /\ storage_trace_frame (g v) /\
         source_exhausted_safe (g v)) ==>
    source_wrapper_cut_at (bind f g) s os
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `f (s with outcomes := SOME (os ++ [probe_failed_outcome]))` >>
  rename1 `f (s with outcomes := SOME (os ++ [probe_failed_outcome])) = (rf,sf)` >>
  qpat_x_assum `!r t. (rf,sf) = (r,t) ==> _`
    (qspecl_then [`rf`,`sf`] mp_tac) >> simp_tac bool_ss [] >> strip_tac
  >- suspend "unconsumed"
  >- suspend "ordinary"
  >> suspend "create"
QED

Resume source_replay_cut_bind_reachable[unconsumed]:
  reverse (Cases_on `rf`)
  >- (gvs[vyperStateTheory.bind_def] >> disj1_tac >>
      qexists_tac `pre` >> simp[vyperStateTheory.bind_def]) >>
  gvs[vyperStateTheory.bind_def] >>
  qpat_assum `!tail. f _ = _`
    (qspec_then `[]` (fn th => rewrite_tac[REWRITE_RULE [APPEND_NIL] th])) >>
  gvs[]
QED

Resume source_replay_cut_bind_reachable[ordinary]:
  disj2_tac >> disj1_tac >> conj_tac
  >- (Cases_on `rf` >> gvs[vyperStateTheory.bind_def] >>
      rename1 `g v sf = (r,t)` >>
      qpat_x_assum `!v. outcomes_suffix (g v) /\ _`
        (qspec_then `v` mp_tac) >>
      simp[outcomes_suffix_def] >> strip_tac >>
      qpat_x_assum `!st. outcome_suffix _ _`
        (qspec_then `sf` mp_tac) >> simp[outcome_suffix_def]) >>
  qpat_assum `bind f g _ = (r,t)` (fn th => rewrite_tac[GSYM th]) >>
  conj_tac >> irule source_replay_bind_transport >> simp[] >>
  qpat_x_assum `!v u pre. _` kall_tac >>
  qpat_x_assum `!v. _` kall_tac >> metis_tac[]
QED

Resume source_replay_cut_bind_reachable[create]:
  `r = INR (Error (RuntimeError "create outcome accounts")) /\ t = sf` by
    gvs[vyperStateTheory.bind_def] >>
  disj2_tac >> disj2_tac >> gvs[] >>
  conj_tac
  >- (Cases_on `f (s with outcomes := SOME (os ++ [empty_failed_outcome]))` >>
      rename1 `f (s with outcomes := SOME (os ++ [empty_failed_outcome])) = (re,se)` >>
      Cases_on `re` >> gvs[vyperStateTheory.bind_def] >>
      rename1 `g v se` >>
      qpat_x_assum `!v. outcomes_suffix (g v) /\ _`
        (qspec_then `v` strip_assume_tac) >>
      Cases_on `g v se` >>
      qpat_x_assum `source_exhausted_safe (g v)`
        (qspecl_then [`se`,`q`,`r`] mp_tac) >> simp[]) >>
  conj_tac
  >- simp[vyperStateTheory.bind_def] >>
  rpt gen_tac >>
  Cases_on `f (s with outcomes := SOME (os ++ [empty_failed_outcome]))` >>
  rename1 `f (s with outcomes := SOME (os ++ [empty_failed_outcome])) = (re,se)` >>
  reverse (Cases_on `re`) >> gvs[vyperStateTheory.bind_def]
  >- (rpt strip_tac >> gvs[]) >>
  strip_tac >>
  qpat_x_assum `!v. outcomes_suffix (g v) /\ _`
    (qspec_then `x` strip_assume_tac) >>
  qpat_x_assum `source_exhausted_safe (g x)`
    (qspecl_then [`se`,`q`,`u`] mp_tac) >> simp[]
QED
Finalise source_replay_cut_bind_reachable

Theorem source_take_request_residual[local]:
  !rq s oc rest r t.
    take_request_outcome rq (s with outcomes := SOME (oc::rest)) = (r,t) ==>
    t.outcomes = SOME rest
Proof
  rpt gen_tac >>
  simp[take_request_outcome_def] >>
  pairarg_tac >>
  mp_tac (Q.INST [`os` |-> `oc::rest`] take_outcome_rest) >>
  simp[] >> rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem source_take_request_bind_consumed[local]:
  !rq g s os r t.
    (!v. outcomes_frame (g v)) /\
    bind (take_request_outcome rq) g
      (s with outcomes := SOME (os ++ [probe_failed_outcome])) = (r,t) /\
    t.outcomes = SOME [] ==> os = []
Proof
  rpt gen_tac >> strip_tac >> Cases_on `os` >> simp[] >>
  gvs[vyperStateTheory.bind_def, AllCaseEqs()] >>
  drule source_take_request_residual >> strip_tac >>
  gvs[] >>
  qpat_x_assum `!v. outcomes_frame (g v)` (qspec_then `x` assume_tac) >>
  drule_all outcomes_frame_result >> simp[]
QED

Theorem source_take_call_bind_normal[local]:
  !addr data amount g s xs.
    bind (take_call_outcome addr data amount) g (s with outcomes := SOME xs) =
    bind (take_request_outcome (call_outcome_request addr data amount s)) g
      (s with outcomes := SOME xs)
Proof
  simp[vyperStateTheory.bind_def, take_call_outcome_def,
       call_outcome_request_def]
QED

Theorem source_send_oracle_normal[local]:
  !cx gas vs s xs.
    eval_send cx gas vs (s with outcomes := SOME xs) =
    case vs of
    | to_v::amount_v::gas_vs =>
      if LENGTH gas_vs <> (if gas then 1 else 0) then
        (INR (Error (TypeError "Send args")), s with outcomes := SOME xs)
      else (case dest_AddressV to_v of
      | NONE => (INR (Error (TypeError "Send not AddressV")), s with outcomes := SOME xs)
      | SOME addr => (case dest_NumV amount_v of
        | NONE => (INR (Error (TypeError "Send not NumV")), s with outcomes := SOME xs)
        | SOME amount =>
          if cx.txn.is_static /\ amount <> 0 then
            (INR (Error (RuntimeError "write in static context")), s with outcomes := SOME xs)
          else bind (take_call_outcome addr []
                       (if cx.txn.is_static then NONE else SOME amount))
                 (\(rq,oc). bind (check oc.co_success "send failed")
                   (\u. bind (adopt_call_outcome rq oc) (\v. return (Value NoneV))))
                 (s with outcomes := SOME xs)))
    | _ => (INR (Error (TypeError "Send args")), s with outcomes := SOME xs)
Proof
  rpt gen_tac >> Cases_on `vs`
  >- simp[eval_send_def, vyperStateTheory.raise_def] >>
  rename1 `h::tl` >> Cases_on `tl`
  >- simp[eval_send_def, vyperStateTheory.raise_def] >>
  Cases_on `dest_AddressV h` >> Cases_on `dest_NumV h'` >>
  Cases_on `cx.txn.is_static` >>
  simp[eval_send_def, frame_call_value_def,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.check_def, vyperStateTheory.lift_option_type_def,
       vyperStateTheory.raise_def, vyperStateTheory.return_def] >>
  rpt IF_CASES_TAC >> gvs[vyperStateTheory.raise_def] >>
  simp[vyperStateTheory.bind_def]
QED

Theorem source_ext_effects_oracle_normal[local]:
  !cx addr data amount gas accounts g s xs.
    bind (eval_ext_call_effects cx addr data amount gas accounts) g
      (s with outcomes := SOME xs) =
    bind (take_call_outcome addr data amount)
      (\(rq,oc). bind
        (if call_outcome_success oc then return ()
         else raise (Error (RevertData (call_outcome_return_data oc))))
        (\u. bind (adopt_call_outcome rq oc)
          (\v. g (call_outcome_return_data oc))))
      (s with outcomes := SOME xs)
Proof
  rpt gen_tac >>
  rewrite_tac[eval_ext_call_effects_def, vyperStateTheory.bind_assoc] >>
  simp[Once vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
  simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc,
       vyperStateTheory.bind_return] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, FORALL_PROD, vyperStateTheory.bind_assoc,
       vyperStateTheory.bind_return]
QED

Theorem source_ext_call_oracle_normal[local]:
  !cx static skip name tys ret opts vs s xs.
    eval_ext_call cx static skip (name,tys,ret) opts vs
      (s with outcomes := SOME xs) =
    case vs of
    | [] => (INR (Error (TypeError "ExtCall operands")), s with outcomes := SOME xs)
    | target::rest =>
      if ~(LENGTH rest = LENGTH tys + LENGTH opts /\ ext_call_opts_ok static opts) then
        (INR (Error (TypeError "ExtCall operands")), s with outcomes := SOME xs)
      else case dest_AddressV target of
      | NONE => (INR (Error (TypeError "ExtCall target not address")), s with outcomes := SOME xs)
      | SOME addr =>
        case (if static then SOME NONE else
          case ext_call_kwarg EKValue opts (DROP (LENGTH tys) rest) of
          | NONE => SOME (SOME 0)
          | SOME v => OPTION_MAP SOME (dest_NumV v)) of
        | NONE => (INR (Error (TypeError "ExtCall value not int")), s with outcomes := SOME xs)
        | SOME amount =>
          case build_ext_calldata (get_tenv cx) name tys (TAKE (LENGTH tys) rest) of
          | NONE => (INR (Error (TypeError "ExtCall build_calldata")), s with outcomes := SOME xs)
          | SOME data =>
            if ~ext_call_precheck_ok skip ret addr s.accounts then
              (INR (Error (RuntimeError "ExtCall target has no code")), s with outcomes := SOME xs)
            else if cx.txn.is_static /\ (case amount of NONE => F | SOME n => n <> 0) then
              (INR (Error (RuntimeError "write in static context")), s with outcomes := SOME xs)
            else bind (take_call_outcome addr data (if cx.txn.is_static then NONE else amount))
              (\(rq,oc). bind
                (if call_outcome_success oc then return ()
                 else raise (Error (RevertData (call_outcome_return_data oc))))
                (\u. bind (adopt_call_outcome rq oc) (\v.
                  case (if call_outcome_return_data oc = [] then
                    ext_call_kwarg EKDefault opts (DROP (LENGTH tys) rest) else NONE) of
                  | SOME d => bind get_accounts (\accounts.
                      bind (check (skip \/ ext_call_has_code addr accounts)
                        "ExtCall target has no code") (\u. return (Value d)))
                  | NONE => bind (lift_sum_runtime
                      (evaluate_abi_decode_return (get_tenv cx) ret (call_outcome_return_data oc)))
                      (\v. return (Value v)))))
              (s with outcomes := SOME xs)
Proof
  `!b ex. assert b ex = if b then return () else raise ex` by
    (rpt gen_tac >> Cases_on `b` >>
     simp[FUN_EQ_THM, vyperStateTheory.assert_def,
          vyperStateTheory.return_def, vyperStateTheory.raise_def]) >>
  rpt gen_tac >> Cases_on `vs`
  >- simp[eval_ext_call_def, vyperStateTheory.raise_def] >>
  Cases_on `LENGTH t = LENGTH tys + LENGTH opts /\ ext_call_opts_ok static opts` >>
  gvs[eval_ext_call_def, vyperStateTheory.type_check_def,
       vyperStateTheory.assert_def, Once vyperStateTheory.ignore_bind_def,
       Once vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, arithmeticTheory.ADD_COMM] >>
  Cases_on `dest_AddressV h` >>
  simp[vyperStateTheory.lift_option_type_def, vyperStateTheory.bind_return,
       Once vyperStateTheory.bind_def, vyperStateTheory.raise_def,
       vyperStateTheory.return_def] >>
  Cases_on `static` >> simp[vyperStateTheory.bind_return] >>
  Cases_on `ext_call_kwarg EKValue opts (DROP (LENGTH tys) t)` >>
  simp[vyperStateTheory.bind_return] >>
  Cases_on `dest_NumV (THE (ext_call_kwarg EKValue opts (DROP (LENGTH tys) t)))` >>
  gvs[vyperStateTheory.lift_option_type_def, vyperStateTheory.bind_return,
      vyperStateTheory.bind_assoc] >>
  Cases_on `build_ext_calldata (get_tenv cx) name tys (TAKE (LENGTH tys) t)` >>
  simp[vyperStateTheory.bind_return, Once vyperStateTheory.bind_def,
       vyperStateTheory.raise_def] >>
  simp[vyperStateTheory.return_def] >>
  simp[Once vyperStateTheory.bind_def, vyperStateTheory.get_accounts_def] >>
  simp[Once vyperStateTheory.ignore_bind_def, Once vyperStateTheory.bind_def,
       vyperStateTheory.check_def, vyperStateTheory.assert_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  Cases_on `cx.txn.is_static` >>
  simp[frame_call_value_def, vyperStateTheory.bind_return,
       vyperStateTheory.check_def, vyperStateTheory.assert_def,
       vyperStateTheory.ignore_bind_def] >>
  rpt (IF_CASES_TAC >> gvs[vyperStateTheory.bind_return]) >>
  simp[source_ext_effects_oracle_normal] >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.raise_def]
QED

Theorem source_raw_call_oracle_normal[local]:
  !cx flags addr data amount gas s xs.
    eval_raw_call cx flags addr data amount gas (s with outcomes := SOME xs) =
    if ~((~(flags.rcf_is_delegate /\ flags.rcf_is_static)) /\
         ((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0)) then
      (INR (Error (TypeError "raw_call flags/value")), s with outcomes := SOME xs)
    else if cx.txn.is_static /\ ~flags.rcf_is_static /\ amount <> 0 then
      (INR (Error (RuntimeError "write in static context")), s with outcomes := SOME xs)
    else bind (take_request_outcome
      (if flags.rcf_is_delegate then
        delegate_outcome_request addr data
          (if cx.txn.is_static \/ flags.rcf_is_static then NONE else SOME amount) s
       else call_outcome_request addr data
          (if cx.txn.is_static \/ flags.rcf_is_static then NONE else SOME amount) s))
      (\(rq,oc). bind (adopt_call_outcome rq oc) (\u.
        if flags.rcf_revert_on_failure then
          bind (if oc.co_success then return () else raise (Error (RevertData oc.co_returnData)))
            (\u. if flags.rcf_max_outsize = 0 then return (Value NoneV)
                 else return (Value (BytesV (TAKE flags.rcf_max_outsize oc.co_returnData))))
        else if flags.rcf_max_outsize = 0 then return (Value (BoolV oc.co_success))
        else return (Value (ArrayV (TupleV [BoolV oc.co_success;
                         BytesV (TAKE flags.rcf_max_outsize oc.co_returnData)])))))
      (s with outcomes := SOME xs)
Proof
  rpt gen_tac >>
  Cases_on `flags.rcf_is_delegate` >> Cases_on `flags.rcf_is_static` >>
  Cases_on `cx.txn.is_static` >>
  simp[eval_raw_call_def, frame_call_value_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.check_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_return, vyperStateTheory.bind_assoc] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, take_call_outcome_def,
       take_delegate_outcome_def, call_outcome_request_def,
       delegate_outcome_request_def, vyperStateTheory.assert_def] >>
  qmatch_goalsub_abbrev_tac `take_request_outcome rq ist` >>
  Cases_on `take_request_outcome rq ist` >> Cases_on `q` >>
  simp[] >> rename1 `INL v` >> PairCases_on `v` >>
  simp[vyperStateTheory.bind_assoc, vyperStateTheory.bind_return,
       vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
  Cases_on `adopt_call_outcome v0 v1 r` >> Cases_on `q` >> simp[]
QED

Theorem source_ordinary_eval_cuts[local]:
  (!cx static skip sig opts vs s os.
    source_wrapper_cut_at (eval_ext_call cx static skip sig opts vs) s os) /\
  (!cx gas vs s os.
    source_wrapper_cut_at (eval_send cx gas vs) s os) /\
  (!cx flags addr data amount gas s os.
    source_wrapper_cut_at (eval_raw_call cx flags addr data amount gas) s os)
Proof
  conj_tac >- suspend "extcall" >>
  conj_tac >- suspend "send" >> suspend "rawcall"
QED

Resume source_ordinary_eval_cuts[send]:
  rpt gen_tac >> strip_tac >>
  Cases_on `t.outcomes = SOME []`
  >- suspend "send_consumed" >>
  disj1_tac >> irule source_replay_unconsumed_cut >>
  simp[outcomes_suffix_send, outcome_prefix_causal_external_actions] >>
  goal_assum (drule_at Any)
QED
Resume source_ordinary_eval_cuts[send_consumed]:
  Cases_on `vs`
  >- gvs[source_send_oracle_normal] >>
  rename1 `h::tl` >> Cases_on `tl`
  >- gvs[source_send_oracle_normal] >>
  Cases_on `dest_AddressV h` >> Cases_on `dest_NumV h'` >>
  gvs[source_send_oracle_normal] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  gvs[source_take_call_bind_normal] >>
  qmatch_asmsub_abbrev_tac `bind (take_request_outcome rq) k` >>
  `os = []` by
    (drule_at (Pos (el 2)) source_take_request_bind_consumed >>
     simp[] >> disch_then irule >>
     simp[Abbr `k`] >> Cases >>
     simp[outcomes_frame_bind, outcomes_frame_adopt]) >>
  disj1_tac >> gvs[] >>
  `k = (\(rq,oc). if oc.co_success then
       bind (adopt_call_outcome rq oc) (\v. return (Value NoneV))
       else raise (Error (RuntimeError "send failed")))` by
    (simp[Abbr `k`, FUN_EQ_THM, FORALL_PROD,
          vyperStateTheory.bind_def, vyperStateTheory.check_def,
          vyperStateTheory.assert_def, vyperStateTheory.raise_def] >>
     rpt gen_tac >> IF_CASES_TAC >>
     simp[vyperStateTheory.bind_def, vyperStateTheory.raise_def]) >>
  qspecl_then [`rq`, `k`, `s`] mp_tac source_ordinary_probe_cut >>
  simp[probe_failed_outcome_def, empty_failed_outcome_def,
       failed_outcome_def, storage_trace_frame_raise] >> strip_tac >>
  first_assum (qspec_then `probe_failed_outcome` mp_tac) >>
  first_x_assum (qspec_then `empty_failed_outcome` mp_tac) >>
  gvs[probe_failed_outcome_def, empty_failed_outcome_def] >> metis_tac[]
QED
Resume source_ordinary_eval_cuts[extcall]:
  rpt gen_tac >> strip_tac >>
  Cases_on `t.outcomes = SOME []`
  >- suspend "extcall_consumed" >>
  disj1_tac >> irule source_replay_unconsumed_cut >>
  simp[outcomes_suffix_ext_call, outcome_prefix_causal_external_actions] >>
  goal_assum (drule_at Any)
QED
Resume source_ordinary_eval_cuts[extcall_consumed]:
  PairCases_on `sig` >> Cases_on `vs` >>
  gvs[source_ext_call_oracle_normal] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  gvs[AllCaseEqs()] >>
  gvs[source_take_call_bind_normal] >>
  qmatch_asmsub_abbrev_tac `bind (take_request_outcome rq) k` >>
  `os = []` by
    (drule_at (Pos (el 2)) source_take_request_bind_consumed >>
     simp[] >> disch_then irule >>
     simp[Abbr `k`] >> Cases >> simp[] >>
     irule outcomes_frame_bind >>
     simp[outcomes_frame_adopt, outcomes_frame_primitives,
          outcomes_frame_reads, outcomes_frame_bind] >>
     irule outcomes_frame_bind >> simp[outcomes_frame_adopt] >>
     TOP_CASE_TAC >>
     simp[outcomes_frame_bind, outcomes_frame_primitives,
          outcomes_frame_reads]) >>
  disj1_tac >> gvs[] >>
  `k (rq,failed_outcome rq) = raise (Error (RevertData [])) /\
   k (rq,probe_failed_outcome) = raise (Error (RevertData [])) /\
   k (rq,empty_failed_outcome) = raise (Error (RevertData []))` by
    simp[Abbr `k`, failed_outcome_def, probe_failed_outcome_def,
         empty_failed_outcome_def, FUN_EQ_THM,
         vyperStateTheory.bind_def, vyperStateTheory.raise_def] >>
  qspecl_then [`rq`, `k`, `s`] mp_tac source_ordinary_probe_cut >>
  simp[storage_trace_frame_raise] >> strip_tac >>
  first_assum (qspec_then `probe_failed_outcome` mp_tac) >>
  first_x_assum (qspec_then `empty_failed_outcome` mp_tac) >>
  simp[] >> gvs[] >> metis_tac[]
QED
Resume source_ordinary_eval_cuts[rawcall]:
  rpt gen_tac >> strip_tac >>
  Cases_on `t.outcomes = SOME []`
  >- suspend "rawcall_consumed" >>
  disj1_tac >> irule source_replay_unconsumed_cut >>
  simp[outcomes_suffix_raw_call, outcome_prefix_causal_external_actions] >>
  goal_assum (drule_at Any)
QED
Resume source_ordinary_eval_cuts[rawcall_consumed]:
  gvs[source_raw_call_oracle_normal] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `bind (take_request_outcome rq) k` >>
  `os = []` by
    (drule_at (Pos (el 2)) source_take_request_bind_consumed >>
     simp[] >> disch_then irule >>
     simp[Abbr `k`] >> Cases >> simp[] >>
     irule outcomes_frame_bind >> simp[outcomes_frame_adopt] >>
     rpt (IF_CASES_TAC >> simp[outcomes_frame_bind])) >>
  disj1_tac >> gvs[] >>
  `!oc. ~oc.co_success /\ oc.co_returnData = [] ==>
    k (rq,oc) =
      if flags.rcf_revert_on_failure then raise (Error (RevertData []))
      else if flags.rcf_max_outsize = 0 then return (Value (BoolV F))
      else return (Value (ArrayV (TupleV [BoolV F; BytesV []])))` by
    (rpt strip_tac >>
     simp[Abbr `k`, FUN_EQ_THM, vyperStateTheory.bind_def,
          adopt_call_outcome_equation, Abbr `rq`, call_outcome_request_def,
          delegate_outcome_request_def, vyperStateTheory.raise_def,
          vyperStateTheory.return_def] >>
     rpt (IF_CASES_TAC >> simp[vyperStateTheory.bind_def,
         vyperStateTheory.return_def, vyperStateTheory.raise_def])) >>
  `storage_trace_frame (k (rq,failed_outcome rq)) /\
   k (rq,probe_failed_outcome) = k (rq,failed_outcome rq) /\
   k (rq,empty_failed_outcome) = k (rq,failed_outcome rq)` by
    (simp[failed_outcome_def, probe_failed_outcome_def,
          empty_failed_outcome_def] >>
     Cases_on `flags.rcf_revert_on_failure` >>
     Cases_on `flags.rcf_max_outsize = 0` >>
     simp[storage_trace_frame_raise, storage_trace_frame_return]) >>
  qspecl_then [`rq`, `k`, `s`] mp_tac source_ordinary_probe_cut >>
  simp[] >> strip_tac >>
  first_assum (qspec_then `probe_failed_outcome` mp_tac) >>
  first_x_assum (qspec_then `empty_failed_outcome` mp_tac) >>
  simp[] >> gvs[] >> metis_tac[]
QED
Finalise source_ordinary_eval_cuts[local]

Theorem source_create_oracle_normal[local]:
  !cx kind salt rof tys vs cs s xs.
    eval_create cx kind salt rof tys vs cs (s with outcomes := SOME xs) =
    case dest_create_args kind salt vs of
    | NONE => (INR (Error (TypeError "create operand shape")), s with outcomes := SOME xs)
    | SOME ops => case create_arg_ctor_types kind salt tys of
    | NONE => (INR (Error (TypeError "create argument type shape")), s with outcomes := SOME xs)
    | SOME ctor => case build_create_code (get_tenv cx) kind ops s.accounts ctor cs of
    | NONE => (INR (Error (TypeError "create operands")), s with outcomes := SOME xs)
    | SOME ci =>
      if ~ci.cc_source_ok then
        (INR (Error (RuntimeError "create source has no deployable code")), s with outcomes := SOME xs)
      else if ~ci.cc_size_ok then
        (INR (Error (RuntimeError "create initcode too large")), s with outcomes := SOME xs)
      else if cx.txn.is_static then
        (INR (Error (RuntimeError "write in static context")), s with outcomes := SOME xs)
      else create_oracle_result ops.co_salt ops.co_value ci.cc_initcode rof
        (s with outcomes := SOME xs)
Proof
  rpt gen_tac >> Cases_on `dest_create_args kind salt vs` >>
  simp[vyperCreateTheory.eval_create_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.lift_option_type_def,
       vyperStateTheory.raise_def, vyperStateTheory.return_def] >>
  Cases_on `create_arg_ctor_types kind salt tys` >>
  simp[vyperStateTheory.get_accounts_def, vyperStateTheory.lift_option_type_def,
       vyperStateTheory.raise_def, vyperStateTheory.return_def] >>
  Cases_on `build_create_code (get_tenv cx) kind x s.accounts x' cs` >>
  simp[vyperStateTheory.lift_option_type_def,
       vyperStateTheory.raise_def, vyperStateTheory.return_def,
       vyperStateTheory.check_def, vyperStateTheory.assert_def,
       vyperStateTheory.check_not_static_def] >>
  rpt (IF_CASES_TAC >> gvs[])
QED

Theorem source_create_oracle_consumed[local]:
  !salt value code rof s os r t.
    create_oracle_result salt value code rof
      (s with outcomes := SOME (os ++ [probe_failed_outcome])) = (r,t) /\
    t.outcomes = SOME [] ==> os = []
Proof
  rpt gen_tac >>
  simp[vyperCreateTheory.create_oracle_result_def] >>
  qmatch_goalsub_abbrev_tac `take_create_outcome kind value code ist` >>
  Cases_on `take_create_outcome kind value code ist` >>
  drule take_create_outcome_suffix >>
  simp[Abbr `ist`] >> strip_tac >>
  Cases_on `q` >>
  simp[adopt_call_outcome_equation, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `LENGTH os = 0` by decide_tac >> gvs[]
QED

Theorem source_create_eval_cut[local]:
  !cx kind salt rof tys vs cs s os.
    source_wrapper_cut_at (eval_create cx kind salt rof tys vs cs) s os
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `t.outcomes = SOME []`
  >- suspend "consumed" >>
  disj1_tac >> irule source_replay_unconsumed_cut >>
  simp[outcomes_suffix_create, outcome_prefix_causal_external_actions] >>
  goal_assum (drule_at Any)
QED
Resume source_create_eval_cut[consumed]:
  gvs[source_create_oracle_normal, AllCaseEqs()] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  drule_all source_create_oracle_consumed >> strip_tac >> gvs[] >>
  `bind (create_oracle_result ops.co_salt ops.co_value ci.cc_initcode rof)
     return = create_oracle_result ops.co_salt ops.co_value ci.cc_initcode rof` by
    (simp[FUN_EQ_THM, vyperStateTheory.bind_def,
      vyperStateTheory.return_def] >> gen_tac >>
      Cases_on `create_oracle_result ops.co_salt ops.co_value ci.cc_initcode rof x` >>
      Cases_on `q` >> simp[]) >>
  disj2_tac >>
  qspecl_then [`ops.co_salt`, `ops.co_value`, `ci.cc_initcode`, `rof`]
    (qspec_then `return` mp_tac) source_create_probe_cut >>
  simp[vyperStateTheory.bind_return, vyperStateTheory.return_def] >>
  disch_then drule >> strip_tac >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qspecl_then [`ops.co_salt`, `ops.co_value`, `ci.cc_initcode`, `rof`]
    (qspec_then `return` mp_tac) source_create_empty_cut_state >>
  simp[vyperStateTheory.bind_return, vyperStateTheory.return_def] >>
  disch_then irule >> goal_assum (drule_at Any)
QED
Finalise source_create_eval_cut[local]

Theorem source_replay_replace_frame[local]:
  (!s oc. f (s with outcomes := oc) =
    (FST (f s), SND (f s) with outcomes := oc)) ==> outcomes_frame f
Proof
  strip_tac >> simp[outcomes_frame_def] >> gen_tac >>
  first_x_assum (qspecl_then [`st`,`st.outcomes`] mp_tac) >>
  simp[] >> disch_then (mp_tac o Q.AP_TERM `(\p. (SND p).outcomes)`) >> simp[]
QED

Theorem source_replay_frame_cut[local]:
  !f s os. outcomes_frame f /\ outcomes_suffix f /\ outcome_prefix_causal f ==>
    source_wrapper_cut_at f s os
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  disj1_tac >> irule source_replay_unconsumed_cut >>
  simp[] >> drule_all outcomes_frame_result >> simp[]
QED

Theorem source_replay_precompile_cut[local]:
  !bt s os. source_wrapper_cut_at (precompile_call_success bt) s os
Proof
  rpt gen_tac >> Cases_on `precompile_builtin bt`
  >- (Cases_on `os`
      >- (simp[precompile_call_success_def, probe_failed_outcome_def,
               empty_failed_outcome_def,
               vyperStateTheory.check_def, vyperStateTheory.assert_def,
               vyperStateTheory.raise_def] >> rpt strip_tac >> gvs[]) >>
      simp[precompile_call_success_def] >>
      Cases_on `call_outcome_success h` >>
      simp[vyperStateTheory.check_def, vyperStateTheory.assert_def,
           vyperStateTheory.raise_def, vyperStateTheory.return_def] >>
      rpt strip_tac >> gvs[] >> disj1_tac >> qexists_tac `t` >> simp[]) >>
  simp[precompile_call_success_def, vyperStateTheory.return_def] >>
  rpt strip_tac >> gvs[] >> disj1_tac >> qexists_tac `os` >> simp[]
QED

(* Keep cut traversal and semantic suppliers at separate abstraction levels. *)
val replay_cut_pattern = ``source_wrapper_cut_at f s os``;
fun is_replay_cut tm = can (match_term replay_cut_pattern) tm;
fun replay_cut_computation tm =
  rator (lhs (fst (dest_imp (snd (strip_forall tm)))));
fun replay_cut_at c tm = PURE_REWRITE_CONV [c (replay_cut_computation tm)] tm;
fun replay_cut_wrap_conv tm =
  if is_replay_cut tm then REWR_CONV exhausted_truth_wrapper tm
  else if is_forall tm then BINDER_CONV replay_cut_wrap_conv tm
  else if is_imp tm then RAND_CONV replay_cut_wrap_conv tm
  else ALL_CONV tm;
fun REPLAY_CUT_IH_TAC g =
  (RULE_ASSUM_TAC (CONV_RULE replay_cut_wrap_conv) >>
   CONV_TAC replay_cut_wrap_conv >>
   evalWalkLib.IH_TAC {stop = K false,
     normalise = PURE_REWRITE_RULE [GSYM AND_IMP_INTRO, custom_error_11,
       NOT_CLAUSES, AND_CLAUSES, IMP_CLAUSES,
       vyperStateTheory.ignore_bind_def]}) g;

val replay_frame_facts =
  [outcomes_frame_read_results, outcomes_frame_places,
   outcomes_frame_write_place, outcomes_frame_append_place,
   outcomes_frame_pop_place, outcomes_frame_resolve_array, outcomes_frame_reads,
   outcomes_frame_primitives, outcomes_frame_handlers,
   outcomes_frame_return, outcomes_frame_raise, outcomes_frame_static,
   outcomes_frame_adopt];
val replay_trace_facts =
  [evaluate_storage_trace_frame, storage_trace_frame_bind_all,
   storage_trace_frame_switch, storage_trace_frame_gas,
   storage_trace_frame_precompile_call_success,
   storage_trace_frame_send, storage_trace_frame_ext_call,
   storage_trace_frame_raw_call,
   storage_trace_frame_check_not_static,
   storage_trace_frame_return, storage_trace_frame_raise,
   storage_trace_frame_checks, storage_trace_frame_lifts,
   storage_trace_frame_read_result, storage_trace_frame_read_results,
   storage_trace_frame_state_reads, storage_trace_frame_state_updates,
   storage_trace_frame_write_place, storage_trace_frame_new_variable,
   storage_trace_frame_append_place, storage_trace_frame_read_place,
   storage_trace_frame_place_type, storage_trace_frame_extend_place,
   storage_trace_frame_pop_scope,
   storage_trace_frame_pop_place,
   storage_trace_frame_finally, storage_trace_frame_finally_unless_halt,
       storage_trace_frame_optional_locks, storage_trace_frame_function_handler,
       storage_trace_frame_function_stack,
       storage_trace_frame_array_iterator_results,
   storage_trace_frame_try, storage_trace_frame_loop_handler,
   storage_trace_frame_conditional_result, storage_trace_frame_select,
   storage_trace_frame_array_length];
val REPLAY_DROP_IHS = POP_ASSUM_LIST (fn facts => map_every assume_tac
  (List.filter (not o is_forall o concl) facts));
fun REPLAY_TRACE_STEP g = FIRST
  [(simp replay_trace_facts >> NO_TAC),
   (MATCH_MP_TAC storage_trace_frame_bind_all >> conj_tac),
   (MATCH_MP_TAC storage_trace_frame_finally >> conj_tac),
   (MATCH_MP_TAC storage_trace_frame_finally_unless_halt >> conj_tac),
   (MATCH_MP_TAC storage_trace_frame_try >> conj_tac),
   CONV_TAC (RAND_CONV (CHANGED_CONV evalWalkLib.head_conv)),
   CONV_TAC (RAND_CONV (evalWalkLib.unfold_conv [switch_BoolV_def, vyperStateTheory.ignore_bind_def])),
   (fn goal as (_,w) =>
     if is_cond (rand w) orelse TypeBase.is_case (rand w)
     then evalWalkLib.HEAD_CASE_TAC goal else NO_TAC goal),
   gen_tac, DISCH_THEN STRIP_ASSUME_TAC] g;
val REPLAY_TRACE_TAC = REPLAY_DROP_IHS >> rpt REPLAY_TRACE_STEP;
fun REPLAY_SUFFIX_STEP g = FIRST
  [ CONV_TAC (RAND_CONV (CHANGED_CONV BETA_CONV)),
    (MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac),
    (fn goal as (_,w) => FIRST (Net.match w prefix_assembly_net) goal),
    (simp[outcomes_suffix_precompile_call_success,
         eval_outcomes_suffix_with_results, outcomes_suffix_frame,
         outcomes_frame_bind] >> NO_TAC),
    (MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac),
    CONV_TAC (RAND_CONV (CHANGED_CONV evalWalkLib.head_conv)),
    CONV_TAC (RAND_CONV (evalWalkLib.unfold_conv [switch_BoolV_def, vyperStateTheory.ignore_bind_def])),
    (fn goal as (_,w) =>
      if is_cond (rand w) orelse TypeBase.is_case (rand w)
      then evalWalkLib.HEAD_CASE_TAC goal else NO_TAC goal),
    gen_tac, DISCH_THEN STRIP_ASSUME_TAC] g;
val REPLAY_SUFFIX_TAC = REPLAY_DROP_IHS >> rpt REPLAY_SUFFIX_STEP;
val replay_safety_net = List.foldl (fn (th,net) =>
  Net.insert (exhausted_computation (concl th), MATCH_ACCEPT_TAC th) net)
  Net.empty (map SPEC_ALL (CONJUNCTS source_exhausted_eval_safety_mutual));
fun REPLAY_SAFETY_STEP g = FIRST
  [(qpat_x_assum `acquire_nonreentrant_lock _ _ _ _ = _` mp_tac >>
    simp[acquire_nonreentrant_lock_def, vyperStateTheory.bind_def,
      vyperStateTheory.ignore_bind_def, vyperStateTheory.record_storage_event_def,
      vyperStateTheory.get_transient_storage_def, vyperStateTheory.update_transient_def,
      vyperStateTheory.check_def, vyperStateTheory.assert_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
    rpt strip_tac >> gvs[COND_RATOR, AllCaseEqs(), vyperStateTheory.raise_def,
      vyperStateTheory.return_def, vyperStateTheory.update_transient_def] >> NO_TAC),
   (qpat_x_assum `release_nonreentrant_lock _ _ _ = _` mp_tac >>
    simp[release_nonreentrant_lock_def, vyperStateTheory.get_transient_storage_def,
      vyperStateTheory.bind_def,
      vyperStateTheory.ignore_bind_def, vyperStateTheory.record_storage_event_def,
      vyperStateTheory.update_transient_def, vyperStateTheory.return_def] >>
    rpt strip_tac >> gvs[]),
   (rename1 `handle_function ex ss = _` >>
    qpat_x_assum `handle_function _ _ = _` mp_tac >> Cases_on `ex` >> simp[handle_function_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, AllCaseEqs()] >>
    rpt strip_tac >> gvs[] >> NO_TAC),
   (qpat_x_assum `next_gas_reading _ = _` mp_tac >>
    simp[next_gas_reading_def, vyperStateTheory.raise_def,
         vyperStateTheory.return_def, AllCaseEqs()] >>
    rpt strip_tac >> gvs[] >> NO_TAC),
   (qpat_x_assum `precompile_call_success _ _ = _` mp_tac >>
    simp[precompile_call_success_def] >>
    REPLAY_DROP_IHS >>
    simp[vyperStateTheory.check_def, vyperStateTheory.assert_def,
         vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
    rpt strip_tac >> gvs[] >> NO_TAC),
   (fn goal as (_,w) => if aconv w F then
      metis_tac[source_binop_excludes_create_error,
        source_range_excludes_create_error,
        MP source_type_pure_exclusions source_abi_decode_excludes_create_error,
        MP source_ordinary_pure_exclusions source_binop_excludes_create_error] goal else NO_TAC goal),
   (fn goal as (_,w) => FIRST
      (Net.match (exhausted_computation w) replay_safety_net) goal),
   EXHAUSTED_SAFETY_STEP] g;
val REPLAY_SAFETY_TAC = REPLAY_DROP_IHS >> rpt REPLAY_SAFETY_STEP;

fun REPLAY_SCOPES_WITH_TAC rule push_eq push_def = (fn goal as (_,w) =>
  let val run = funpow 4 rand w in
    (Cases_on [ANTIQUOTE run] >> simp[NULL_EQ] >>
     irule rule >>
     qpat_x_assum push_eq mp_tac >>
     simp[push_def, vyperStateTheory.return_def] >>
     REPLAY_DROP_IHS >> strip_tac >> gvs[] >>
     goal_assum (drule_at Any) >> simp[]) goal
  end);

val REPLAY_SCOPES_TAC = REPLAY_SCOPES_WITH_TAC
  (cj 1 source_replay_cleanup_scopes) `push_scope _ = _`
  vyperStateTheory.push_scope_def;
val REPLAY_LOOP_SCOPES_TAC = REPLAY_SCOPES_WITH_TAC
  (cj 2 source_replay_cleanup_scopes) `push_scope_with_var _ _ _ _ = _`
  vyperStateTheory.push_scope_with_var_def;

fun replay_recursive tm = List.exists (fn n => n =
    fst (dest_const (fst (strip_comb tm))))
  ["eval_stmt", "eval_stmts", "eval_iterator", "eval_for", "eval_expr",
   "eval_exprs", "eval_base_place", "eval_target_place", "assign_tuple_targets",
   "assign_tuple_target_list", "eval_expr_results"];
fun REPLAY_CUT_STEP g = FIRST
  [MATCH_ACCEPT_TAC source_replay_precompile_cut,
   MATCH_ACCEPT_TAC (cj 1 source_ordinary_eval_cuts),
   MATCH_ACCEPT_TAC (cj 2 source_ordinary_eval_cuts),
   MATCH_ACCEPT_TAC (cj 3 source_ordinary_eval_cuts),
   MATCH_ACCEPT_TAC source_create_eval_cut,
   (fn goal as (_,w) => if is_replay_cut w andalso
      replay_recursive (replay_cut_computation w) then
      REPLAY_CUT_IH_TAC goal else NO_TAC goal),
   (fn goal as (_,w) => if is_replay_cut w then
      (MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac) goal
      else NO_TAC goal),
   (fn goal as (_,w) => if is_replay_cut w then
      (MATCH_MP_TAC source_replay_frame_cut >> REPLAY_DROP_IHS >> conj_tac
       >- (simp replay_frame_facts >> NO_TAC) >> conj_tac
       >- (irule outcomes_suffix_frame >> simp replay_frame_facts >> NO_TAC) >>
       rpt PREFIX_STEP >> NO_TAC) goal else NO_TAC goal),
   CONV_TAC (replay_cut_at (CHANGED_CONV (DEPTH_CONV BETA_CONV))),
   CONV_TAC (replay_cut_at (CHANGED_CONV evalWalkLib.head_conv)),
   CONV_TAC (replay_cut_at (evalWalkLib.unfold_conv
     [vyperStateTheory.ignore_bind_def, switch_BoolV_def])),
   (fn goal as (_,w) => if is_replay_cut w then
      let val c = replay_cut_computation w in
        if TypeBase.is_case c orelse is_cond c
        then evalWalkLib.HEAD_CASE_TAC goal else NO_TAC goal end
      else NO_TAC goal),
   (fn goal as (_,w) => if can (match_term ``outcomes_suffix f``) w
      then CHANGED_TAC REPLAY_SUFFIX_TAC goal else NO_TAC goal),
   (fn goal as (_,w) => if can (match_term ``storage_trace_frame f``) w
      then CHANGED_TAC REPLAY_TRACE_TAC goal else NO_TAC goal),
   (fn goal as (_,w) => if is_exhausted_safety w
      then CHANGED_TAC REPLAY_SAFETY_TAC goal else NO_TAC goal),
   (fn goal as (_,w) => if is_replay_cut w then NO_TAC goal
      else FIRST [gen_tac, conj_tac, DISCH_THEN STRIP_ASSUME_TAC] goal)] g;

Theorem source_replay_internal_suppliers[local]:
  !cx src_id_opt fn args dflts es ret mut nr stmts vs.
    outcomes_suffix (do
      prev <- get_scopes;
      dflt_vs <- finally
        do set_scopes [FEMPTY];
           eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
             (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
        od (set_scopes prev);
      env <- lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
        "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret) "IntCall eval ret";
      lock_if_nr cx nr (is_view_mut mut);
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally_unless_halt
        (finally (try (do eval_stmts cxf stmts; return NoneV od) handle_function)
          (pop_function prev)) (unlock_if_nr cx nr (is_view_mut mut));
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
    od) /\
    storage_trace_frame (do
      prev <- get_scopes;
      dflt_vs <- finally
        do set_scopes [FEMPTY];
           eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
             (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
        od (set_scopes prev);
      env <- lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
        "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret) "IntCall eval ret";
      lock_if_nr cx nr (is_view_mut mut);
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally_unless_halt
        (finally (try (do eval_stmts cxf stmts; return NoneV od) handle_function)
          (pop_function prev)) (unlock_if_nr cx nr (is_view_mut mut));
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
    od) /\
    source_exhausted_safe (do
      prev <- get_scopes;
      dflt_vs <- finally
        do set_scopes [FEMPTY];
           eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
             (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
        od (set_scopes prev);
      env <- lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
        "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret) "IntCall eval ret";
      lock_if_nr cx nr (is_view_mut mut);
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally_unless_halt
        (finally (try (do eval_stmts cxf stmts; return NoneV od) handle_function)
          (pop_function prev)) (unlock_if_nr cx nr (is_view_mut mut));
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
    od)
Proof
  rpt gen_tac >> rewrite_tac[LET_THM, vyperStateTheory.ignore_bind_def] >>
  BETA_TAC >> conj_tac
  >- (MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
      >- REPLAY_SUFFIX_TAC >>
      rpt gen_tac >> strip_tac >> BETA_TAC >>
      MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
      >- REPLAY_SUFFIX_TAC >>
      rpt gen_tac >> strip_tac >> REPLAY_SUFFIX_TAC) >>
  conj_tac >- REPLAY_TRACE_TAC >>
  REPLAY_SAFETY_TAC
QED

val REPLAY_BASE_SUFFIX_STEP = REPLAY_SUFFIX_STEP;
val REPLAY_BASE_TRACE_STEP = REPLAY_TRACE_STEP;
val REPLAY_BASE_SAFETY_STEP = REPLAY_SAFETY_STEP;
val replay_internal_supplier_facts =
  CONJUNCTS (SPEC_ALL (BETA_RULE (PURE_REWRITE_RULE
    [LET_THM, vyperStateTheory.ignore_bind_def] source_replay_internal_suppliers)));
val REPLAY_INTERNAL_SUPPLIER_TAC =
  BETA_TAC >> rewrite_tac[LET_THM, vyperStateTheory.ignore_bind_def] >> BETA_TAC >>
  FIRST (map MATCH_ACCEPT_TAC replay_internal_supplier_facts);

val REPLAY_SUFFIX_STEP = FIRST [FIRST (map MATCH_ACCEPT_TAC replay_internal_supplier_facts), REPLAY_BASE_SUFFIX_STEP];
val REPLAY_SUFFIX_TAC = REPLAY_DROP_IHS >> BETA_TAC >>
  rewrite_tac[LET_THM, vyperStateTheory.ignore_bind_def] >> BETA_TAC >> rpt REPLAY_SUFFIX_STEP;
val REPLAY_TRACE_STEP = FIRST [FIRST (map MATCH_ACCEPT_TAC replay_internal_supplier_facts), REPLAY_BASE_TRACE_STEP];
val REPLAY_TRACE_TAC = REPLAY_DROP_IHS >> BETA_TAC >>
  rewrite_tac[LET_THM, vyperStateTheory.ignore_bind_def] >> BETA_TAC >> rpt REPLAY_TRACE_STEP;
val REPLAY_SAFETY_STEP = FIRST [FIRST (map MATCH_ACCEPT_TAC replay_internal_supplier_facts), REPLAY_BASE_SAFETY_STEP];
val REPLAY_SAFETY_TAC = REPLAY_DROP_IHS >> BETA_TAC >>
  rewrite_tac[LET_THM, vyperStateTheory.ignore_bind_def] >> BETA_TAC >> rpt REPLAY_SAFETY_STEP;

Theorem source_replay_internal_args_suppliers[local]:
  !cx src_id_opt fn args dflts es ret mut nr stmts.
    outcomes_suffix (do
      type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
        "IntCall args length";
      vs <- eval_exprs cx es;
      prev <- get_scopes;
      dflt_vs <- finally
        do set_scopes [FEMPTY];
           eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
             (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
        od (set_scopes prev);
      env <- lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
        "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret) "IntCall eval ret";
      lock_if_nr cx nr (is_view_mut mut);
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally_unless_halt
        (finally (try (do eval_stmts cxf stmts; return NoneV od) handle_function)
          (pop_function prev)) (unlock_if_nr cx nr (is_view_mut mut));
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
    od) /\
    storage_trace_frame (do
      type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
        "IntCall args length";
      vs <- eval_exprs cx es;
      prev <- get_scopes;
      dflt_vs <- finally
        do set_scopes [FEMPTY];
           eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
             (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
        od (set_scopes prev);
      env <- lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
        "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret) "IntCall eval ret";
      lock_if_nr cx nr (is_view_mut mut);
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally_unless_halt
        (finally (try (do eval_stmts cxf stmts; return NoneV od) handle_function)
          (pop_function prev)) (unlock_if_nr cx nr (is_view_mut mut));
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
    od) /\
    source_exhausted_safe (do
      type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
        "IntCall args length";
      vs <- eval_exprs cx es;
      prev <- get_scopes;
      dflt_vs <- finally
        do set_scopes [FEMPTY];
           eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
             (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
        od (set_scopes prev);
      env <- lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
        "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret) "IntCall eval ret";
      lock_if_nr cx nr (is_view_mut mut);
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally_unless_halt
        (finally (try (do eval_stmts cxf stmts; return NoneV od) handle_function)
          (pop_function prev)) (unlock_if_nr cx nr (is_view_mut mut));
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
    od)
Proof
  rpt gen_tac >> rewrite_tac[LET_THM, vyperStateTheory.ignore_bind_def] >>
  BETA_TAC >> conj_tac
  >- (MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
      >- REPLAY_SUFFIX_TAC >>
      rpt gen_tac >> strip_tac >> BETA_TAC >>
      MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
      >- REPLAY_SUFFIX_TAC >>
      rpt gen_tac >> strip_tac >> REPLAY_INTERNAL_SUPPLIER_TAC) >>
  conj_tac >- REPLAY_TRACE_TAC >> REPLAY_SAFETY_TAC
QED

val replay_internal_supplier_facts = replay_internal_supplier_facts @
  CONJUNCTS (SPEC_ALL (BETA_RULE (PURE_REWRITE_RULE
    [LET_THM, vyperStateTheory.ignore_bind_def] source_replay_internal_args_suppliers)));
val REPLAY_INTERNAL_SUPPLIER_TAC =
  BETA_TAC >> rewrite_tac[LET_THM, vyperStateTheory.ignore_bind_def] >> BETA_TAC >>
  FIRST (map MATCH_ACCEPT_TAC replay_internal_supplier_facts);
val REPLAY_SUFFIX_STEP = FIRST [FIRST (map MATCH_ACCEPT_TAC replay_internal_supplier_facts), REPLAY_BASE_SUFFIX_STEP];
val REPLAY_SUFFIX_TAC = REPLAY_DROP_IHS >> BETA_TAC >>
  rewrite_tac[LET_THM, vyperStateTheory.ignore_bind_def] >> BETA_TAC >> rpt REPLAY_SUFFIX_STEP;
val REPLAY_TRACE_STEP = FIRST [FIRST (map MATCH_ACCEPT_TAC replay_internal_supplier_facts), REPLAY_BASE_TRACE_STEP];
val REPLAY_TRACE_TAC = REPLAY_DROP_IHS >> BETA_TAC >>
  rewrite_tac[LET_THM, vyperStateTheory.ignore_bind_def] >> BETA_TAC >> rpt REPLAY_TRACE_STEP;
val REPLAY_SAFETY_STEP = FIRST [FIRST (map MATCH_ACCEPT_TAC replay_internal_supplier_facts), REPLAY_BASE_SAFETY_STEP];
val REPLAY_SAFETY_TAC = REPLAY_DROP_IHS >> BETA_TAC >>
  rewrite_tac[LET_THM, vyperStateTheory.ignore_bind_def] >> BETA_TAC >> rpt REPLAY_SAFETY_STEP;

Theorem eval_outcome_probe_cut_mutual:
  (!cx stmt s os. source_wrapper_cut_at (eval_stmt cx stmt) s os) /\
  (!cx stmts s os. source_wrapper_cut_at (eval_stmts cx stmts) s os) /\
  (!cx it s os. source_wrapper_cut_at (eval_iterator cx it) s os) /\
  (!cx tyv id fbody vs s os.
    source_wrapper_cut_at (eval_for cx tyv id fbody vs) s os) /\
  (!cx e s os. source_wrapper_cut_at (eval_expr cx e) s os) /\
  (!cx es s os. source_wrapper_cut_at (eval_exprs cx es) s os) /\
  (!cx t s os. source_wrapper_cut_at (eval_base_place cx t) s os) /\
  (!cx t s os. source_wrapper_cut_at (eval_target_place cx t) s os) /\
  (!cx g v s os. source_wrapper_cut_at (assign_tuple_targets cx g v) s os) /\
  (!cx gs vs s os. source_wrapper_cut_at (assign_tuple_target_list cx gs vs) s os) /\
  (!cx es s os. source_wrapper_cut_at (eval_expr_results cx es) s os)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac
  >- (ntac 3 gen_tac >> ho_match_mp_tac source_replay_frame_cut >>
      simp[eval_outcomes_suffix_with_results, eval_outcome_prefix_causal_mutual] >>
      simp[Once evaluate_def])
  >- (ntac 3 gen_tac >> ho_match_mp_tac source_replay_frame_cut >>
      simp[eval_outcomes_suffix_with_results, eval_outcome_prefix_causal_mutual] >>
      simp[Once evaluate_def])
  >- (ntac 3 gen_tac >> ho_match_mp_tac source_replay_frame_cut >>
      simp[eval_outcomes_suffix_with_results, eval_outcome_prefix_causal_mutual] >>
      simp[Once evaluate_def])
  >- (ntac 3 gen_tac >> ho_match_mp_tac source_replay_frame_cut >>
      simp[eval_outcomes_suffix_with_results, eval_outcome_prefix_causal_mutual] >>
      simp[Once evaluate_def])
  >- (ntac 2 gen_tac >> strip_tac >>
      rewrite_tac[cj 5 evaluate_def] >>
      ho_match_mp_tac source_replay_cut_bind >>
      conj_tac >- first_assum MATCH_ACCEPT_TAC >>
      conj_tac
      >- (ntac 3 gen_tac >> ho_match_mp_tac source_replay_frame_cut >>
          conj_tac >- simp[] >> conj_tac
          >- (irule outcomes_suffix_frame >> simp[]) >>
          rpt PREFIX_STEP) >>
      conj_tac
      >- (gen_tac >> irule outcomes_suffix_frame >> simp[]) >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          irule source_replay_bind_transport >> simp[] >>
          gen_tac >> irule storage_trace_frame_bind_all >>
          simp[storage_trace_frame_read_result, storage_trace_frame_raise]) >>
      gen_tac >>
      `source_exhausted_safe
        (bind (read_result cx tv)
          (\v. (raise (ReturnException v) : evaluation_state -> unit evaluation_result)))` by
        rpt EXHAUSTED_SAFETY_STEP >>
      qpat_x_assum `!s os r t. _` kall_tac >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `source_exhausted_safe _`
        (qspecl_then [`s`,`r`,`t`] mp_tac) >> simp[])
  >- (ntac 3 gen_tac >> ho_match_mp_tac source_replay_frame_cut >>
      simp[eval_outcomes_suffix_with_results, eval_outcome_prefix_causal_mutual] >>
      simp[Once evaluate_def])
  >- (ntac 3 gen_tac >> ho_match_mp_tac source_replay_frame_cut >>
      simp[eval_outcomes_suffix_with_results, eval_outcome_prefix_causal_mutual] >>
      simp[Once evaluate_def])
  >- (ntac 2 gen_tac >> strip_tac >>
      rewrite_tac[cj 8 evaluate_def] >>
      ho_match_mp_tac source_replay_cut_bind >>
      conj_tac >- first_assum MATCH_ACCEPT_TAC >>
      conj_tac
      >- (ntac 3 gen_tac >> ho_match_mp_tac source_replay_frame_cut >>
          conj_tac >- simp[] >> conj_tac
          >- (irule outcomes_suffix_frame >> simp[]) >> rpt PREFIX_STEP) >>
      conj_tac >- (gen_tac >> irule outcomes_suffix_frame >> simp[]) >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          irule source_replay_bind_transport >> simp[] >>
          gen_tac >> irule storage_trace_frame_bind_all >>
          simp[storage_trace_frame_read_result] >> qx_gen_tac `sv` >>
          Cases_on `dest_StringV sv` >>
          simp[vyperStateTheory.lift_option_type_def,
            storage_trace_frame_raise, vyperStateTheory.bind_return] >>
          irule storage_trace_frame_bind_all >> simp[storage_trace_frame_raise]) >>
      gen_tac >>
      `source_exhausted_safe
        (bind (read_result cx tv) (\v.
          bind (lift_option_type (dest_StringV v) "not StringV")
            (\str. (raise (AssertException str) : evaluation_state -> unit evaluation_result))))` by
        rpt EXHAUSTED_SAFETY_STEP >>
      qpat_x_assum `!s os r t. _` kall_tac >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `source_exhausted_safe _`
        (qspecl_then [`s`,`r`,`t`] mp_tac) >> simp[])
  >- (ntac 2 gen_tac >> strip_tac >> rewrite_tac[cj 9 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 2 gen_tac >> strip_tac >> rewrite_tac[cj 10 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 2 gen_tac >> strip_tac >> rewrite_tac[cj 11 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 12 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 13 evaluate_def] >>
      ntac 5 REPLAY_CUT_STEP
      >- rpt REPLAY_CUT_STEP >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 14 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 4 gen_tac >> strip_tac >> rewrite_tac[cj 15 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 16 evaluate_def] >>
      ntac 5 REPLAY_CUT_STEP
      >- rpt REPLAY_CUT_STEP >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 17 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 18 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 5 gen_tac >> strip_tac >> rewrite_tac[cj 19 evaluate_def] >>
      ntac 5 REPLAY_CUT_STEP
      >- rpt REPLAY_CUT_STEP >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 4 gen_tac >> strip_tac >> rewrite_tac[cj 20 evaluate_def] >>
      ntac 5 REPLAY_CUT_STEP
      >- (ntac 10 REPLAY_CUT_STEP
          >- (strip_tac >> BETA_TAC >>
              MATCH_MP_TAC (cj 1 source_replay_cut_wrappers) >>
              conj_tac
              >- REPLAY_SCOPES_TAC >>
              conj_tac
              >- REPLAY_SCOPES_TAC >>
              rpt REPLAY_CUT_STEP) >>
          rpt REPLAY_CUT_STEP) >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 6 gen_tac >> strip_tac >> rewrite_tac[cj 21 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 2 gen_tac >> strip_tac >> rewrite_tac[cj 22 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (gen_tac >> rewrite_tac[cj 23 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 24 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 2 gen_tac >> strip_tac >> rewrite_tac[cj 25 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 26 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 4 gen_tac >> rewrite_tac[cj 27 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (rpt gen_tac >> strip_tac >> rewrite_tac[cj 28 evaluate_def] >>
      ntac 5 REPLAY_CUT_STEP
      >- (ntac 10 REPLAY_CUT_STEP
          >- (strip_tac >> BETA_TAC >>
              MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
              >- (MATCH_MP_TAC (cj 3 source_replay_cut_wrappers) >>
                  conj_tac
                  >- REPLAY_LOOP_SCOPES_TAC >>
                  conj_tac
                  >- REPLAY_LOOP_SCOPES_TAC >>
                  rpt REPLAY_CUT_STEP) >>
              rpt REPLAY_CUT_STEP >> REPLAY_CUT_IH_TAC) >>
          rpt REPLAY_CUT_STEP) >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> rewrite_tac[cj 29 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 4 gen_tac >> rewrite_tac[cj 30 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 4 gen_tac >> rewrite_tac[cj 31 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 5 gen_tac >> strip_tac >> rewrite_tac[cj 32 evaluate_def] >>
      ntac 5 REPLAY_CUT_STEP
      >- (ntac 10 REPLAY_CUT_STEP
          >- (ntac 5 REPLAY_CUT_STEP >>
              qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> _`
                drule >> strip_tac >> simp[]) >>
          all_tac
          >- REPLAY_SUFFIX_TAC >>
          ntac 1 REPLAY_CUT_STEP
          >- REPLAY_TRACE_TAC
          >- REPLAY_SAFETY_TAC >>
          rpt REPLAY_CUT_STEP) >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> rewrite_tac[cj 33 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (rpt gen_tac >> strip_tac >> rewrite_tac[cj 34 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 4 gen_tac >> strip_tac >> rewrite_tac[cj 35 evaluate_def] >>
      ntac 5 REPLAY_CUT_STEP
      >- (ntac 10 REPLAY_CUT_STEP
          >- (BETA_TAC >> rpt REPLAY_CUT_STEP) >>
          rpt REPLAY_CUT_STEP) >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 4 gen_tac >> strip_tac >> rewrite_tac[cj 36 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 4 gen_tac >> strip_tac >> rewrite_tac[cj 37 evaluate_def] >>
      ntac 4 REPLAY_CUT_STEP
      >- rpt REPLAY_CUT_STEP >>
      ntac 4 REPLAY_CUT_STEP
      >- (strip_tac >> BETA_TAC >> Cases_on `bt = Len` >>
          asm_simp_tac bool_ss [COND_CLAUSES]
          >- rpt REPLAY_CUT_STEP >>
          Cases_on `bt = Bop In \/ bt = Bop NotIn` >>
          asm_simp_tac bool_ss [COND_CLAUSES] >>
          ntac 3 REPLAY_CUT_STEP
          >- ntac 10 REPLAY_CUT_STEP
          >- (gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
              conj_tac >- REPLAY_TRACE_TAC >>
              REPLAY_SAFETY_TAC)
          >- rpt REPLAY_CUT_STEP
          >- rpt REPLAY_CUT_STEP >>
          all_tac
          >- rpt REPLAY_CUT_STEP
          >- (conj_tac
          >- (ntac 6 REPLAY_CUT_STEP
              >- rpt REPLAY_CUT_STEP >>
              conj_tac
              >- (ntac 5 REPLAY_CUT_STEP >>
                  MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
                  >- rpt REPLAY_CUT_STEP >>
                  conj_tac
                  >- rpt REPLAY_CUT_STEP >>
                  gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
                  conj_tac >- REPLAY_TRACE_TAC >>
                  REPLAY_SAFETY_TAC) >>
              gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
              conj_tac >- REPLAY_TRACE_TAC >>
              REPLAY_SAFETY_TAC) >>
          gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
          conj_tac >- REPLAY_TRACE_TAC >>
          REPLAY_SAFETY_TAC) >>
          rpt REPLAY_CUT_STEP) >>
      all_tac >- REPLAY_TRACE_TAC >>
      REPLAY_SAFETY_TAC)
  >- (ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 38 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (rpt gen_tac >> strip_tac >> rewrite_tac[cj 39 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (rpt gen_tac >> strip_tac >> rewrite_tac[cj 40 evaluate_def] >>
      ntac 4 REPLAY_CUT_STEP
      >- rpt REPLAY_CUT_STEP >>
      conj_tac >- (ntac 5 REPLAY_CUT_STEP >>
        MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
        >- REPLAY_CUT_IH_TAC >>
        conj_tac >- rpt REPLAY_CUT_STEP >>
        gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
        conj_tac >- REPLAY_TRACE_TAC >>
        REPLAY_SAFETY_TAC) >>
      gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
      conj_tac >- REPLAY_TRACE_TAC >>
      REPLAY_SAFETY_TAC)
  >- (rpt gen_tac >> strip_tac >> rewrite_tac[cj 41 evaluate_def] >>
      ntac 4 REPLAY_CUT_STEP
      >- (ntac 6 REPLAY_CUT_STEP >> BETA_TAC >>
          MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
          >- REPLAY_CUT_IH_TAC >>
          conj_tac >- (ntac 5 REPLAY_CUT_STEP >>
            MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
            >- REPLAY_CUT_IH_TAC >>
            conj_tac >- rpt REPLAY_CUT_STEP >>
            gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
            conj_tac >- REPLAY_TRACE_TAC >>
            REPLAY_SAFETY_TAC) >>
          gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
          conj_tac >- REPLAY_TRACE_TAC >>
          REPLAY_SAFETY_TAC) >>
      gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
      conj_tac >- REPLAY_TRACE_TAC >>
      REPLAY_SAFETY_TAC)
  >- (rpt gen_tac >> strip_tac >> rewrite_tac[cj 42 evaluate_def] >>
      ntac 4 REPLAY_CUT_STEP
      >- rpt REPLAY_CUT_STEP >>
      conj_tac >- (ntac 5 REPLAY_CUT_STEP >>
        MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
        >- rpt REPLAY_CUT_STEP >>
        conj_tac >- (ntac 5 REPLAY_CUT_STEP >>
          MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
          >- rpt REPLAY_CUT_STEP >>
          conj_tac >- (ntac 6 REPLAY_CUT_STEP >>
            BETA_TAC >> rewrite_tac[LET_THM] >> BETA_TAC >>
            rewrite_tac[vyperStateTheory.ignore_bind_def] >>
            MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
            >- rpt REPLAY_CUT_STEP >>
            conj_tac >- (ntac 5 REPLAY_CUT_STEP >>
              MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
              >- REPLAY_CUT_IH_TAC >>
              conj_tac >- (ntac 5 REPLAY_CUT_STEP >>
                MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
                >- rpt REPLAY_CUT_STEP >>
                conj_tac >- (ntac 5 REPLAY_CUT_STEP >>
                  MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
                  >- (MATCH_MP_TAC (cj 2 source_replay_cut_wrappers) >>
                      rpt REPLAY_CUT_STEP) >>
                  conj_tac >- (ntac 5 REPLAY_CUT_STEP >>
                    MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
                    >- rpt REPLAY_CUT_STEP >>
                    conj_tac >- (ntac 5 REPLAY_CUT_STEP >>
                      MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
                      >- rpt REPLAY_CUT_STEP >>
                      conj_tac >- (ntac 5 REPLAY_CUT_STEP >>
                        MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
                        >- (rewrite_tac[lock_if_nr_def] >>
                            rpt REPLAY_CUT_STEP) >>
                        conj_tac >- (ntac 5 REPLAY_CUT_STEP >>
                          MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
                          >- rpt REPLAY_CUT_STEP >>
                          conj_tac >- (ntac 5 REPLAY_CUT_STEP >>
                            MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
                            >- (MATCH_MP_TAC (cj 4 source_replay_cut_wrappers) >>
                                conj_tac >- metis_tac[source_replay_internal_cleanup] >>
                                rpt REPLAY_CUT_STEP) >>
                            conj_tac >- rpt REPLAY_CUT_STEP >>
                            gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
                            conj_tac >- REPLAY_TRACE_TAC >>
                            REPLAY_SAFETY_TAC) >>
                          gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
                          conj_tac >- REPLAY_TRACE_TAC >>
                          REPLAY_SAFETY_TAC) >>
                        gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
                        conj_tac >- REPLAY_TRACE_TAC >>
                        REPLAY_SAFETY_TAC) >>
                      gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
                      conj_tac >- REPLAY_TRACE_TAC >>
                      REPLAY_SAFETY_TAC) >>
                    gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
                    conj_tac >- REPLAY_TRACE_TAC >>
                    REPLAY_SAFETY_TAC) >>
                  gen_tac >> conj_tac
                  >- (REPLAY_DROP_IHS >> BETA_TAC >>
                      MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
                      >- REPLAY_SUFFIX_TAC >>
                      rpt gen_tac >> strip_tac >> REPLAY_SUFFIX_TAC) >>
                  conj_tac >- REPLAY_TRACE_TAC >>
                  REPLAY_SAFETY_TAC) >>
                gen_tac >> conj_tac
                >- (REPLAY_DROP_IHS >> BETA_TAC >>
                    MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
                    >- REPLAY_SUFFIX_TAC >>
                    rpt gen_tac >> strip_tac >> BETA_TAC >>
                    MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
                    >- REPLAY_SUFFIX_TAC >>
                    rpt gen_tac >> strip_tac >> REPLAY_SUFFIX_TAC) >>
                conj_tac >- REPLAY_TRACE_TAC >>
                REPLAY_DROP_IHS >> BETA_TAC >>
                MATCH_MP_TAC source_exhausted_bind_safety >> conj_tac
                >- REPLAY_SAFETY_TAC >>
                rpt gen_tac >> strip_tac >> REPLAY_SAFETY_TAC) >>
              gen_tac >> conj_tac
              >- (REPLAY_DROP_IHS >> BETA_TAC >>
                  MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
                  >- REPLAY_SUFFIX_TAC >>
                  rpt gen_tac >> strip_tac >> BETA_TAC >>
                  MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
                  >- REPLAY_SUFFIX_TAC >>
                  rpt gen_tac >> strip_tac >> REPLAY_SUFFIX_TAC) >>
              conj_tac >- REPLAY_TRACE_TAC >>
              REPLAY_INTERNAL_SUPPLIER_TAC) >>
            gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
            conj_tac >- REPLAY_TRACE_TAC >>
            REPLAY_DROP_IHS >> BETA_TAC >>
            MATCH_MP_TAC source_exhausted_bind_safety >> conj_tac
            >- REPLAY_SAFETY_TAC >>
            rpt gen_tac >> strip_tac >> REPLAY_INTERNAL_SUPPLIER_TAC) >>
          gen_tac >> conj_tac >- REPLAY_INTERNAL_SUPPLIER_TAC >>
          conj_tac >- REPLAY_INTERNAL_SUPPLIER_TAC >>
          REPLAY_INTERNAL_SUPPLIER_TAC) >>
        gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
        conj_tac >- REPLAY_TRACE_TAC >>
        REPLAY_SAFETY_TAC) >>
      gen_tac >> conj_tac
      >- (REPLAY_DROP_IHS >> BETA_TAC >>
          MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
          >- REPLAY_SUFFIX_TAC >>
          rpt gen_tac >> strip_tac >> BETA_TAC >>
          MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
          >- REPLAY_SUFFIX_TAC >>
          rpt gen_tac >> strip_tac >> REPLAY_INTERNAL_SUPPLIER_TAC) >>
      conj_tac >- REPLAY_TRACE_TAC >>
      REPLAY_DROP_IHS >> BETA_TAC >>
      MATCH_MP_TAC source_exhausted_bind_safety >> conj_tac
      >- REPLAY_SAFETY_TAC >>
      rpt gen_tac >> strip_tac >> BETA_TAC >>
      MATCH_MP_TAC source_exhausted_bind_safety >> conj_tac
      >- REPLAY_SAFETY_TAC >>
      rpt gen_tac >> strip_tac >> REPLAY_INTERNAL_SUPPLIER_TAC)
  >- (rpt gen_tac >> strip_tac >> rewrite_tac[cj 43 evaluate_def] >>
      ntac 4 REPLAY_CUT_STEP
      >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
          rewrite_tac[vyperStateTheory.ignore_bind_def] >>
          MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
          >- rpt REPLAY_CUT_STEP >>
          conj_tac >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
            MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
            >- rpt REPLAY_CUT_STEP >>
            conj_tac >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
              MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
              >- rpt REPLAY_CUT_STEP >>
              conj_tac >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
                MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
                >- rpt REPLAY_CUT_STEP >>
                conj_tac >- rpt REPLAY_CUT_STEP >>
                gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
                conj_tac >- REPLAY_TRACE_TAC >> REPLAY_SAFETY_TAC) >>
              gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
              conj_tac >- REPLAY_TRACE_TAC >> REPLAY_SAFETY_TAC) >>
            gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
            conj_tac >- REPLAY_TRACE_TAC >> REPLAY_SAFETY_TAC) >>
          gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
          conj_tac >- REPLAY_TRACE_TAC >> REPLAY_SAFETY_TAC) >>
      gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
      conj_tac >- REPLAY_TRACE_TAC >>
      REPLAY_SAFETY_TAC)
  >- (rpt gen_tac >> strip_tac >> rewrite_tac[cj 44 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (rpt gen_tac >> strip_tac >> rewrite_tac[cj 45 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (rpt gen_tac >> strip_tac >> rewrite_tac[cj 46 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (rpt gen_tac >> strip_tac >> rewrite_tac[cj 47 evaluate_def] >>
      ntac 2 gen_tac >> MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
      >- REPLAY_CUT_IH_TAC >>
      conj_tac >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
        MATCH_MP_TAC source_replay_frame_cut >> REPLAY_DROP_IHS >>
        conj_tac >- (Cases_on `cx.txn.created_in_tx` >>
          simp[LET_THM, vyperStateTheory.ignore_bind_def,
            outcomes_frame_bind, outcomes_frame_primitives, outcomes_frame_reads,
            outcomes_frame_static, outcomes_frame_return, outcomes_frame_raise] >>
          rpt (FIRST [CHANGED_TAC BETA_TAC,
            irule outcomes_frame_bind >> conj_tac, gen_tac,
            simp[outcomes_frame_primitives, outcomes_frame_reads,
              outcomes_frame_static, outcomes_frame_return, outcomes_frame_raise] >> NO_TAC])) >>
        conj_tac >- (REPLAY_SUFFIX_TAC) >>
        rpt PREFIX_STEP) >>
      gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
      conj_tac >- (REPLAY_TRACE_TAC >>
        MATCH_ACCEPT_TAC storage_trace_frame_transfer_value) >> REPLAY_SAFETY_TAC)
  >- (rpt gen_tac >> strip_tac >> rewrite_tac[cj 48 evaluate_def] >>
      Cases_on `kind` >> rewrite_tac[create_kind_case_def] >>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [create_kind_distinct, create_kind_11,
        REFL_CLAUSE, AND_CLAUSES, IMP_CLAUSES, FORALL_SIMP]) >>
      (ntac 2 gen_tac >>
      MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
      >- REPLAY_CUT_IH_TAC >>
      conj_tac >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
        FIRST [MATCH_ACCEPT_TAC source_create_eval_cut,
          IF (CONV_TAC (replay_cut_at (CHANGED_CONV (SIMP_CONV bool_ss [LET_THM]))))
            (MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
             >- REPLAY_CUT_IH_TAC >>
             conj_tac >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
               MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
               >- (rpt REPLAY_CUT_STEP) >>
               conj_tac >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
                 MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
                 >- REPLAY_CUT_IH_TAC >>
                 conj_tac >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
                   MATCH_ACCEPT_TAC source_create_eval_cut) >>
                 gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
                 conj_tac >- (BETA_TAC >> MATCH_ACCEPT_TAC storage_trace_frame_create) >>
                 REPLAY_SAFETY_TAC) >>
               gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
               conj_tac >- (REPLAY_TRACE_TAC >> MATCH_ACCEPT_TAC storage_trace_frame_create) >>
               REPLAY_SAFETY_TAC) >>
             gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
             conj_tac >- (REPLAY_TRACE_TAC >> MATCH_ACCEPT_TAC storage_trace_frame_create) >>
             REPLAY_SAFETY_TAC)
            (MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
          >- (rpt REPLAY_CUT_STEP) >>
          conj_tac >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
            MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
            >- REPLAY_CUT_IH_TAC >>
            conj_tac >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
              MATCH_MP_TAC source_replay_cut_bind_reachable >> conj_tac
              >- (rpt REPLAY_CUT_STEP) >>
              conj_tac >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
                MATCH_ACCEPT_TAC source_create_eval_cut) >>
              gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
              conj_tac >- (BETA_TAC >> MATCH_ACCEPT_TAC storage_trace_frame_create) >>
              REPLAY_SAFETY_TAC) >>
            gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
            conj_tac >- (REPLAY_TRACE_TAC >> MATCH_ACCEPT_TAC storage_trace_frame_create) >>
            REPLAY_SAFETY_TAC) >>
          gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
          conj_tac >- (REPLAY_TRACE_TAC >> MATCH_ACCEPT_TAC storage_trace_frame_create) >>
          REPLAY_SAFETY_TAC)]) >>
      gen_tac >> conj_tac >- REPLAY_SUFFIX_TAC >>
      conj_tac >- (REPLAY_TRACE_TAC >>
        FIRST [MATCH_ACCEPT_TAC storage_trace_frame_create,
          MATCH_ACCEPT_TAC storage_trace_frame_check_create_blueprint]) >>
      REPLAY_SAFETY_TAC >>
      gvs[vyperCreateTheory.check_create_blueprint_def,
        vyperStateTheory.bind_def, vyperStateTheory.get_accounts_def,
        vyperStateTheory.return_def, vyperStateTheory.raise_def,
        vyperStateTheory.lift_option_def, vyperMiscTheory.option_CASE_rator,
        AllCaseEqs()]))
  >- (ntac 3 gen_tac >> ho_match_mp_tac source_replay_frame_cut >>
      simp[eval_outcomes_suffix_with_results, eval_outcome_prefix_causal_mutual] >>
      simp[cj 49 evaluate_def])
  >- (ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 50 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 2 gen_tac >> rewrite_tac[cj 51 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> rewrite_tac[cj 52 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 53 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 54 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 2 gen_tac >> strip_tac >> rewrite_tac[cj 55 evaluate_def] >>
      rpt REPLAY_CUT_STEP
      >- (MATCH_MP_TAC source_replay_frame_cut >> conj_tac
          >- (irule source_replay_replace_frame >> simp[outcomes_replace_get_place]) >>
          conj_tac
          >- (irule outcomes_suffix_frame >> irule source_replay_replace_frame >>
              simp[outcomes_replace_get_place]) >> rpt PREFIX_STEP)
      >- (irule outcomes_suffix_frame >> irule source_replay_replace_frame >>
          simp[outcomes_replace_get_place]) >>
      MATCH_ACCEPT_TAC storage_trace_frame_get_place)
  >- (ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 56 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 57 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (gen_tac >> rewrite_tac[cj 58 evaluate_def] >>
      rpt REPLAY_CUT_STEP >> gvs[])
  >- (ntac 5 gen_tac >> strip_tac >> rewrite_tac[cj 59 evaluate_def] >>
      rpt REPLAY_CUT_STEP)
  >- (ntac 3 gen_tac >> rewrite_tac[cj 60 evaluate_def] >>
      rpt REPLAY_CUT_STEP >> gvs[])
  >- (ntac 3 gen_tac >> rewrite_tac[cj 61 evaluate_def] >>
      rpt REPLAY_CUT_STEP >> gvs[])
  >- (gen_tac >> rewrite_tac[cj 62 evaluate_def] >>
      rpt REPLAY_CUT_STEP >> gvs[]) >>
  ntac 3 gen_tac >> strip_tac >> rewrite_tac[cj 63 evaluate_def] >>
  rpt REPLAY_CUT_STEP
QED

val _ = clear_overloads_on "source_wrapper_cut_at";

Theorem eval_outcome_probe_replay_mutual:
  (!cx stmt st0 os res_p st_p.
    eval_stmt cx stmt (st0 with outcomes := SOME (os ++ [probe_failed_outcome])) =
      (res_p,st_p) /\ st_p.outcomes = SOME [] ==>
    (\(r,s). (r,erase_storage_trace s))
      (eval_stmt cx stmt (st0 with outcomes := SOME os)) =
    (\(r,s). (r,erase_storage_trace s))
      (eval_stmt cx stmt (st0 with outcomes := SOME
      (os ++ [case eval_stmt cx stmt (st0 with outcomes :=
                    SOME (os ++ [empty_failed_outcome])) of
        (res_e,_) =>
          if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
             res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
             ~NULL st_p.requests
          then failed_outcome (LAST st_p.requests)
          else empty_failed_outcome])))) /\
  (!cx stmts st0 os res_p st_p.
    eval_stmts cx stmts (st0 with outcomes := SOME (os ++ [probe_failed_outcome])) =
      (res_p,st_p) /\ st_p.outcomes = SOME [] ==>
    (\(r,s). (r,erase_storage_trace s))
      (eval_stmts cx stmts (st0 with outcomes := SOME os)) =
    (\(r,s). (r,erase_storage_trace s))
      (eval_stmts cx stmts (st0 with outcomes := SOME
      (os ++ [case eval_stmts cx stmts (st0 with outcomes :=
                    SOME (os ++ [empty_failed_outcome])) of
        (res_e,_) =>
          if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
             res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
             ~NULL st_p.requests
          then failed_outcome (LAST st_p.requests)
          else empty_failed_outcome])))) /\
  (!cx it st0 os res_p st_p.
    eval_iterator cx it (st0 with outcomes := SOME (os ++ [probe_failed_outcome])) =
      (res_p,st_p) /\ st_p.outcomes = SOME [] ==>
    (\(r,s). (r,erase_storage_trace s))
      (eval_iterator cx it (st0 with outcomes := SOME os)) =
    (\(r,s). (r,erase_storage_trace s))
      (eval_iterator cx it (st0 with outcomes := SOME
      (os ++ [case eval_iterator cx it (st0 with outcomes :=
                    SOME (os ++ [empty_failed_outcome])) of
        (res_e,_) =>
          if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
             res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
             ~NULL st_p.requests
          then failed_outcome (LAST st_p.requests)
          else empty_failed_outcome])))) /\
  (!cx tyv id fbody vs st0 os res_p st_p.
    eval_for cx tyv id fbody vs (st0 with outcomes := SOME (os ++ [probe_failed_outcome])) =
      (res_p,st_p) /\ st_p.outcomes = SOME [] ==>
    (\(r,s). (r,erase_storage_trace s))
      (eval_for cx tyv id fbody vs (st0 with outcomes := SOME os)) =
    (\(r,s). (r,erase_storage_trace s))
      (eval_for cx tyv id fbody vs (st0 with outcomes := SOME
      (os ++ [case eval_for cx tyv id fbody vs (st0 with outcomes :=
                    SOME (os ++ [empty_failed_outcome])) of
        (res_e,_) =>
          if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
             res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
             ~NULL st_p.requests
          then failed_outcome (LAST st_p.requests)
          else empty_failed_outcome])))) /\
  (!cx e st0 os res_p st_p.
    eval_expr cx e (st0 with outcomes := SOME (os ++ [probe_failed_outcome])) =
      (res_p,st_p) /\ st_p.outcomes = SOME [] ==>
    (\(r,s). (r,erase_storage_trace s))
      (eval_expr cx e (st0 with outcomes := SOME os)) =
    (\(r,s). (r,erase_storage_trace s))
      (eval_expr cx e (st0 with outcomes := SOME
      (os ++ [case eval_expr cx e (st0 with outcomes :=
                    SOME (os ++ [empty_failed_outcome])) of
        (res_e,_) =>
          if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
             res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
             ~NULL st_p.requests
          then failed_outcome (LAST st_p.requests)
          else empty_failed_outcome])))) /\
  (!cx es st0 os res_p st_p.
    eval_exprs cx es (st0 with outcomes := SOME (os ++ [probe_failed_outcome])) =
      (res_p,st_p) /\ st_p.outcomes = SOME [] ==>
    (\(r,s). (r,erase_storage_trace s))
      (eval_exprs cx es (st0 with outcomes := SOME os)) =
    (\(r,s). (r,erase_storage_trace s))
      (eval_exprs cx es (st0 with outcomes := SOME
      (os ++ [case eval_exprs cx es (st0 with outcomes :=
                    SOME (os ++ [empty_failed_outcome])) of
        (res_e,_) =>
          if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
             res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
             ~NULL st_p.requests
          then failed_outcome (LAST st_p.requests)
          else empty_failed_outcome])))) /\
  (!cx t st0 os res_p st_p.
    eval_base_place cx t (st0 with outcomes := SOME (os ++ [probe_failed_outcome])) =
      (res_p,st_p) /\ st_p.outcomes = SOME [] ==>
    (\(r,s). (r,erase_storage_trace s))
      (eval_base_place cx t (st0 with outcomes := SOME os)) =
    (\(r,s). (r,erase_storage_trace s))
      (eval_base_place cx t (st0 with outcomes := SOME
      (os ++ [case eval_base_place cx t (st0 with outcomes :=
                    SOME (os ++ [empty_failed_outcome])) of
        (res_e,_) =>
          if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
             res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
             ~NULL st_p.requests
          then failed_outcome (LAST st_p.requests)
          else empty_failed_outcome])))) /\
  (!cx t st0 os res_p st_p.
    eval_target_place cx t (st0 with outcomes := SOME (os ++ [probe_failed_outcome])) =
      (res_p,st_p) /\ st_p.outcomes = SOME [] ==>
    (\(r,s). (r,erase_storage_trace s))
      (eval_target_place cx t (st0 with outcomes := SOME os)) =
    (\(r,s). (r,erase_storage_trace s))
      (eval_target_place cx t (st0 with outcomes := SOME
      (os ++ [case eval_target_place cx t (st0 with outcomes :=
                    SOME (os ++ [empty_failed_outcome])) of
        (res_e,_) =>
          if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
             res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
             ~NULL st_p.requests
          then failed_outcome (LAST st_p.requests)
          else empty_failed_outcome])))) /\
  (!cx g v st0 os res_p st_p.
    assign_tuple_targets cx g v (st0 with outcomes := SOME (os ++ [probe_failed_outcome])) =
      (res_p,st_p) /\ st_p.outcomes = SOME [] ==>
    (\(r,s). (r,erase_storage_trace s))
      (assign_tuple_targets cx g v (st0 with outcomes := SOME os)) =
    (\(r,s). (r,erase_storage_trace s))
      (assign_tuple_targets cx g v (st0 with outcomes := SOME
      (os ++ [case assign_tuple_targets cx g v (st0 with outcomes :=
                    SOME (os ++ [empty_failed_outcome])) of
        (res_e,_) =>
          if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
             res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
             ~NULL st_p.requests
          then failed_outcome (LAST st_p.requests)
          else empty_failed_outcome])))) /\
  (!cx gs vs st0 os res_p st_p.
    assign_tuple_target_list cx gs vs (st0 with outcomes := SOME (os ++ [probe_failed_outcome])) =
      (res_p,st_p) /\ st_p.outcomes = SOME [] ==>
    (\(r,s). (r,erase_storage_trace s))
      (assign_tuple_target_list cx gs vs (st0 with outcomes := SOME os)) =
    (\(r,s). (r,erase_storage_trace s))
      (assign_tuple_target_list cx gs vs (st0 with outcomes := SOME
      (os ++ [case assign_tuple_target_list cx gs vs (st0 with outcomes :=
                    SOME (os ++ [empty_failed_outcome])) of
        (res_e,_) =>
          if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
             res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
             ~NULL st_p.requests
          then failed_outcome (LAST st_p.requests)
          else empty_failed_outcome])))) /\
  (!cx es st0 os res_p st_p.
    eval_expr_results cx es (st0 with outcomes := SOME (os ++ [probe_failed_outcome])) =
      (res_p,st_p) /\ st_p.outcomes = SOME [] ==>
    (\(r,s). (r,erase_storage_trace s))
      (eval_expr_results cx es (st0 with outcomes := SOME os)) =
    (\(r,s). (r,erase_storage_trace s))
      (eval_expr_results cx es (st0 with outcomes := SOME
      (os ++ [case eval_expr_results cx es (st0 with outcomes :=
                    SOME (os ++ [empty_failed_outcome])) of
        (res_e,_) =>
          if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
             res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
             ~NULL st_p.requests
          then failed_outcome (LAST st_p.requests)
          else empty_failed_outcome]))))
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  FIRST (map drule (CONJUNCTS eval_outcome_probe_cut_mutual)) >>
  strip_tac >> gvs[] >>
  pairarg_tac >> gvs[SF CONJ_ss] >>
  gvs[pairTheory.pair_CASE_def]
QED
