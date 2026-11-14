(* Source outcome-consuming-step horizon, shared by call and deployment. *)
Theory sourceCallCount
Ancestors
  vyperInterpreter vyperCallOutcome extCallOracle vyperRuntimeAccounts
  finite_map list option pair vyperTypeDeploymentMachine vyperStorageTrace
Libs BasicProvers

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
