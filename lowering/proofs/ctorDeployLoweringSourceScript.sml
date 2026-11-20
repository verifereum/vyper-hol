(* Constructor source entry and evaluation at the selected outcomes. *)
Theory ctorDeployLoweringSource
Ancestors
  ctorDeployLoweringDefs vyperState vyperInterpreter vyperScopePreservation
  supportedStmtTraverse supportedExprTraverse e2eDeployDefs
  vyperTypeDeploymentSoundness evalNoHalt vyperStorageTrace

Theorem send_call_value_transport:
  send_call_value mut cx
    (s with <|scopes := scs; outcomes := oc; gas_obs := gobs|>) =
  (FST (send_call_value mut cx s),
   SND (send_call_value mut cx s) with
     <|scopes := scs; outcomes := oc; gas_obs := gobs|>)
Proof
  Cases_on `cx.txn.value = 0` >>
  simp[send_call_value_def, transfer_value_def, COND_RATOR,
    ignore_bind_def, bind_def, check_def, assert_def, get_accounts_def,
    update_accounts_def, return_def, raise_def] >>
  Cases_on `mut = Payable` >>
  simp[bind_def, assert_def, get_accounts_def, update_accounts_def,
    return_def, raise_def, COND_RATOR] >>
  Cases_on `cx.txn.sender = cx.txn.target` >>
  simp[bind_def, assert_def, get_accounts_def, update_accounts_def,
    return_def, raise_def, COND_RATOR] >>
  rpt IF_CASES_TAC >> simp[bind_def, return_def, raise_def, update_accounts_def]
QED

Theorem lock_if_nr_transport:
  lock_if_nr cx nr view
    (s with <|scopes := scs; outcomes := oc; gas_obs := gobs|>) =
  (FST (lock_if_nr cx nr view s),
   SND (lock_if_nr cx nr view s) with
     <|scopes := scs; outcomes := oc; gas_obs := gobs|>)
Proof
  Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[raise_def] >>
  simp[acquire_nonreentrant_lock_def, ignore_bind_def, bind_def,
    record_storage_event_def, get_transient_storage_def, update_transient_def, return_def,
    raise_def, check_not_static_def, check_def, assert_def, COND_RATOR] >>
  rpt IF_CASES_TAC >>
  simp[bind_def, return_def, raise_def, update_transient_def, assert_def] >>
  Cases_on `view` >> simp[]
QED

Theorem send_call_value_scopes:
  send_call_value mut cx s = (r,t) ==> t.scopes = s.scopes
Proof
  Cases_on `cx.txn.value = 0` >> Cases_on `mut = Payable` >>
  simp[send_call_value_def, ignore_bind_def, bind_def, check_def,
       assert_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[transfer_value_scopes]
QED

Theorem lock_if_nr_scopes:
  lock_if_nr cx nr view s = (r,t) ==> t.scopes = s.scopes
Proof
  Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[raise_def] >>
  Cases_on `view` >> Cases_on `cx.txn.is_static` >>
  simp[ignore_bind_def, bind_def, check_not_static_def,
       check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[acquire_nonreentrant_lock_scopes]
QED

Theorem deploy_ctor_prefix_transport:
  ignore_bind (send_call_value mut cx) (lock_if_nr cx nr (is_view_mut mut))
    (initial_state am [env] with <|outcomes := NONE; requests := []|>) =
    (INL (), es0) ==>
  ignore_bind (send_call_value mut cx)
    (ignore_bind (set_scopes [env]) (lock_if_nr cx nr (is_view_mut mut)))
    (initial_state am [FEMPTY] with
      <|outcomes := oc; requests := []; gas_obs := gobs|>) =
    (INL (), es0 with <|gas_obs := gobs; outcomes := oc|>)
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `ignore_bind _ _ s0` >>
  `s0.scopes = [env]` by simp[Abbr `s0`, initial_state_def] >>
  `initial_state am [FEMPTY] with
     <|outcomes := oc; requests := []; gas_obs := gobs|> =
   s0 with <|scopes := [FEMPTY]; gas_obs := gobs; outcomes := oc|>` by
    simp[Abbr `s0`, initial_state_def] >>
  namedCases_on `send_call_value mut cx s0` ["r mid"] >>
  Cases_on `r` >>
  gvs[ignore_bind_def, bind_def, Excl "lock_if_nr_def"] >>
  `mid.scopes = [env]` by metis_tac[send_call_value_scopes] >>
  `es0.scopes = [env]` by metis_tac[lock_if_nr_scopes] >>
  simp[send_call_value_transport, Excl "lock_if_nr_def"] >>
  simp[bind_def, set_scopes_def, return_def, Excl "lock_if_nr_def"] >>
  simp[send_call_value_transport, lock_if_nr_transport,
       Excl "lock_if_nr_def"] >>
  simp[evaluation_state_component_equality]
QED

(* A selected constructor's typed explicit return is NoneV. *)
Theorem deploy_ctor_return_none:
  !tops am tx mut nr body am_c es0 gobs oc v st.
  deploy_source_ok tops am tx /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
  eval_stmts (deploy_evaluation_context tops am tx) body
    (es0 with <|gas_obs := gobs; outcomes := oc|>) =
      (INR (ReturnException v),st) ==> v = NoneV
Proof
  simp[ctorDeployDefsTheory.deploy_source_ok_def, deploy_typing_ok_constants_ready,
    deploy_ctor_start_def, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >> rpt strip_tac >>
  `context_well_typed (deploy_evaluation_context tops am tx)` by
    (gvs[vyperTypeContractSoundnessTheory.call_tx_well_typed_def,
      vyperTypeInvariantsTheory.context_well_typed_def,
      deploy_evaluation_context_def, initial_evaluation_context_def]) >>
  drule deploy_ctor_prefix_transport >>
  disch_then (qspecl_then [`oc`, `gobs`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `eval_stmts cx bdy` >>
  `ignore_bind (send_call_value mut cx)
     (ignore_bind (set_scopes [env])
       (ignore_bind (lock_if_nr cx nr (is_view_mut mut)) (eval_stmts cx bdy)))
     (initial_state am_c [FEMPTY] with
       <|outcomes := oc; requests := []; gas_obs := gobs|>) =
       (INR (ReturnException v),st)` by
    (gvs[ignore_bind_def, bind_def, AllCaseEqs(),
      Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  gvs[lock_if_nr_def, is_view_mut_def] >>
  `cx = (initial_evaluation_context ((tx.target,[(NONE,tops)])::am.sources)
      am.layouts (tx with created_in_tx := T) NONE with in_deploy := T)` by
    simp[Abbr `cx`, deploy_evaluation_context_def] >>
  `ALOOKUP [(NONE,tops)] NONE = SOME tops` by simp[] >>
  qpat_x_assum `supported_program _` kall_tac >>
  qpat_x_assum `checked_deployment_constants_ready _ _ _ _` kall_tac >>
  drule_at (Pat `_ = (INR (ReturnException _),_)`)
    checked_constructor_prefix_return_typed >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`tx.args`, `[]`] mp_tac) >>
  gvs[Abbr `cx`, deploy_evaluation_context_def]
QED

Theorem deploy_source_ctor_not_nr[local]:
  !tops am tx fname mut nr args dflts ret body.
    deploy_source_ok tops am tx /\
    lookup_function NONE fname Deploy tops = SOME (mut,nr,args,dflts,ret,body) ==>
    ~nr
Proof
  rpt strip_tac >>
  drule vyperTypeContractStaticMapsTheory.lookup_function_Deploy_SOME_cases >>
  strip_tac >> gvs[] >>
  gvs[ctorDeployDefsTheory.deploy_source_ok_def, deploy_typing_ok_constants_ready] >>
  qspecl_then [`T`, `am.layouts`, `tx.target`, `[(NONE,tops)]`, `deploy_art`,
      `NONE`, `tops`, `mut`, `T`, `raw`, `fname`, `args`, `dflts`, `ret`, `body'`]
    mp_tac
    (Q.GENL [`in_deploy`, `layouts`, `addr`, `mods`, `art`, `src`, `tls`, `mut`,
        `nr`, `rr`, `name`, `args`, `dflts`, `ret`, `body`]
      vyperTypeContractTheory.check_contract_deploy_nonreentrant) >>
  simp[]
QED

Theorem load_contract_trace_selected:
  !tops am tx orc gobs imms am0 cx mut nr args dflts ret body r am' rqs obs.
    initial_immutables (type_env_all_modules [(NONE, tops)])
      [(NONE, tops)] = SOME imms /\
    am0 = (am with <| immutables updated_by CONS (tx.target, imms);
                     exports updated_by CONS (tx.target, []) |>) /\
    cx = deploy_evaluation_context tops am tx /\
    lookup_function NONE tx.function_name Deploy tops =
      SOME (mut, nr, args, dflts, ret, body) /\
    call_external_function_trace orc gobs am0 cx nr mut tops [(NONE, tops)]
      args dflts tx.args body ret = (r, am', rqs, obs)
    ==>
    load_contract_trace orc gobs am tx [(NONE, tops)] [] =
      ((case r of
          INR HaltException => INL (finalize_pending_deletions am', rqs)
        | INR exn => INR exn
        | INL v => INL (finalize_pending_deletions
            (am' with sources updated_by CONS (tx.target, [(NONE, tops)])), rqs)),
       obs)
Proof
  rpt gen_tac >> strip_tac >>
  `deploy_evaluation_context tops
      (am with <|exports updated_by CONS (tx.target,[]);
                 immutables updated_by CONS (tx.target,imms)|>) tx = cx` by
    gvs[deploy_evaluation_context_def] >>
  qpat_x_assum `am0 = _` SUBST_ALL_TAC >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  fs[load_contract_trace_def, GSYM deploy_evaluation_context_def] >>
  Cases_on `r` >> gvs[] >>
  rename1 `_ = (INR exn, am', rqs, obs)` >> Cases_on `exn` >> gvs[]
QED

Theorem deploy_ctor_source_run:
  !tops am tx mut nr body am_c es0 gobs oc res st.
    deploy_source_ok tops am tx /\ tx.function_name = "__init__" /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) /\
    eval_stmts (deploy_evaluation_context tops am tx) body
      (es0 with <| gas_obs := gobs; outcomes := oc |>) = (res, st) ==>
    load_contract oc gobs am tx [(NONE, tops)] [] =
      (if res = INR HaltException then
         INL (finalize_pending_deletions
           (abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st),
           st.requests)
       else deploy_ctor_finish tops tx (deploy_evaluation_context tops am tx)
              nr mut am_c res st)
Proof
  rpt gen_tac >> strip_tac >>
  `!v. res = INR (ReturnException v) ==> v = NoneV` by
    (rpt strip_tac >> irule deploy_ctor_return_none >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     qexistsl [`gobs`, `oc`, `st`] >> gvs[]) >>
  gvs[deploy_ctor_start_def, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  drule deploy_ctor_prefix_transport >>
  disch_then (qspecl_then [`oc`, `gobs`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `eval_stmts cx bdy` >>
  `ignore_bind (send_call_value mut cx)
     (ignore_bind (set_scopes [env])
       (ignore_bind (lock_if_nr cx nr (is_view_mut mut)) (eval_stmts cx bdy)))
     (initial_state am_c [FEMPTY] with
       <|outcomes := oc; requests := []; gas_obs := gobs|>) = (res,st)` by
    (gvs[ignore_bind_def, bind_def, AllCaseEqs(),
      Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  `deploy_evaluation_context tops
      (am with <|exports updated_by CONS (tx.target,[]);
        immutables updated_by CONS (tx.target,imms)|>) tx = cx` by
    simp[Abbr `cx`, deploy_evaluation_context_def] >>
  `cx.in_deploy /\ cx.txn = tx with created_in_tx := T` by
    simp[Abbr `cx`, deploy_evaluation_context_def, initial_evaluation_context_def] >>
  `bind (eval_external_defaults cx [])
      (\dflt_vs. case bind_arguments (type_env_all_modules [(NONE,tops)]) args
          (tx.args ++ dflt_vs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME env => ignore_bind (set_scopes [env])
          (ignore_bind (lock_if_nr cx nr (is_view_mut mut)) (eval_stmts cx bdy))) =
    ignore_bind (set_scopes [env])
      (ignore_bind (lock_if_nr cx nr (is_view_mut mut)) (eval_stmts cx bdy))` by
    simp[FUN_EQ_THM, bind_def, eval_external_defaults_nil] >>
  (* The constructor is never nonreentrant, so the lock and unlock are
     returns. *)
  `~nr` by metis_tac[deploy_source_ctor_not_nr] >>
  (* The trace semantics seeds the run's storage_trace with the constant
     evaluation's observations; the body carries it along. *)
  qpat_x_assum `evaluate_all_constants _ _ _ _ = _` mp_tac >>
  simp_tac std_ss [evaluate_all_constants_def, evaluate_module_constants_def] >>
  qmatch_goalsub_abbrev_tac `FST ctrace = SOME am_c` >>
  Cases_on `ctrace` >> simp_tac std_ss [] >>
  disch_then SUBST_ALL_TAC >>
  qpat_x_assum `Abbrev _`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  rename1 `_ = (SOME am_c, obs)` >>
  `storage_trace_frame (ignore_bind (send_call_value mut cx)
     (ignore_bind (set_scopes [env])
       (ignore_bind (lock_if_nr cx nr (is_view_mut mut)) (eval_stmts cx bdy))))` by
    (irule storage_trace_frame_ignore_bind >>
     conj_tac >- MATCH_ACCEPT_TAC send_call_value_storage_trace_frame >>
     irule storage_trace_frame_ignore_bind >>
     conj_tac >- MATCH_ACCEPT_TAC (cj 6 storage_trace_frame_state_updates) >>
     irule storage_trace_frame_ignore_bind >>
     conj_tac >- MATCH_ACCEPT_TAC (cj 1 storage_trace_frame_optional_locks) >>
     MATCH_ACCEPT_TAC (cj 2 evaluate_storage_trace_frame)) >>
  `ignore_bind (send_call_value mut cx)
     (ignore_bind (set_scopes [env])
       (ignore_bind (lock_if_nr cx nr (is_view_mut mut)) (eval_stmts cx bdy)))
     (initial_state am_c [FEMPTY] with
       <|outcomes := oc; requests := []; gas_obs := gobs;
         storage_trace := obs|>) =
   (res, st with storage_trace := obs ++ st.storage_trace)` by
    (drule_all storage_trace_frame_result >>
     disch_then (qspec_then `obs` mp_tac) >>
     simp[initial_state_def]) >>
  `bind (eval_external_defaults cx [])
      (\dflt_vs. case bind_arguments (type_env_all_modules [(NONE,tops)]) args
          (tx.args ++ dflt_vs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME env => ignore_bind (set_scopes [env])
          (ignore_bind (return ()) (eval_stmts cx bdy))) =
    ignore_bind (set_scopes [env])
      (ignore_bind (return ()) (eval_stmts cx bdy))` by
    simp[FUN_EQ_THM, bind_def] >>
  qpat_x_assum `_ (initial_state _ _ with
       <|outcomes := oc; requests := []; gas_obs := gobs;
         storage_trace := obs|>) = _` mp_tac >>
  simp[load_contract_def, load_contract_trace_def,
    call_external_function_trace_def,
    abstract_machine_from_state_storage_trace,
    lock_if_nr_def, unlock_if_nr_def, return_def,
    GSYM deploy_evaluation_context_def,
    eval_external_defaults_nil] >>
  strip_tac >>
  Cases_on `res`
  >- (Cases_on `x` >>
      simp[deploy_ctor_finish_def, unlock_if_nr_def, return_def,
           abstract_machine_from_state_storage_trace]) >>
  rename1 `INR ex` >> Cases_on `ex` >>
  gvs[deploy_ctor_finish_def, unlock_if_nr_def, return_def,
      abstract_machine_from_state_storage_trace,
      vyperValueOperationTheory.safe_cast_def]
QED
