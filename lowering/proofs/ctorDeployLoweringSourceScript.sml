(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringSource
Ancestors
  ctorDeployLoweringDefs vyperState vyperInterpreter vyperScopePreservation
  supportedStmtTraverse supportedExprTraverse e2eDeployDefs
  vyperTypeDeploymentSoundness evalNoHalt vyperEvalOutcomeReplace vyperStorageTrace

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

(* load_contract is deploy_ctor_finish of the constructor body's run from
   deploy_ctor_start, at any gas observations.  The body is call-free
   (constructor_call_free), so it never reads the call outcomes: a run with
   any outcomes field gives the same result. *)
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
  qpat_x_assum `constructor_call_free _` kall_tac >>
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

Theorem deploy_ctor_source_run_none:
  !tops am tx mut nr body am_c es0 gobs res st.
    deploy_source_ok tops am tx /\ tx.function_name = "__init__" /\
    deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
    eval_stmts (deploy_evaluation_context tops am tx) body
      (es0 with <|gas_obs := gobs; outcomes := NONE|>) = (res,st) ==>
    load_contract NONE gobs am tx [(NONE,tops)] [] =
      deploy_ctor_finish tops tx (deploy_evaluation_context tops am tx)
        nr mut am_c res st
Proof
  rpt gen_tac >> strip_tac >>
  `!v. res = INR (ReturnException v) ==> v = NoneV` by
    (rpt strip_tac >> irule deploy_ctor_return_none >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     qexistsl [`gobs`, `NONE`, `st`] >> gvs[]) >>
  `res <> INR HaltException` by
    (strip_tac >>
     gvs[ctorDeployDefsTheory.deploy_source_ok_def, deploy_ctor_start_def,
         Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
     rename1 `lookup_function NONE _ Deploy tops = SOME (_,_,_,_,_,cbody)` >>
     `get_module_code (deploy_evaluation_context tops am tx) NONE = SOME tops` by
       simp[deploy_evaluation_context_def, vyperInterpreterTheory.initial_evaluation_context_def,
            vyperContextTheory.get_module_code_def] >>
     `!st st'. eval_stmts (deploy_evaluation_context tops am tx) cbody st <>
               (INR HaltException, st')` by
       (rpt gen_tac >> irule deploy_body_no_halt >> metis_tac[]) >>
     metis_tac[]) >>
  gvs[deploy_ctor_start_def, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  drule deploy_ctor_prefix_transport >>
  disch_then (qspecl_then [`NONE`, `gobs`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `eval_stmts cx bdy` >>
  `ignore_bind (send_call_value mut cx)
     (ignore_bind (set_scopes [env])
       (ignore_bind (lock_if_nr cx nr (is_view_mut mut)) (eval_stmts cx bdy)))
     (initial_state am_c [FEMPTY] with
       <|outcomes := NONE; requests := []; gas_obs := gobs|>) = (res,st)` by
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
       <|outcomes := NONE; requests := []; gas_obs := gobs;
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
       <|outcomes := NONE; requests := []; gas_obs := gobs;
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

Theorem deploy_ctor_finish_outcomes:
  deploy_ctor_finish tops tx cx nr mut am_c res (st with outcomes := oc) =
  deploy_ctor_finish tops tx cx nr mut am_c res st
Proof
  Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
  simp[deploy_ctor_finish_def, unlock_if_nr_def,
    release_nonreentrant_lock_def, update_transient_def,
    ignore_bind_def, bind_def, record_storage_event_def,
    return_def, raise_def, abstract_machine_from_state_def] >>
  Cases_on `mut` >>
  simp[bind_def, get_transient_storage_def, update_transient_def,
    record_storage_event_def, return_def, abstract_machine_from_state_def]
QED

Theorem outcomes_replace_evaluate_call_free:
  (!cx stmt. ~supported_stmt_expr_exists constructor_call_root stmt ==>
    !s oc. eval_stmt cx stmt (s with outcomes := oc) =
      (FST (eval_stmt cx stmt s), SND (eval_stmt cx stmt s) with outcomes := oc)) /\
  (!cx body. ~supported_stmts_expr_exists constructor_call_root body ==>
    !s oc. eval_stmts cx body (s with outcomes := oc) =
      (FST (eval_stmts cx body s), SND (eval_stmts cx body s) with outcomes := oc)) /\
  (!cx it. ~supported_iterator_exists constructor_call_root it ==>
    !s oc. eval_iterator cx it (s with outcomes := oc) =
      (FST (eval_iterator cx it s), SND (eval_iterator cx it s) with outcomes := oc)) /\
  (!cx ty nm body vs. ~supported_stmts_expr_exists constructor_call_root body ==>
    !s oc. eval_for cx ty nm body vs (s with outcomes := oc) =
      (FST (eval_for cx ty nm body vs s), SND (eval_for cx ty nm body vs s) with outcomes := oc)) /\
  (!cx e. ~supported_expr_exists constructor_call_root e ==>
    !s oc. eval_expr cx e (s with outcomes := oc) =
      (FST (eval_expr cx e s), SND (eval_expr cx e s) with outcomes := oc)) /\
  (!cx es. ~supported_exprs_exists constructor_call_root es ==>
    !s oc. eval_exprs cx es (s with outcomes := oc) =
      (FST (eval_exprs cx es s), SND (eval_exprs cx es s) with outcomes := oc)) /\
  (!cx target. ~supported_target_exists constructor_call_root target ==>
    !s oc. eval_base_place cx target (s with outcomes := oc) =
      (FST (eval_base_place cx target s), SND (eval_base_place cx target s) with outcomes := oc)) /\
  (!cx target. ~supported_target_exists constructor_call_root target ==>
    !s oc. eval_target_place cx target (s with outcomes := oc) =
      (FST (eval_target_place cx target s), SND (eval_target_place cx target s) with outcomes := oc)) /\
  (!cx target v. ~supported_assignment_exists constructor_call_root target ==>
    !s oc. assign_tuple_targets cx target v (s with outcomes := oc) =
      (FST (assign_tuple_targets cx target v s), SND (assign_tuple_targets cx target v s) with outcomes := oc)) /\
  (!cx targets vs. ~supported_assignments_exists constructor_call_root targets ==>
    !s oc. assign_tuple_target_list cx targets vs (s with outcomes := oc) =
      (FST (assign_tuple_target_list cx targets vs s), SND (assign_tuple_target_list cx targets vs s) with outcomes := oc)) /\
  (!cx es. ~supported_exprs_exists constructor_call_root es ==>
    !s oc. eval_expr_results cx es (s with outcomes := oc) =
      (FST (eval_expr_results cx es s), SND (eval_expr_results cx es s) with outcomes := oc))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[supported_stmt_expr_exists_def, supported_expr_exists_def,
    supported_assignment_exists_def, supported_iterator_exists_def,
    supported_assert_exists_def, supported_raise_exists_def,
    constructor_call_root_def] >>
  rpt strip_tac >> map_every qid_spec_tac [`oc`, `s`] >>
  gvs[] >> once_rewrite_tac[evaluate_def] >>
  simp[outcomes_replace_lookup_global, outcomes_replace_lookup_flag_mem,
    return_def, raise_def]
  >~ [`builtin_args_length_ok bt (LENGTH es)`]
  >- (match_mp_tac outcomes_replace_ignore_bind_guarded >>
      simp[outcomes_replace_basic] >>
      rpt gen_tac >> strip_tac >>
      match_mp_tac outcomes_replace_bind >> conj_tac
      >- (Cases_on `bt = Len`
          >- (gvs[] >> match_mp_tac outcomes_replace_bind >> conj_tac
              >- (first_x_assum irule >> reverse conj_tac
                  >- (goal_assum (drule_at Any)) >>
                  Cases_on `es` >>
                  gvs[type_check_def, assert_def, raise_def,
                      vyperContextTheory.builtin_args_length_ok_def,
                      supported_exprs_exists_every]) >>
              simp[outcomes_replace_bind, outcomes_replace_result_array_length,
                   return_def]) >>
          Cases_on `bt = Bop In \/ bt = Bop NotIn`
          >- (gvs[] >>
              (match_mp_tac outcomes_replace_bind >> conj_tac
               >- metis_tac[] >>
               simp[outcomes_replace_ignore_bind, outcomes_replace_bind,
                    outcomes_replace_basic, outcomes_replace_lifts])) >>
          Cases_on `bt = Env MsgGas`
          >- gvs[outcomes_replace_next_gas_reading] >>
          gvs[] >> match_mp_tac outcomes_replace_bind >> conj_tac
          >- (Cases_on `code_slice_source bt es` >> simp[]
              >- metis_tac[] >>
              rename1 `code_slice_source bt es = SOME csa` >> PairCases_on `csa` >>
              `~supported_exprs_exists constructor_call_root (TL es) /\
               ~supported_expr_exists constructor_call_root csa1` by
                (qpat_x_assum `~supported_exprs_exists _ es` mp_tac >>
                 qpat_x_assum `code_slice_source _ _ = SOME _` mp_tac >>
                 rpt (pop_assum kall_tac) >>
                 rw[code_slice_source_SOME] >>
                 gvs[supported_expr_exists_def, constructor_call_root_def]) >>
              `!s oc. eval_exprs cx (TL es) (s with outcomes := oc) =
                 (FST (eval_exprs cx (TL es) s),
                  SND (eval_exprs cx (TL es) s) with outcomes := oc)` by metis_tac[] >>
              `!s0 v t. eval_exprs cx (TL es) s0 = (INL v,t) ==>
                 !s oc. eval_exprs cx [csa1] (s with outcomes := oc) =
                   (FST (eval_exprs cx [csa1] s),
                    SND (eval_exprs cx [csa1] s) with outcomes := oc)` by metis_tac[] >>
              map_every qid_spec_tac [`oc`, `s`] >> simp_tac (srw_ss()) [] >>
              irule outcomes_replace_bind_guarded >> conj_tac >> simp[] >>
              rpt strip_tac >>
              qpat_x_assum `!s0 v t. eval_exprs cx (TL es) s0 = _ ==> _` drule >>
              strip_tac >>
              irule outcomes_replace_bind >> simp[] >> rpt gen_tac >>
              irule outcomes_replace_bind >> simp[outcomes_replace_basic] >>
              rpt gen_tac >>
              irule outcomes_replace_bind >>
              simp[outcomes_replace_lifts, outcomes_replace_basic, return_def]) >>
          simp[outcomes_replace_bind, outcomes_replace_ignore_bind,
               outcomes_replace_basic, outcomes_replace_lifts,
               outcomes_replace_precompile_call_success, return_def]) >>
      simp[return_def]) >>
  simp_tac (srw_ss()) [outcomes_replace_basic, outcomes_replace_lifts,
    return_def, raise_def] >>
  rpt (FIRST [first_assum ACCEPT_TAC,
      goal_assum (drule_at Any),
      first_assum (fn th => irule th >> rpt conj_tac >>
        FIRST [goal_assum (drule_at Any) >> NO_TAC,
               gvs[] >> NO_TAC]),
      (first_assum irule >> goal_assum (drule_at Any)),
      irule outcomes_replace_bind_guarded,
      irule outcomes_replace_ignore_bind_guarded,
      irule outcomes_replace_finally_guarded,
      irule outcomes_replace_try_guarded,
      irule outcomes_replace_switch_BoolV,
      IF_CASES_TAC,
      conj_tac, gen_tac, disch_tac] >>
    simp[outcomes_replace_basic, outcomes_replace_lifts,
      outcomes_replace_read_result, outcomes_replace_read_place,
      outcomes_replace_place_type_value, outcomes_replace_write_place,
      outcomes_replace_new_variable, outcomes_replace_scopes,
      outcomes_replace_handlers, outcomes_replace_append_place,
      outcomes_replace_pop_place, outcomes_replace_select_result,
      outcomes_replace_extend_place, outcomes_replace_get_place,
      outcomes_replace_result_array_length, outcomes_replace_conditional_result,
      outcomes_replace_next_gas_reading, return_def, raise_def])
  (* the seven goals left: two custom errors, a tuple-target value, struct
     fields, the array iterator, the for loop, a builtin arity clash *)
  >>~- ([`order_custom_error_args`],
    (Cases_on `err` >> simp[] >>
        rpt BasicProvers.TOP_CASE_TAC >> simp[raise_def] >>
        drule vyperASTTheory.order_custom_error_args_perm >> strip_tac >>
        rename1 `order_custom_error_args params (CustomError id pos kws) = SOME es` >>
        `~supported_exprs_exists constructor_call_root es` by
          (simp[supported_exprs_exists_every] >>
           metis_tac[sortingTheory.PERM_EVERY]) >>
        gvs[] >>
        `!s oc. eval_exprs cx es (s with outcomes := oc) =
          (FST (eval_exprs cx es s), SND (eval_exprs cx es s) with outcomes := oc)` by
          metis_tac[] >>
        map_every qid_spec_tac [`oc`, `s`] >>
        irule outcomes_replace_bind >> simp[] >> gen_tac >>
        irule outcomes_replace_bind >> simp[outcomes_replace_lifts, raise_def]))
  >~ [`TupleV _`]
  >- (Cases_on `v` >> simp[raise_def] >> Cases_on `a` >> gvs[raise_def])
  >~ [`eval_exprs _ (MAP SND _)`]
  >- (gvs[supported_fields_exists_every, supported_exprs_exists_every,
          listTheory.EVERY_MAP] >>
      metis_tac[outcomes_replace_array_iterator_results])
  >~ [`array_iterator_results _ _ _ (_ with outcomes := _)`]
  >- metis_tac[outcomes_replace_array_iterator_results]
  >~ [`eval_for _ _ _ _ _ (_ with outcomes := _)`]
  >- metis_tac[]
  >> Cases_on `es` >>
  gvs[type_check_def, assert_def, raise_def,
      vyperContextTheory.builtin_args_length_ok_def,
      supported_exprs_exists_every]
QED

Theorem deploy_ctor_source_run:
  !tops am tx mut nr body am_c es0 gobs oc res st.
    deploy_source_ok tops am tx /\ tx.function_name = "__init__" /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) /\
    eval_stmts (deploy_evaluation_context tops am tx) body
      (es0 with <| gas_obs := gobs; outcomes := oc |>) = (res, st) ==>
    load_contract NONE gobs am tx [(NONE, tops)] [] =
      deploy_ctor_finish tops tx (deploy_evaluation_context tops am tx) nr mut am_c res st
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `deploy_ctor_start tops am tx (mut,nr,bdy,am_c,es0)` >>
  `~supported_stmts_expr_exists constructor_call_root bdy` by
    (gvs[ctorDeployDefsTheory.deploy_source_ok_def,
       constructor_call_free_def, deploy_ctor_start_def,
       Excl "lock_if_nr_def", Excl "is_view_mut_def"] >> metis_tac[]) >>
  drule (cj 2 outcomes_replace_evaluate_call_free) >>
  disch_then (qspecl_then
    [`deploy_evaluation_context tops am tx`,
     `es0 with <|gas_obs := gobs; outcomes := oc|>`, `NONE`] mp_tac) >>
  simp[] >> strip_tac >>
  `load_contract NONE gobs am tx [(NONE,tops)] [] =
    deploy_ctor_finish tops tx (deploy_evaluation_context tops am tx)
      nr mut am_c res (st with outcomes := NONE)` by
    (irule deploy_ctor_source_run_none >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  gvs[deploy_ctor_finish_outcomes]
QED
