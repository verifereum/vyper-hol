(* Internal calls: actuals are supplied by the expression induction;
   defaults are empty and callable bodies have a separately proved contract. *)
Theory bodyOracleCallStorage
Ancestors
  list pair sum option finite_map
  exprOracleStorageInterfaces stmtOracleStoragePreservation bodyStorageSyntax
  supportedProgram supportedStmts supportedStmtTraverse
  vyperAST vyperState vyperInterpreter vyperContext vyperTypeSystem
  vyperTypeEvalStoragePreservation vyperTypeEvalSoundness vyperTypeBindArguments
  vyperTypeStoragePreservation vyperCallOutcomeStorage vyperEvalOutcomeSuffix
  vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperTypeExprSoundness vyperTypeInvariants vyperTypeExprResult vyperTypeEnv
  vyperEvalMisc vyperStatePreservation vyperValue
Libs monadsyntax

Definition oracle_body_storage_def:
  oracle_body_storage cx fn_body <=>
    !env ret_ty env_after st res rt.
      type_stmts env ret_ty fn_body = SOME env_after /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_stmts fn_body) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_stmts cx fn_body st = (res,rt) ==>
      contract_storage_well_formed cx rt
End

Theorem oracle_body_storage_supported:
  supported_stmts tops bindings fn_body /\
  ~supported_stmts_expr_exists expr_evm_run_root fn_body /\
  EVERY (oracle_internal_call_storage cx) (int_calls_stmts fn_body) ==>
  oracle_body_storage cx fn_body
Proof
  rw[oracle_body_storage_def] >>
  drule_all (cj 2 eval_stmts_oracle_storage_mutual) >> simp[]
QED

Theorem oracle_empty_defaults[local]:
  finally (do set_scopes [FEMPTY]; eval_exprs cxd [] od) (set_scopes prev) st =
  (INL [], st with scopes := prev)
Proof
  simp[Once evaluate_def,finally_def,bind_def,ignore_bind_def,set_scopes_def,return_def]
QED

Theorem oracle_call_frame_runtime[local]:
  runtime_storage_consistent env cx st /\ functions_well_typed cx /\
  env_body.current_src = src /\ env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\ env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members /\ scope_well_typed call_env /\
  env_scopes_consistent env_body cx (st with scopes := [call_env]) ==>
  runtime_storage_consistent env_body (cx with stk updated_by CONS (src,fn))
    (st with scopes := [call_env]) /\
  functions_well_typed (cx with stk updated_by CONS (src,fn))
Proof
  strip_tac >>
  `runtime_consistent env cx st /\ contract_storage_well_formed cx st /\
   storage_layout_safe cx` by fs[runtime_storage_consistent_def] >>
  `env_consistent env cx st /\ state_well_typed st /\
   accounts_well_typed st.accounts` by fs[runtime_consistent_def] >>
  `runtime_storage_consistent (defaults_env env_body)
     (cx with stk updated_by CONS (src,fn)) (st with scopes := [FEMPTY]) /\
   functions_well_typed (cx with stk updated_by CONS (src,fn))` by
    (irule intcall_defaults_runtime_storage_consistent >> simp[] >>
     qexists_tac `env` >> simp[]) >>
  `env_immutables_consistent (defaults_env env_body)
     (cx with stk updated_by CONS (src,fn)) (st with scopes := [FEMPTY]) /\
   context_well_typed (cx with stk updated_by CONS (src,fn))` by
    fs[runtime_storage_consistent_def,runtime_consistent_def,env_consistent_def] >>
  `env_immutables_consistent env_body (cx with stk updated_by CONS (src,fn)) st` by
    (mp_tac (Q.INST [`env` |-> `env_body`, `cx` |-> `cx with stk updated_by CONS (src,fn)`,
                      `st` |-> `st with scopes := [FEMPTY]`, `scopes` |-> `st.scopes`]
               env_immutables_consistent_defaults_scopes_storage) >> simp[]) >>
  qspecl_then [`env`, `env_body`, `cx`, `st`, `st`, `st`, `call_env`, `fn`, `F`, `F`]
    mp_tac intcall_live_pushed_body_preconditions >>
  (impl_tac >- simp[return_def,env_scopes_consistent_stk_irrelevant_storage]) >> strip_tac >>
  simp[runtime_storage_consistent_def,runtime_consistent_def,
       contract_storage_well_formed_stk_scopes] >>
  qpat_x_assum `env_consistent env_body _ _` mp_tac >> simp[]
QED

Theorem oracle_internal_call_from_bodies:
  get_module_code cx src = SOME tops /\
  (!mut nr params dflts ret fn_body.
    lookup_callable_function cx.in_deploy fn tops =
      SOME (mut,nr,params,dflts,ret,fn_body) ==>
    ~nr /\ dflts = [] /\
    oracle_body_storage (cx with stk updated_by CONS (src,fn)) fn_body) ==>
  oracle_internal_call_storage cx (src,fn)
Proof
  strip_tac >> rw[oracle_internal_call_storage_def] >>
  `runtime_consistent env cx st /\ contract_storage_well_formed cx st /\
   storage_layout_safe cx` by fs[runtime_storage_consistent_def] >>
  `env_consistent env cx st` by fs[runtime_consistent_def] >>
  `fn_sigs_consistent env.fn_sigs cx` by
    fs[env_consistent_def,env_context_consistent_def] >>
  qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  drule_all fn_sigs_consistent_FLOOKUP_storage >> strip_tac >> gvs[] >>
  rename1 `lookup_callable_function cx.in_deploy fn tops = SOME (mut,F,params,[],sig.ret_ty,fn_body)` >>
  `LENGTH es = LENGTH params` by decide_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (drule intcall_call_evaluation_safe_args_storage >> simp[]) >>
  Cases_on `MEM (src,fn) cx.stk`
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def,type_check_def,assert_def,raise_def,ignore_bind_def,bind_def] >>
      strip_tac >> gvs[]) >>
  Cases_on `eval_expr_results cx es st` >>
  rename1 `eval_expr_results cx es st = (actual_res,args_st)` >>
  `contract_storage_well_formed cx args_st` by
    fs[] >>
  reverse (Cases_on `actual_res`)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def,type_check_def,assert_def,return_def,raise_def,
           ignore_bind_def,bind_def,lift_option_type_def] >> strip_tac >> gvs[]) >>
  rename1 `eval_expr_results cx es st = (INL actual_results,args_st)` >>
  `runtime_consistent env cx args_st` by
    (drule_all eval_expr_results_preserves_runtime_consistent_from_eval >> simp[]) >>
  `expr_results_typed (env,cx,args_st) es actual_results` by
    (drule_all eval_expr_results_success_typed >> simp[]) >>
  `env_consistent env cx args_st` by fs[runtime_consistent_def] >>
  `runtime_storage_consistent env cx args_st` by fs[runtime_storage_consistent_def] >>
  suspend "callable_typing_and_binding"
QED

Resume oracle_internal_call_from_bodies[callable_typing_and_binding]:
  mp_tac (Q.INST [`st` |-> `args_st`, `ts` |-> `tops`, `fm` |-> `mut`,
                  `nr` |-> `F`, `args` |-> `params`, `dflts` |-> `[] : expr list`,
                  `ret` |-> `sig.ret_ty`, `fn_body` |-> `fn_body`,
                  `src_id_opt` |-> `src`]
            callable_body_typing_from_env_consistent) >>
  simp[] >>
  disch_then (qx_choose_then `env_body` (qx_choose_then `ret_tv`
    (qx_choose_then `env_after` (fn th => map_every assume_tac (CONJUNCTS th))))) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,type_check_def,assert_def,return_def,raise_def,
       ignore_bind_apply,bind_apply,lift_option_type_def,get_scopes_def,
       oracle_empty_defaults] >>
  Cases_on `read_results cx actual_results args_st` >>
  rename1 `read_results cx actual_results args_st = (read_res,read_st)` >>
  drule read_results_state >> disch_then SUBST_ALL_TAC >>
  reverse (Cases_on `read_res`)
  >- (simp[] >> strip_tac >> gvs[]) >>
  rename1 `read_results cx actual_results args_st = (INL actual_vs,args_st)` >>
  `state_well_typed args_st` by fs[runtime_consistent_def] >>
  `exprs_runtime_typed env es actual_vs` by
    (drule_all read_results_typed >> simp[]) >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def,env_context_consistent_def] >>
  mp_tac (Q.SPECL [`cx`, `env`, `env_body`, `params`, `[] : expr list`, `es`,
                  `actual_vs`, `[] : value list`, `[] : expr list`, `args_st`]
             intcall_bind_arguments_from_runtime_typed) >>
  (impl_tac >- (simp[exprs_runtime_typed_def,defaults_env_def] >> metis_tac[])) >>
  disch_then (qx_choose_then `call_env` (fn th => map_every assume_tac (CONJUNCTS th))) >>
  qpat_x_assum `bind_arguments _ _ _ = _` (assume_tac o REWRITE_RULE[APPEND_NIL]) >>
  simp[push_function_def,return_def] >> strip_tac >>
  `runtime_storage_consistent env_body (cx with stk updated_by CONS (src,fn))
     (args_st with scopes := [call_env]) /\
   functions_well_typed (cx with stk updated_by CONS (src,fn))` by
    (drule_all oracle_call_frame_runtime >> simp[]) >>
  suspend "body_and_cleanup"
QED

Resume oracle_internal_call_from_bodies[body_and_cleanup]:
  `call_evaluation_safe (cx with stk updated_by CONS (src,fn)) (int_calls_stmts fn_body)` by
    (drule_all intcall_call_evaluation_safe_body_storage >> simp[]) >>
  `IS_SOME args_st.outcomes /\ oracle_storage_ok cx args_st` by
    (irule oracle_storage_entry_suffix >> qexists_tac `st` >> simp[] >>
     drule eval_expr_results_outcome_suffix >> simp[]) >>
  `oracle_storage_ok (cx with stk updated_by CONS (src,fn))
     (args_st with scopes := [call_env])` by
    fs[oracle_storage_ok_stk,oracle_storage_ok_payload] >>
  `!bres bst. eval_stmts (cx with stk updated_by CONS (src,fn)) fn_body
      (args_st with scopes := [call_env]) = (bres,bst) ==>
      contract_storage_well_formed cx bst` by
    (rpt strip_tac >>
     qpat_x_assum `oracle_body_storage _ _`
       (mp_tac o Q.SPECL [`env_body`, `sig.ret_ty`, `env_after`,
                          `args_st with scopes := [call_env]`, `bres`, `bst`] o
        REWRITE_RULE[oracle_body_storage_def]) >>
     simp[contract_storage_well_formed_stk]) >>
  qspecl_then [`cx`, `cx with stk updated_by CONS (src,fn)`, `fn_body`,
               `args_st with scopes := [call_env]`, `args_st.scopes`, `F`, `F`,
               `ret_tv`, `res`, `rt`] mp_tac
    intcall_post_push_expanded_suffix_preserves_contract_storage_well_formed >>
  (impl_tac >- simp[contract_storage_well_formed_scopes]) >> simp[]
QED

Finalise oracle_internal_call_from_bodies

(* Supported internal declarations cannot themselves make internal calls. *)
Theorem supported_internal_callee_storage:
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  storage_internal_callee tops callee ==>
  oracle_internal_call_storage cx callee
Proof
  PairCases_on `callee` >> strip_tac >>
  drule storage_internal_callee_lookup >> strip_tac >> gvs[] >>
  irule oracle_internal_call_from_bodies >> qexists_tac `tops` >> simp[] >>
  rpt strip_tac >>
  Cases_on `lookup_function NONE callee1 Internal tops` >>
  gvs[lookup_callable_function_def] >>
  drule_at (Pat `lookup_function _ _ _ _ = _`) storage_supported_lookup >>
  simp[] >> strip_tac >> gvs[] >>
  drule oracle_body_storage_supported >> simp[]
QED

(* This also covers deployment lookup and its empty default constructor.
   Deployment bodies may call supported internal declarations, whose contracts
   above are already available independently of deployment bodies. *)
Theorem supported_main_callee_storage:
  supported_program tops /\ get_module_code cx NONE = SOME tops ==>
  oracle_internal_call_storage cx (NONE,fn)
Proof
  strip_tac >> irule oracle_internal_call_from_bodies >>
  qexists_tac `tops` >> simp[] >> rpt strip_tac >>
  drule_all storage_supported_callable_lookup >> strip_tac >> gvs[] >>
  `EVERY (oracle_internal_call_storage (cx with stk updated_by CONS (NONE,fn)))
     (int_calls_stmts fn_body)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     irule supported_internal_callee_storage >> qexists_tac `tops` >>
     fs[get_module_code_def]) >>
  drule oracle_body_storage_supported >> simp[]
QED
