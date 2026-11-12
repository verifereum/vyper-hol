Theory targetGuardedInternalCallStorageFrame
Ancestors
  vyperMachineFrame bodyIntCallSource targetInternalCallStorageFrame vyperCallOutcomeFrame vyperEvalFrame vyperTypeEvalSoundness vyperTypeEvalStoragePreservation
  vyperInterpreter vyperState vyperStorageBackend vyperTypeExprSoundness vyperTypeInitialState vyperTypeSystem vyperTypeEnv vyperTypeInvariants pair list
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";

(* The empty defaults scope has its own typing environment.  In particular,
   this is not transport of the caller's environment across push_function. *)
Theorem intcall_defaults_runtime_entry:
  runtime_consistent env cx st /\ functions_well_typed cx /\
  env_body.current_src = src /\
  env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members ==>
  runtime_consistent (defaults_env env_body)
    (cx with stk updated_by CONS (src,fn)) (st with scopes := [FEMPTY]) /\
  functions_well_typed (cx with stk updated_by CONS (src,fn))
Proof
  strip_tac >>
  fs[runtime_consistent_def] >>
  drule_all intcall_default_env_side_conditions >> strip_tac >>
  `env_consistent (defaults_env env_body)
     (cx with stk updated_by CONS (src,fn)) (st with scopes := [FEMPTY])` by
    (irule defaults_env_empty_frame_consistent >> simp[]) >>
  gvs[runtime_consistent_def, state_well_typed_def, scope_well_typed_def]
QED

(* Successful-prefix composition keeps the guard on the actual entry state;
   it never turns a guarded recursive premise into an all-state frame. *)
Triviality guarded_bind_observer:
  (!s r t. P s /\ f s = (r,t) ==> obs t = obs s) /\
  (!s v t r u. P s /\ f s = (INL v,t) /\ g v t = (r,u) ==>
     obs u = obs t) ==>
  !s r t. P s /\ bind f g s = (r,t) ==> obs t = obs s
Proof
  strip_tac >> rpt gen_tac >>
  simp_tac bool_ss [bind_def] >>
  Cases_on `f s` >> Cases_on `q` >> gvs[] >> metis_tac[]
QED

Theorem intcall_defaults_guarded_storage_frame:
  (!st res fin. P (st with scopes := [FEMPTY]) /\
     eval_exprs cx es (st with scopes := [FEMPTY]) = (res,fin) ==>
     lookup_storage w (get_storage ocx fin tr) =
     lookup_storage w (get_storage ocx (st with scopes := [FEMPTY]) tr)) ==>
  !st res fin prev. P (st with scopes := [FEMPTY]) /\
    finally (do set_scopes [FEMPTY]; eval_exprs cx es od)
      (set_scopes prev) st = (res,fin) ==>
    lookup_storage w (get_storage ocx fin tr) =
    lookup_storage w (get_storage ocx st tr)
Proof
  strip_tac >> rpt gen_tac >>
  simp_tac bool_ss [finally_def, bind_def, ignore_bind_def,
    set_scopes_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  Cases_on `q` >>
  simp_tac bool_ss [set_scopes_def, ignore_bind_def, bind_def,
    return_def, raise_def, PAIR_EQ, sumTheory.INL_11, sumTheory.INR_11] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >>
  simp[get_storage_scopes]
QED

Theorem intcall_defaults_runtime_storage_frame:
  runtime_consistent env cx st /\ functions_well_typed cx /\
  env_body.current_src = src /\
  env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members /\
  (!s res fin. runtime_consistent (defaults_env env_body)
       (cx with stk updated_by CONS (src,fn)) s /\
     eval_exprs (cx with stk updated_by CONS (src,fn)) needed s = (res,fin) ==>
     lookup_storage w (get_storage cx fin tr) =
     lookup_storage w (get_storage cx s tr)) /\
  finally (do set_scopes [FEMPTY];
              eval_exprs (cx with stk updated_by CONS (src,fn)) needed od)
    (set_scopes prev) st = (res,fin) ==>
  lookup_storage w (get_storage cx fin tr) = lookup_storage w (get_storage cx st tr)
Proof
  strip_tac >> drule_all intcall_defaults_runtime_entry >> strip_tac >>
  irule intcall_defaults_guarded_storage_frame >>
  qexistsl_tac [`runtime_consistent (defaults_env env_body)
    (cx with stk updated_by CONS (src,fn))`,
    `cx with stk updated_by CONS (src,fn)`, `needed`, `prev`, `res`] >>
  simp[]
QED

Theorem intcall_body_runtime_entry:
  runtime_consistent env cx st /\ functions_well_typed cx /\
  env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members /\
  scope_well_typed call_env /\
  env_scopes_consistent env_body cx (st with scopes := [call_env]) /\
  lock_if_nr cx nr view st = (INL (),locked) ==>
  runtime_consistent env_body
    (cx with stk updated_by CONS (env_body.current_src,fn))
    (locked with scopes := [call_env])
Proof
  strip_tac >> fs[runtime_consistent_def] >>
  drule intcall_default_env_side_conditions >>
  disch_then (qspecl_then [`env_body`,`env_body.current_src`,`fn`] mp_tac) >>
  simp[] >> strip_tac >>
  `env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (locked with scopes := [call_env]) /\
    state_well_typed (locked with scopes := [call_env]) /\
    accounts_well_typed (locked with scopes := [call_env]).accounts` by
    (irule intcall_live_pushed_body_preconditions >>
     simp[lock_if_nr_def] >>
     conj_tac
     >- (qexistsl_tac [`st`,`env`] >> simp[]) >>
     qexistsl_tac [`st`,`view`,`nr`] >>
     gvs[env_scopes_consistent_def, vyperContextTheory.get_tenv_def] >>
     first_assum ACCEPT_TAC) >>
  gvs[runtime_consistent_def]
QED

Triviality guarded_finally_observer:
  (!s r t. P s /\ f s = (r,t) ==> obs t = obs s) /\
  state_rel_frame (\s t. obs t = obs s) g ==>
  !s r t. P s /\ finally f g s = (r,t) ==> obs t = obs s
Proof
  simp_tac bool_ss [state_rel_frame_result, finally_def] >>
  strip_tac >> rpt gen_tac >>
  Cases_on `f s` >> Cases_on `q` >>
  simp_tac bool_ss [bind_def, ignore_bind_def] >>
  Cases_on `g r'` >> Cases_on `q` >>
  gvs[return_def, raise_def] >> metis_tac[]
QED

Triviality guarded_try_observer:
  (!s r t. P s /\ f s = (r,t) ==> obs t = obs s) /\
  (!e. state_rel_frame (\s t. obs t = obs s) (h e)) ==>
  !s r t. P s /\ try f h s = (r,t) ==> obs t = obs s
Proof
  simp_tac bool_ss [state_rel_frame_result, try_def] >>
  strip_tac >> rpt gen_tac >>
  Cases_on `f s` >> Cases_on `q` >> gvs[return_def] >> metis_tac[]
QED

Triviality defaults_restore_runtime:
  runtime_consistent env cx base_st /\
  runtime_consistent (defaults_env env_body)
    (cx with stk updated_by CONS (src,fn)) framed_st /\
  env_body.type_defs = get_tenv cx /\
  env_body.bare_globals = env.bare_globals /\
  env_body.toplevel_vtypes = env.toplevel_vtypes ==>
  runtime_consistent env cx (framed_st with scopes := base_st.scopes)
Proof
  rw[runtime_consistent_def, env_consistent_def]
  >- (qpat_x_assum `env_scopes_consistent env cx base_st` mp_tac >>
      simp[env_scopes_consistent_def] >> metis_tac[])
  >- (gvs[env_immutables_consistent_def, defaults_env_def,
          vyperLookupStorageTheory.get_tenv_stk,
          vyperLookupStorageTheory.get_module_code_stk,
          vyperContextTheory.get_tenv_def, vyperContextTheory.get_module_code_def] >> metis_tac[])
  >> gvs[state_well_typed_def]
QED

Theorem internal_call_storage_frame_guarded:
  ~cx.in_deploy /\
  (~tr \/ !slot. cx.nonreentrant_slot = SOME slot ==> w <> n2w slot) /\
  (!env st res fin.
    runtime_consistent env cx st /\ functions_well_typed cx /\
    well_typed_exprs env es /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    eval_expr_results cx es st = (res,fin) ==>
    lookup_storage w (get_storage cx fin tr) =
    lookup_storage w (get_storage cx st tr)) /\
  (!ts mut nr args dflts ret body env st res fin.
    get_module_code cx src = SOME ts /\
    lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,body) /\
    runtime_consistent env (cx with stk updated_by CONS (src,fn)) st /\
    functions_well_typed (cx with stk updated_by CONS (src,fn)) /\
    well_typed_exprs env
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) /\
    call_evaluation_safe (cx with stk updated_by CONS (src,fn))
      (int_calls_exprs (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)) /\
    eval_exprs (cx with stk updated_by CONS (src,fn))
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) st = (res,fin) ==>
    lookup_storage w (get_storage cx fin tr) =
    lookup_storage w (get_storage cx st tr)) /\
  (!ts mut nr args dflts ret body env ret_ty env' st res fin.
    get_module_code cx src = SOME ts /\
    lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,body) /\
    runtime_consistent env (cx with stk updated_by CONS (src,fn)) st /\
    functions_well_typed (cx with stk updated_by CONS (src,fn)) /\
    type_stmts env ret_ty body = SOME env' /\
    call_evaluation_safe (cx with stk updated_by CONS (src,fn))
      (int_calls_stmts body) /\
    eval_stmts (cx with stk updated_by CONS (src,fn)) body st = (res,fin) ==>
    lookup_storage w (get_storage cx fin tr) =
    lookup_storage w (get_storage cx st tr)) ==>
  !env st res fin.
    runtime_consistent env cx st /\ functions_well_typed cx /\
    well_typed_expr env (Call ty (IntCall (src,fn)) es ann) /\
    call_evaluation_safe cx (int_calls_expr (Call ty (IntCall (src,fn)) es ann)) /\
    eval_expr cx (Call ty (IntCall (src,fn)) es ann) st = (res,fin) ==>
    lookup_storage w (get_storage cx fin tr) =
    lookup_storage w (get_storage cx st tr)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once evaluate_def] >>
  Cases_on `MEM (src,fn) cx.stk`
  >- simp[bind_def, ignore_bind_def, type_check_def, assert_def, raise_def] >>
  Cases_on `get_module_code cx src`
  >- simp[bind_def, ignore_bind_def, type_check_def, assert_def, lift_option_type_def,
          return_def, raise_def] >>
  rename1 `get_module_code cx src = SOME ts` >>
  Cases_on `lookup_callable_function F fn ts`
  >- simp[bind_def, ignore_bind_def, type_check_def, assert_def, lift_option_type_def,
          return_def, raise_def] >>
  rename1 `lookup_callable_function F fn ts = SOME tup` >>
  PairCases_on `tup` >>
  Cases_on `LENGTH es <= LENGTH tup2 /\ LENGTH tup2 - LENGTH es <= LENGTH tup3`
  >- (simp[bind_def, ignore_bind_def, type_check_def, assert_def,
       lift_option_type_def, return_def, raise_def] >>
      Cases_on `eval_expr_results cx es st` >>
      rename1 `eval_expr_results cx es st = (rr,args_st)` >>
      `well_typed_exprs env es` by fs[well_typed_expr_def] >>
      `call_evaluation_safe cx (int_calls_exprs es)` by
        metis_tac[intcall_call_evaluation_safe_args] >>
      `lookup_storage w (get_storage cx args_st tr) =
       lookup_storage w (get_storage cx st tr)` by metis_tac[] >>
      Cases_on `rr`
      >- (rename1 `eval_expr_results cx es st = (INL results,args_st)` >>
          `env_consistent env cx st /\ state_well_typed st /\
           context_well_typed cx /\ accounts_well_typed st.accounts` by
             fs[runtime_consistent_def] >>
          drule_all (cj 1 (cj 11 eval_scc_type_sound_results_mutual)) >>
          strip_tac >>
          `runtime_consistent env cx args_st` by
            fs[runtime_consistent_def] >>
          `env_context_consistent env cx` by fs[env_consistent_def] >>
          `lookup_callable_function cx.in_deploy fn ts =
            SOME (tup0,tup1,tup2,tup3,tup4,tup5)` by simp[] >>
          `context_function_live cx (src,fn)` by
            (fs[well_typed_expr_def, env_context_consistent_def,
                fn_sigs_live_def] >> metis_tac[]) >>
          `IS_SOME (FLOOKUP env.fn_sigs (src,fn))` by
            (fs[well_typed_expr_def] >> metis_tac[optionTheory.IS_SOME_EXISTS]) >>
          drule_all callable_body_typing_from_env_consistent >>
          disch_then (CONJUNCTS_THEN2 assume_tac
            (qx_choose_then `env_body` (qx_choose_then `ret_tv`
              (qx_choose_then `env_after` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
          `well_typed_exprs (defaults_env env_body)
             (DROP (LENGTH tup3 - (LENGTH tup2 - LENGTH es)) tup3)` by
            metis_tac[well_typed_exprs_DROP] >>
          drule_all intcall_defaults_runtime_entry >>
          disch_then (qspec_then `fn` strip_assume_tac) >>
          `call_evaluation_safe (cx with stk updated_by CONS (src,fn))
             (int_calls_exprs (DROP (LENGTH tup3 - (LENGTH tup2 - LENGTH es)) tup3))` by
            metis_tac[intcall_call_evaluation_safe_needed_defaults] >>
          `LENGTH es + LENGTH tup3 - LENGTH tup2 =
             LENGTH tup3 - (LENGTH tup2 - LENGTH es)` by decide_tac >>
          simp_tac bool_ss [get_scopes_def, pairTheory.pair_case_thm,
            sumTheory.sum_case_def] >>
          asm_rewrite_tac [] >>
          Cases_on `finally (do set_scopes [FEMPTY];
            eval_exprs (cx with stk updated_by CONS (src,fn))
              (DROP (LENGTH tup3 - (LENGTH tup2 - LENGTH es)) tup3) od)
            (set_scopes args_st.scopes) args_st` >>
          rename1 `_ = (dres,dflt_st)` >>
          `lookup_storage w (get_storage cx dflt_st tr) =
             lookup_storage w (get_storage cx args_st tr)` by
            (irule intcall_defaults_runtime_storage_frame >>
             conj_tac >- first_assum ACCEPT_TAC >>
             qexistsl_tac [`env`,`env_body`,`fn`,
               `DROP (LENGTH tup3 - (LENGTH tup2 - LENGTH es)) tup3`,
               `args_st.scopes`,`dres`,`src`] >>
             reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
             rpt strip_tac >>
             qpat_x_assum `!ts' mut nr args dflts ret body env st res fin.
               _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ eval_exprs _ _ _ = _ ==> _`
               irule >>
             metis_tac[]) >>
          simp_tac bool_ss [return_def, pairTheory.pair_case_thm,
            sumTheory.sum_case_def] >>
          pure_rewrite_tac [GSYM ignore_bind_def] >>
          asm_rewrite_tac [] >>
          reverse (Cases_on `dres`)
          >- (simp_tac bool_ss [pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
              strip_tac >>
              qpat_x_assum `(INR _,_) = (_,_)`
                (SUBST_ALL_TAC o cj 2 o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
              qpat_x_assum `lookup_storage _ (get_storage _ fin _) = _` SUBST1_TAC >>
              first_assum ACCEPT_TAC) >>
          rename1 `_ = (INL dflt_vs,dflt_st)` >>
          Cases_on `eval_exprs (cx with stk updated_by CONS (src,fn))
            (DROP (LENGTH tup3 - (LENGTH tup2 - LENGTH es)) tup3)
            (args_st with scopes := [FEMPTY])` >>
          rename1 `_ = (raw_res,raw_st)` >>
          `raw_res = INL dflt_vs /\
           dflt_st = raw_st with scopes := args_st.scopes` by
            (qpat_x_assum `finally _ _ _ = _` mp_tac >>
             Cases_on `raw_res` >>
             simp_tac (srw_ss()) [finally_def, bind_def, ignore_bind_def,
               set_scopes_def, return_def, raise_def] >>
             qpat_x_assum `eval_exprs _ _ _ = _`
               (fn th => rewrite_tac [th]) >>
             simp_tac (srw_ss()) []) >>
          `env_consistent (defaults_env env_body)
             (cx with stk updated_by CONS (src,fn))
             (args_st with scopes := [FEMPTY]) /\
           state_well_typed (args_st with scopes := [FEMPTY]) /\
           context_well_typed (cx with stk updated_by CONS (src,fn)) /\
           accounts_well_typed (args_st with scopes := [FEMPTY]).accounts` by
            (qpat_x_assum `runtime_consistent (defaults_env _) _ _` mp_tac >>
             simp_tac bool_ss [runtime_consistent_def]) >>
          drule_all (cj 1 (cj 6 eval_scc_type_sound_results_mutual)) >>
          strip_tac >>
          `runtime_consistent (defaults_env env_body)
             (cx with stk updated_by CONS (src,fn)) raw_st` by
            (simp_tac bool_ss [runtime_consistent_def] >>
             rpt conj_tac >> first_assum ACCEPT_TAC) >>
          `runtime_consistent env cx dflt_st` by
            (qpat_x_assum `dflt_st = _` SUBST1_TAC >>
             irule defaults_restore_runtime >>
             metis_tac[]) >>
          simp_tac bool_ss [pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
          Cases_on `read_results cx results dflt_st` >>
          rename1 `read_results cx results dflt_st = (read_res,read_st)` >>
          `read_st = dflt_st` by metis_tac[read_results_state] >>
          qpat_x_assum `read_st = dflt_st` SUBST_ALL_TAC >>
          reverse (Cases_on `read_res`)
          >- (simp_tac bool_ss [pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
              disch_then (SUBST_ALL_TAC o cj 2 o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
              qpat_x_assum `lookup_storage _ (get_storage _ fin _) = _` SUBST1_TAC >>
              first_assum ACCEPT_TAC) >>
          rename1 `read_results cx results dflt_st = (INL vs,dflt_st)` >>
          `vyperImmutableMetadataFrame$immutable_metadata_frame
             (args_st with scopes := [FEMPTY]) raw_st` by
            (drule (cj 6 vyperImmutableMetadataFrameTheory.eval_metadata_frame_mutual) >>
             simp_tac bool_ss []) >>
          `vyperImmutableMetadataFrame$immutable_metadata_frame args_st dflt_st` by
            (qpat_x_assum `dflt_st = _` SUBST1_TAC >>
             qpat_x_assum `vyperImmutableMetadataFrame$immutable_metadata_frame _ raw_st` mp_tac >>
             simp_tac (srw_ss()) [vyperImmutableMetadataFrameTheory.immutable_metadata_frame_def] >>
             strip_tac >> first_assum ACCEPT_TAC) >>
          `dflt_st.scopes = args_st.scopes` by
            (qpat_x_assum `dflt_st = _` SUBST1_TAC >> simp_tac (srw_ss()) []) >>
          `expr_results_typed (env,cx,args_st) es results` by
            (first_assum (ACCEPT_TAC o SIMP_RULE bool_ss [sumTheory.sum_case_def])) >>
          `state_well_typed dflt_st` by
            (qpat_x_assum `runtime_consistent env cx dflt_st` mp_tac >>
             simp_tac bool_ss [runtime_consistent_def] >> metis_tac[]) >>
          drule_all read_results_restored_runtime_typed >> strip_tac >>
          `exprs_runtime_typed (defaults_env env_body)
             (DROP (LENGTH tup3 - (LENGTH tup2 - LENGTH es)) tup3) dflt_vs` by
            (qpat_x_assum `raw_res = INL dflt_vs` SUBST_ALL_TAC >>
             first_assum (ACCEPT_TAC o SIMP_RULE bool_ss [sumTheory.sum_case_def])) >>
          `env.type_defs = get_tenv cx /\ fn_sigs_consistent env.fn_sigs cx` by
            (qpat_x_assum `env_context_consistent env cx` mp_tac >>
             simp_tac (srw_ss()) [env_context_consistent_def] >> metis_tac[]) >>
          `MAP expr_type es = TAKE (LENGTH es) (MAP SND tup2)` by
            (drule_all typed_intcall_source_signature >>
             strip_tac >>
             qpat_x_assum `get_module_code cx src = SOME ts` (fn th =>
               RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
             qpat_x_assum `SOME ts = SOME _`
               (SUBST_ALL_TAC o REWRITE_RULE [optionTheory.SOME_11]) >>
             qpat_x_assum `lookup_callable_function cx.in_deploy fn _ = SOME (tup0,_)`
               (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
             qpat_x_assum `SOME (tup0,_) = SOME _`
               (strip_assume_tac o REWRITE_RULE [optionTheory.SOME_11,pairTheory.PAIR_EQ]) >>
             qpat_x_assum `tup2 = _` SUBST_ALL_TAC >>
             first_assum ACCEPT_TAC) >>
          `?call_env.
             bind_arguments (get_tenv cx) tup2 (vs ++ dflt_vs) = SOME call_env /\
             scope_well_typed call_env /\
             env_scopes_consistent env_body cx (dflt_st with scopes := [call_env])` by
            (irule vyperTypeBindArgumentsTheory.intcall_bind_arguments_from_runtime_typed >>
             rpt conj_tac >> metis_tac[]) >>
          qpat_assum `bind_arguments _ _ _ = SOME call_env` (fn th =>
            simp_tac (srw_ss()) [th, return_def]) >>
          pure_rewrite_tac [GSYM lock_if_nr_def] >>
          Cases_on `lock_if_nr cx tup1 (tup0 = View \/ tup0 = Pure) dflt_st` >>
          rename1 `lock_if_nr _ _ _ _ = (lock_res,locked)` >>
          `lookup_storage w (get_storage cx locked tr) =
             lookup_storage w (get_storage cx dflt_st tr)` by
            metis_tac[targetCallLockFrameTheory.lock_if_nr_get_storage_frame] >>
          reverse (Cases_on `lock_res`)
          >- (simp_tac (srw_ss()) [] >>
              disch_then (SUBST_ALL_TAC o cj 2 o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
              metis_tac[]) >>
          Cases_on `x` >>
          `runtime_consistent env_body (cx with stk updated_by CONS (src,fn))
             (locked with scopes := [call_env])` by
            (qpat_assum `env_body.current_src = src` (fn th =>
               once_rewrite_tac [GSYM th]) >>
             irule intcall_body_runtime_entry >> metis_tac[]) >>
          simp_tac (srw_ss()) [push_function_def, bind_def, get_scopes_def,
            set_scopes_def, return_def] >>
          `call_evaluation_safe (cx with stk updated_by CONS (src,fn))
             (int_calls_stmts tup5)` by
            metis_tac[intcall_call_evaluation_safe_body] >>
          `!s r t. runtime_consistent env_body
              (cx with stk updated_by CONS (src,fn)) s /\
              eval_stmts (cx with stk updated_by CONS (src,fn)) tup5 s = (r,t) ==>
              lookup_storage w (get_storage cx t tr) =
              lookup_storage w (get_storage cx s tr)` by
            (rpt strip_tac >>
             qpat_x_assum `!ts' mut nr args dflts ret body env ret_ty env' st res fin. _`
               irule >> metis_tac[]) >>
          `!s t. machine_frame s t ==>
              lookup_storage w (get_storage cx t tr) =
              lookup_storage w (get_storage cx s tr)` by
            (Cases_on `tr` >> simp_tac (srw_ss()) [machine_frame_def, get_storage_def]) >>
          pure_rewrite_tac [GSYM CONJ_ASSOC, GSYM DE_MORGAN_THM,
            GSYM unlock_if_nr_def] >>
          qmatch_goalsub_abbrev_tac `finally work cleanup entry` >>
          `state_rel_frame (\s t. lookup_storage w (get_storage cx t tr) =
              lookup_storage w (get_storage cx s tr)) cleanup` by
            (unabbrev_all_tac >>
             pure_rewrite_tac [ignore_bind_def] >>
             match_mp_tac state_rel_frame_bind_guarded >>
             conj_tac >- simp_tac bool_ss [] >>
             conj_tac
             >- (irule state_rel_frame_machine >>
                 simp_tac (srw_ss()) [machine_frame_pop_function] >>
                 first_assum ACCEPT_TAC) >>
             rpt strip_tac >>
             pure_rewrite_tac [state_rel_frame_result] >> BETA_TAC >>
             rpt strip_tac >>
             irule targetCallLockFrameTheory.unlock_if_nr_get_storage_frame >>
             metis_tac[]) >>
          `!s r t. runtime_consistent env_body
              (cx with stk updated_by CONS (src,fn)) s /\ work s = (r,t) ==>
              lookup_storage w (get_storage cx t tr) =
              lookup_storage w (get_storage cx s tr)` by
            (simp_tac bool_ss [Abbr `work`] >>
             ho_match_mp_tac guarded_try_observer >>
             conj_tac
             >- (pure_rewrite_tac [ignore_bind_def] >>
                 ho_match_mp_tac guarded_bind_observer >>
                 conj_tac >- first_assum ACCEPT_TAC >>
                 simp_tac bool_ss [return_def, pairTheory.PAIR_EQ] >>
                 metis_tac[]) >>
             gen_tac >> irule state_rel_frame_machine >>
             conj_tac >- metis_tac[] >>
             simp_tac (srw_ss()) [machine_frame_handlers]) >>
          `!s r t. runtime_consistent env_body
              (cx with stk updated_by CONS (src,fn)) s /\
              finally work cleanup s = (r,t) ==>
              lookup_storage w (get_storage cx t tr) =
              lookup_storage w (get_storage cx s tr)` by
            (ho_match_mp_tac guarded_finally_observer >>
             conj_tac >> first_assum ACCEPT_TAC) >>
          Cases_on `finally work cleanup entry` >>
          rename1 `finally work cleanup entry = (body_res,body_fin)` >>
          `lookup_storage w (get_storage cx body_fin tr) =
             lookup_storage w (get_storage cx locked tr)` by
            (qpat_x_assum `Abbrev (entry = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
             `runtime_consistent env_body (cx with stk updated_by CONS (src,fn)) entry` by
               metis_tac[] >>
             `lookup_storage w (get_storage cx body_fin tr) =
                lookup_storage w (get_storage cx entry tr)` by metis_tac[] >>
             qpat_x_assum `entry = _` SUBST_ALL_TAC >>
             qpat_x_assum `lookup_storage w (get_storage cx body_fin tr) = _` mp_tac >>
             Cases_on `tr` >> simp_tac (srw_ss()) [get_storage_def]) >>
          Cases_on `body_res`
          >- (simp_tac (srw_ss()) [] >>
              rename1 `finally work cleanup entry = (INL rv,body_fin)` >>
              Cases_on `safe_cast ret_tv rv` >>
              qpat_x_assum `safe_cast ret_tv rv = _` (fn th => pure_rewrite_tac [th]) >>
              simp_tac (srw_ss()) [return_def, raise_def] >>
              disch_then (SUBST_ALL_TAC o cj 2 o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
              metis_tac[]) >>
          simp_tac (srw_ss()) [] >>
          disch_then (SUBST_ALL_TAC o cj 2 o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
          metis_tac[]) >>
      simp[] >> strip_tac >> gvs[]) >>
  simp[bind_def, ignore_bind_def, type_check_def, assert_def,
       lift_option_type_def, return_def, raise_def]
QED
