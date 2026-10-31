(*
 * Main mutual evaluator type-soundness proof for the executable Vyper type
 * system.
 *
 * This file contains the helper lemmas and proof of eval_scc_type_sound_mutual,
 * covering statements, statement lists, iterators, assignment targets, base
 * targets, for-loop bodies, and expressions.  Statement/list consequences are
 * stated separately in vyperTypeStmtSoundness.
 *)

Theory vyperTypeEvalSoundness
Ancestors
  list rich_list sorting pred_set prim_rec arithmetic finite_map option pair sum
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperCreate vyperCreateFrame vyperInterpreter vyperState vyperContext vyperStorage vyperTyping vyperLookup
  vyperImmutableMetadataFrame[ignore_grammar]
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeEnvExtension vyperTypeEnvPreservation vyperTypeScopePop
  vyperTypeABI vyperTypeBindArguments vyperTypeExprResult vyperTypeStmtResult
  vyperTypeCallOutcome[ignore_grammar] vyperCallOutcome[ignore_grammar]
  vyperTypeArgFits vyperTypeExtCallSoundness vyperTypeGlobalLookupSoundness vyperTypeAssignContext vyperTypeBuiltins vyperTypeExprSoundness vyperTypeAssignSoundness
  vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
  vyperEvalMisc vyperStatePreservation vyperAssignPreservesType vyperTypeStatePreservation
  vyperTypeCallGraph vyperTypeCallStackSoundness vyperPlaceResultTyping vyperPlaceTyping
  vyperPlaceWriteSoundness vyperTargetPlaceWrite vyperPlaceMutationSoundness
  vyperAugAssignWriteSoundness
  vyperAbiOperand vyperAbiExprTyping vyperAbiProjectionTyping vyperAbiReadTyping
  vyperAbiStateTyping vyperEvalAbiMemory vyperAbiFrame vyperTypeAbiLookupSoundness
  vyperTypeAbiProjectionSoundness
  vyperTypeAbiPlaceSoundness vyperCallOutcomeFrame
Libs
  wordsLib markerLib intLib

(* ===== Generic exception/result typing helpers ===== *)

Theorem lift_option_type_INL_eq[local]:
  lift_option_type opt msg st = (INL v,st') <=> opt = SOME v /\ st' = st
Proof
  Cases_on `opt` >> simp[lift_option_type_def, return_def, raise_def] >>
  metis_tac[]

QED
Theorem well_typed_exprs_EVERY[local]:
  well_typed_exprs env es ⇔ EVERY (well_typed_expr env) es
Proof
  Induct_on `es` >> simp[well_typed_expr_def]
QED

Theorem well_typed_exprs_perm:
  PERM xs ys ⇒
  (well_typed_exprs env xs ⇔ well_typed_exprs env ys)
Proof
  simp[well_typed_exprs_EVERY] >> metis_tac[PERM_EVERY]
QED

Theorem MEM_int_calls_exprs[local]:
  MEM call (int_calls_exprs es) ⇔
  ∃e. MEM e es ∧ MEM call (int_calls_expr e)
Proof
  Induct_on `es` >> simp[int_calls_expr_def] >> metis_tac[]
QED

Theorem call_evaluation_safe_exprs_perm:
  ∀cx xs ys.
    PERM xs ys ∧ call_evaluation_safe cx (int_calls_exprs xs) ⇒
    call_evaluation_safe cx (int_calls_exprs ys)
Proof
  rpt gen_tac >> strip_tac >> irule call_evaluation_safe_mono >>
  qexists_tac `int_calls_exprs xs` >>
  simp[MEM_int_calls_exprs] >>
  metis_tac[PERM_MEM_EQ]
QED

Theorem fn_sigs_consistent_FLOOKUP[local]:
  fn_sigs_consistent fn_sigs cx /\
  FLOOKUP fn_sigs (src_id_opt, fn) = SOME sig ==>
  ?ts fm nr params dflts body.
    get_module_code cx src_id_opt = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (fm, nr, params, dflts, sig.ret_ty, body) /\
    sig.param_types = MAP SND params /\
    sig.num_defaults = LENGTH dflts
Proof
  simp[fn_sigs_consistent_def]
QED

Theorem intcall_lookup_function_not_INR[local]:
  get_module_code cx src_id_opt = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME v /\
  get_module_code cx src_id_opt = SOME ts' ==>
  lift_option_type (lookup_callable_function cx.in_deploy fn ts') msg st <> (INR e,st')
Proof
  rpt strip_tac >> gvs[lift_option_type_def, return_def]
QED

Theorem intcall_args_length_condition[local]:
  fn_sigs_consistent fn_sigs cx /\
  FLOOKUP fn_sigs (src_id_opt,fn) = SOME sig /\
  lift_option_type (get_module_code cx src_id_opt) msg1 st1 = (INL ts,st1') /\
  lift_option_type (lookup_callable_function cx.in_deploy fn ts) msg2 st2 = (INL tup,st2') /\
  LENGTH es <= LENGTH sig.param_types /\
  LENGTH sig.param_types - sig.num_defaults <= LENGTH es ==>
  LENGTH es <= LENGTH (FST (SND (SND tup))) /\
  LENGTH (FST (SND (SND tup))) <=
    LENGTH es + LENGTH (FST (SND (SND (SND tup))))
Proof
  rpt strip_tac >>
  drule_all fn_sigs_consistent_FLOOKUP >> strip_tac >>
  qpat_x_assum `lift_option_type (get_module_code cx src_id_opt) _ _ = _`
    (fn th => assume_tac (MATCH_MP (iffLR lift_option_type_INL_eq) th)) >>
  qpat_x_assum `lift_option_type (lookup_callable_function cx.in_deploy fn ts) _ _ = _`
    (fn th => assume_tac (MATCH_MP (iffLR lift_option_type_INL_eq) th)) >>
  gvs[]
QED

Theorem intcall_call_evaluation_safe_target_not_mem[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (IntCall (src_id_opt,fn)) es extra)) ==>
  ~MEM (src_id_opt,fn) cx.stk
Proof
  simp[int_calls_expr_def] >> strip_tac >>
  irule call_evaluation_safe_target_not_mem >>
  qexists_tac `int_calls_exprs es` >> simp[]
QED

Theorem intcall_call_evaluation_safe_args[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (IntCall callee) es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  strip_tac >> irule call_evaluation_safe_mono >>
  qexists_tac `int_calls_expr (Call loc (IntCall callee) es extra)` >>
  simp[int_calls_expr_def]
QED

Theorem intcall_call_evaluation_safe_needed_defaults[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (IntCall (src_id_opt,fn)) es extra)) /\
  get_module_code cx src_id_opt = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (mut,nr,args,dflts,ret,fn_body) ==>
  call_evaluation_safe
    (cx with stk updated_by CONS (src_id_opt,fn))
    (int_calls_exprs (DROP n dflts))
Proof
  rpt strip_tac >> gvs[int_calls_expr_def] >>
  irule call_evaluation_safe_push_needed_defaults >>
  conj_tac
  >- (qexistsl_tac [`args`, `fn_body`, `fn`, `mut`, `nr`, `ret`,
                    `src_id_opt`, `ts`] >> simp[]) >>
  qexists_tac `int_calls_exprs es` >> simp[int_calls_expr_def]
QED

Theorem intcall_call_evaluation_safe_body[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (IntCall (src_id_opt,fn)) es extra)) /\
  get_module_code cx src_id_opt = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (mut,nr,args,dflts,ret,fn_body) ==>
  call_evaluation_safe
    (cx with stk updated_by CONS (src_id_opt,fn))
    (int_calls_stmts fn_body)
Proof
  rpt strip_tac >> gvs[int_calls_expr_def] >>
  irule call_evaluation_safe_push_body >>
  conj_tac
  >- (qexistsl_tac [`args`, `dflts`, `fn`, `mut`, `nr`, `ret`,
                    `src_id_opt`, `ts`] >> simp[]) >>
  qexists_tac `int_calls_exprs es` >> simp[int_calls_expr_def]
QED



Theorem int_calls_exprs_MAP_SND[local]:
  !kes. int_calls_exprs (MAP SND kes) = int_calls_named_exprs kes
Proof
  Induct >> simp[int_calls_expr_def] >> gen_tac >> PairCases_on `h` >>
  simp[int_calls_expr_def]
QED

Theorem call_evaluation_safe_int_calls_exprs_HD[local]:
  es <> [] /\ call_evaluation_safe cx (int_calls_exprs es) ==>
  call_evaluation_safe cx (int_calls_expr (HD es))
Proof
  Cases_on `es` >> simp[int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem extcall_call_evaluation_safe_args[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (ExtCall static skip_check sig opts) es drv)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem send_call_evaluation_safe_args[local]:
  call_evaluation_safe cx (int_calls_expr (Call loc (Send has_gas) es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem rawcall_call_evaluation_safe_args[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (RawCallTarget flags) es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem rawlog_call_evaluation_safe_args[local]:
  call_evaluation_safe cx (int_calls_expr (Call loc RawLog es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem rawrevert_call_evaluation_safe_args[local]:
  call_evaluation_safe cx (int_calls_expr (Call loc RawRevert es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem selfdestruct_call_evaluation_safe_args[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc SelfDestructTarget es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem create_call_evaluation_safe_args[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (CreateTarget kind has_salt rof) es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem exprs_cons_call_evaluation_safe_head[local]:
  call_evaluation_safe cx (int_calls_exprs (e::es)) ==>
  call_evaluation_safe cx (int_calls_expr e)
Proof
  simp[int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem exprs_cons_call_evaluation_safe_tail[local]:
  call_evaluation_safe cx (int_calls_exprs (e::es)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Theorem well_typed_exprs_DROP:
  !env es n. well_typed_exprs env es ==> well_typed_exprs env (DROP n es)
Proof
  gen_tac >> Induct >> simp[well_typed_expr_def] >>
  rpt strip_tac >> Cases_on `n` >> simp[well_typed_expr_def]
QED

Theorem well_typed_exprs_TAKE:
  !env es n. well_typed_exprs env es ==> well_typed_exprs env (TAKE n es)
Proof
  gen_tac >> Induct >> simp[well_typed_expr_def] >>
  rpt strip_tac >> Cases_on `n` >> simp[well_typed_expr_def]
QED

Theorem int_calls_exprs_APPEND[local]:
  !es es'. int_calls_exprs (es ++ es') =
    int_calls_exprs es ++ int_calls_exprs es'
Proof
  Induct >> simp[int_calls_expr_def, APPEND_ASSOC]
QED

Theorem call_evaluation_safe_exprs_TAKE:
  !es n cx. call_evaluation_safe cx (int_calls_exprs es) ==>
    call_evaluation_safe cx (int_calls_exprs (TAKE n es))
Proof
  rpt strip_tac >>
  `int_calls_exprs es =
     int_calls_exprs (TAKE n es) ++ int_calls_exprs (DROP n es)` by
    metis_tac[int_calls_exprs_APPEND, TAKE_DROP] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem call_evaluation_safe_exprs_DROP:
  !es n cx. call_evaluation_safe cx (int_calls_exprs es) ==>
    call_evaluation_safe cx (int_calls_exprs (DROP n es))
Proof
  rpt strip_tac >>
  `int_calls_exprs es =
     int_calls_exprs (TAKE n es) ++ int_calls_exprs (DROP n es)` by
    metis_tac[int_calls_exprs_APPEND, TAKE_DROP] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Theorem exprs_runtime_typed_APPEND:
  exprs_runtime_typed env es vs /\
  exprs_runtime_typed env es' vs' ==>
  exprs_runtime_typed env (es ++ es') (vs ++ vs')
Proof
  rw[exprs_runtime_typed_def] >>
  qexists_tac `tvs ++ tvs'` >> metis_tac[LIST_REL_APPEND_suff]
QED

Theorem get_tenv_stk_irrelevant[local]:
  !cx f. get_tenv (cx with stk updated_by f) = get_tenv cx
Proof
  simp[get_tenv_def]
QED

Theorem get_module_code_stk_irrelevant[local]:
  !cx f src. get_module_code (cx with stk updated_by f) src = get_module_code cx src
Proof
  simp[get_module_code_def]
QED

Theorem fn_sigs_consistent_stk_irrelevant[local]:
  !sigs cx f. fn_sigs_consistent sigs (cx with stk updated_by f) <=>
              fn_sigs_consistent sigs cx
Proof
  simp[fn_sigs_consistent_def, get_module_code_def]
QED

Theorem fn_sigs_declared_complete_stk_irrelevant[local]:
  !sigs cx f. fn_sigs_declared_complete sigs (cx with stk updated_by f) <=>
              fn_sigs_declared_complete sigs cx
Proof
  simp[fn_sigs_declared_complete_def, get_module_code_def]
QED

Theorem toplevel_vtypes_complete_stk_irrelevant[local]:
  !toplevel_vtypes cx f.
    toplevel_vtypes_complete toplevel_vtypes (cx with stk updated_by f) <=>
    toplevel_vtypes_complete toplevel_vtypes cx
Proof
  simp[toplevel_vtypes_complete_def, get_module_code_stk_irrelevant]
QED

Theorem bare_globals_complete_stk_irrelevant[local]:
  !bare_globals cx f.
    bare_globals_complete bare_globals (cx with stk updated_by f) <=>
    bare_globals_complete bare_globals cx
Proof
  simp[bare_globals_complete_def, get_module_code_stk_irrelevant]
QED

Theorem bare_global_assignable_complete_stk_irrelevant[local]:
  !bare_global_assignable cx f.
    bare_global_assignable_complete bare_global_assignable (cx with stk updated_by f) <=>
    bare_global_assignable_complete bare_global_assignable cx
Proof
  simp[bare_global_assignable_complete_def, get_module_code_stk_irrelevant]
QED

Theorem flag_members_complete_stk_irrelevant[local]:
  !flag_members cx f.
    flag_members_complete flag_members (cx with stk updated_by f) <=>
    flag_members_complete flag_members cx
Proof
  simp[flag_members_complete_def, get_module_code_stk_irrelevant]
QED

Theorem functions_well_typed_stk_irrelevant[local]:
  !cx f. functions_well_typed (cx with stk updated_by f) <=>
         functions_well_typed cx
Proof
  simp[functions_well_typed_def, get_module_code_def,
       get_tenv_stk_irrelevant, fn_sigs_consistent_stk_irrelevant,
       fn_sigs_declared_complete_stk_irrelevant,
       toplevel_vtypes_complete_stk_irrelevant,
       bare_globals_complete_stk_irrelevant,
       bare_global_assignable_complete_stk_irrelevant,
       flag_members_complete_stk_irrelevant,
       well_formed_type_def]
QED

Theorem context_well_typed_stk_irrelevant[local]:
  !cx f. context_well_typed (cx with stk updated_by f) <=>
         context_well_typed cx
Proof
  simp[context_well_typed_def]
QED
Theorem env_scopes_consistent_stk_irrelevant[local]:
  !env cx f st.
    env_scopes_consistent env (cx with stk updated_by f) st <=>
    env_scopes_consistent env cx st
Proof
  simp[env_scopes_consistent_def, get_tenv_stk_irrelevant]
QED

Theorem type_place_expr_Call_ExtCall_NONE[local]:
  !env ty static sig opts es drv skip_check.
    type_place_expr env (Call ty (ExtCall static skip_check sig opts) es drv) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

Theorem eval_expr_exception_return_typed:
  eval_expr cx e st = (INR exn, st') ==> return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  drule (cj 1 eval_expr_no_control) >>
  rw[no_control_exc_return_exception_typed]
QED

Theorem eval_exprs_exception_return_typed:
  eval_exprs cx es st = (INR exn, st') ==> return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  drule (cj 2 eval_expr_no_control) >>
  rw[no_control_exc_return_exception_typed]
QED


Theorem eval_iterator_no_control:
  !cx it st exn st'.
    eval_iterator cx it st = (INR exn, st') ==> no_control_exc exn
Proof
  Cases_on `it` >>
  rw[evaluate_def, bind_def, return_def, raise_def, lift_option_type_def,
     lift_sum_def, option_CASE_rator, sum_CASE_rator, AllCaseEqs()] >>
  metis_tac[cj 1 eval_expr_no_control, read_result_no_control, no_control_exc_def]
QED


Theorem value_runtime_typed_env_static:
  env'.type_defs = env.type_defs /\ value_runtime_typed env' ty v ==>
  value_runtime_typed env ty v
Proof
  rw[value_runtime_typed_def] >> metis_tac[]
QED

Definition live_memory_result_def:
  live_memory_result st pv <=>
    case pv of
    | PlaceR (MemoryPlace id path) =>
        ?entry fresh old. lookup_scopes id st.scopes = SOME entry /\
          memory_eval_path entry.type path /\
          memory_history_region entry fresh old [path]
    | _ => T
End

Theorem live_result_read_typed[local]:
  state_well_typed st /\ eval_result_typed (env,cx,st) pv (Type ty) /\
  live_memory_result st pv /\ read_result cx pv st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  (case res of INL v => value_runtime_typed env ty v | INR _ => T)
Proof
  Cases_on `pv`
  >- (rpt strip_tac >>
      gvs[eval_result_typed_def, read_result_def, return_def,
          no_type_error_result_def, value_runtime_typed_def])
  >- (rpt strip_tac >>
      gvs[eval_result_typed_def, live_memory_result_def, read_result_def] >>
      drule_all read_place_live_typed >>
      simp[value_runtime_typed_def] >> metis_tac[]) >>
  simp[eval_result_typed_def]
QED

(* Reading a live result preserves every permitted implicit bound widening. *)
Theorem read_live_result_widens_type[local]:
  state_well_typed st /\ eval_result_typed (env,cx,st) pv (Type src_ty) /\
  live_memory_result st pv /\ read_result cx pv st = (INL v,st') /\
  type_widens_to env.type_defs src_ty dst_ty ==>
  value_runtime_typed env dst_ty v
Proof
  strip_tac >> drule_all live_result_read_typed >> strip_tac >>
  gvs[value_runtime_typed_def] >>
  drule_all type_widens_to_value_has_type >> rw[] >> gvs[]
QED

Theorem switch_BoolV_live_empty_scope_post[local]:
  state_well_typed st /\
  eval_result_typed (env,cx,st) pv (Type (BaseT BoolT)) /\
  live_memory_result st pv /\
  switch_BoolV cx pv kt kf (st with scopes := FEMPTY::st.scopes) = (res,st') /\
  (!r s. kt (st with scopes := FEMPTY::st.scopes) = (r,s) ==> P r s) /\
  (!r s. kf (st with scopes := FEMPTY::st.scopes) = (r,s) ==> P r s) /\
  (!exn. no_type_error_result (INR exn) /\ no_control_exc exn ==>
    P (INR exn) (st with scopes := FEMPTY::st.scopes)) ==>
  P res st'
Proof
  rpt strip_tac >>
  Cases_on `read_result cx pv st` >>
  rename1 `read_result cx pv st = (rr,rs)` >>
  drule_all live_result_read_typed >> strip_tac >> gvs[] >>
  reverse (Cases_on `rr`)
  >- (drule read_result_no_control >> strip_tac >>
      gvs[switch_BoolV_def, bind_def, read_result_empty_scope,
          no_type_error_result_def] >> metis_tac[]) >>
  gvs[value_runtime_typed_def, evaluate_type_def] >>
  drule value_has_type_BoolTV >> strip_tac >>
  Cases_on `b` >> gvs[switch_BoolV_def, bind_def, read_result_empty_scope]
QED

Theorem switch_BoolV_live_post[local]:
  state_well_typed st /\
  eval_result_typed (env,cx,st) pv (Type (BaseT BoolT)) /\
  live_memory_result st pv /\
  switch_BoolV cx pv kt kf st = (res,st') /\
  (!r s. kt st = (r,s) ==> P r s) /\
  (!r s. kf st = (r,s) ==> P r s) /\
  (!exn. no_type_error_result (INR exn) /\ no_control_exc exn ==>
    P (INR exn) st) ==> P res st'
Proof
  rpt strip_tac >>
  Cases_on `read_result cx pv st` >>
  rename1 `read_result cx pv st = (rr,rs)` >>
  drule_all live_result_read_typed >> strip_tac >> gvs[] >>
  reverse (Cases_on `rr`)
  >- (drule read_result_no_control >> strip_tac >>
      gvs[switch_BoolV_def, bind_def, no_type_error_result_def] >> metis_tac[]) >>
  gvs[value_runtime_typed_def, evaluate_type_def] >>
  drule value_has_type_BoolTV >> strip_tac >>
  Cases_on `b` >> gvs[switch_BoolV_def, bind_def]
QED

Theorem conditional_result_live_typed[local]:
  state_well_typed st /\ eval_result_typed (env,cx,st) pv (Type ty) /\
  live_memory_result st pv /\ conditional_result cx pv st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  (case res of INL out => eval_result_typed (env,cx,st') out (Type ty) /\
                         live_memory_result st' out | INR _ => T)
Proof
  Cases_on `pv`
  >- (simp[conditional_result_def, return_def] >> rpt strip_tac >>
      gvs[no_type_error_result_def, live_memory_result_def])
  >- (strip_tac >>
      `?tv. evaluate_type env.type_defs ty = SOME tv /\
            runtime_place_typed cx st p tv` by gvs[eval_result_typed_def] >>
      `place_type_value cx p st = (INL tv,st)` by
        gvs[runtime_place_typed_def] >>
      qpat_x_assum `conditional_result _ _ _ = _` mp_tac >>
      simp[conditional_result_def, bind_def] >>
      IF_CASES_TAC
      >- (simp[return_def] >> strip_tac >> gvs[no_type_error_result_def]) >>
      Cases_on `read_result cx (PlaceR p) st` >>
      rename1 `read_result cx (PlaceR p) st = (rr,rs)` >>
      drule_all live_result_read_typed >> strip_tac >> gvs[] >>
      Cases_on `rr` >>
      gvs[read_result_def, bind_def, return_def, no_type_error_result_def,
          eval_result_typed_def, value_runtime_typed_def, live_memory_result_def] >>
      strip_tac >> gvs[eval_result_typed_def, live_memory_result_def]) >>
  simp[eval_result_typed_def]
QED

Theorem annassign_new_variable_after_read_result_sound[local]:
  env_consistent env cx st /\ state_well_typed st /\ accounts_well_typed st.accounts /\
  get_tenv cx = env.type_defs /\ evaluate_type env.type_defs typ = SOME tyv /\
  type_widens_to env.type_defs (expr_type e) typ /\
  eval_result_typed (env,cx,st) tvl (Type (expr_type e)) /\ live_memory_result st tvl /\
  id NOTIN FDOM env.var_types /\
  read_result cx tvl st = (INL v, st1) /\
  new_variable id tyv v st1 = (res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL u => env_consistent (extend_local env id typ T) cx st'
  | INR exn => env_consistent env cx st' /\ return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule read_result_state >> strip_tac >> gvs[] >>
  `value_has_type tyv v` by
    (drule_all read_live_result_widens_type >>
     simp[value_runtime_typed_def]) >>
  conj_tac
  >- metis_tac[new_variable_preserves_state_well_typed_result] >>
  conj_tac >- (drule new_variable_accounts >> rw[]) >>
  Cases_on `res` >> gvs[no_type_error_result_def]
  >- metis_tac[extend_local_env_consistent_after_new_variable] >>
  conj_asm1_tac
  >- (rpt strip_tac >> gvs[] >>
      drule_at(Pat`new_variable`) new_variable_no_type_error >>
      simp[] >> goal_assum drule_all) >>
  gvs[new_variable_def, bind_apply, AllCaseEqs(),
      ignore_bind_apply, list_CASE_rator, raise_def,
      get_scopes_def, return_def, type_check_def,
      assert_def, set_scopes_def]
QED
Theorem annassign_statement_sound_from_expr_ih[local]:
  (!env st res st'.
     env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
     accounts_well_typed st.accounts /\ functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_expr e) /\
     eval_expr cx e st = (res, st') ==>
     well_typed_expr env e ==>
     state_well_typed st' /\ env_consistent env cx st' /\
     accounts_well_typed st'.accounts /\ no_type_error_result res /\
     case res of INL tv =>
       eval_result_typed (env,cx,st') tv (Type (expr_type e)) /\
       live_memory_result st' tv | INR v1 => T) /\
  env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
  accounts_well_typed st.accounts /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  well_typed_expr env e /\ assignable_type env.type_defs typ /\
  type_widens_to env.type_defs (expr_type e) typ /\
  id NOTIN FDOM env.var_types /\
  get_tenv cx = env.type_defs /\ evaluate_type env.type_defs typ = SOME tyv /\
  eval_stmt cx (AnnAssign id typ e) st = (res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL u => env_consistent (extend_local env id typ T) cx st'
  | INR exn => env_consistent env cx st' /\ return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt cx (AnnAssign id typ e) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, lift_option_type_def,
                       return_def, raise_def] >>
  asm_rewrite_tac[] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    rename1 `eval_expr cx e st = (INL tvl, st1)` >>
    Cases_on `read_result cx tvl st1` >> rename1 `read_result cx tvl st1 = (mat_res, st2)` >>
    Cases_on `mat_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `read_result cx tvl st1 = (INL v, st2)` >>
      strip_tac >>
      `new_variable id tyv v st2 = (res,st')` by (
        qpat_x_assum `do tyv <- return tyv; tv <- eval_expr cx e; v <- read_result cx tv; new_variable id tyv v od st = (res,st')` mp_tac >>
        simp[bind_def, return_def, pairTheory.UNCURRY]) >>
      metis_tac[annassign_new_variable_after_read_result_sound,
                no_type_error_result_def]) >>
    rename1 `read_result cx tvl st1 = (INR exn, st2)` >>
    strip_tac >>
    `res = INR exn /\ st' = st2` by (
      qpat_x_assum `do tyv <- return tyv; tv <- eval_expr cx e; v <- read_result cx tv; new_variable id tyv v od st = (res,st')` mp_tac >>
      simp[bind_def, return_def, raise_def, pairTheory.UNCURRY]) >>
    gvs[no_type_error_result_def] >>
    `!msg. exn <> Error (TypeError msg)` by
      (drule_all live_result_read_typed >>
       simp[no_type_error_result_def]) >>
    drule read_result_state >> strip_tac >> gvs[] >>
    drule read_result_no_control >>
    rw[no_control_exc_return_exception_typed]) >>
  rename1 `eval_expr cx e st = (INR exn, st1)` >>
  strip_tac >>
  `res = INR exn /\ st' = st1` by (
    qpat_x_assum `do tyv <- return tyv; tv <- eval_expr cx e; v <- read_result cx tv; new_variable id tyv v od st = (res,st')` mp_tac >>
    simp[bind_def, return_def, raise_def, pairTheory.UNCURRY]) >>
  gvs[no_type_error_result_def] >>
  drule eval_expr_exception_return_typed >> rw[]
QED

Theorem callable_body_typing_from_env_consistent:
  functions_well_typed cx /\
  env_consistent env cx st /\
  IS_SOME (FLOOKUP env.fn_sigs (src_id_opt,fn)) /\
  get_module_code cx src_id_opt = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,fn_body) ==>
  (nr ==> cx.nonreentrant_slot <> NONE) /\
  ?env_body ret_tv env_after.
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    type_stmts env_body ret fn_body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough fn_body) /\
    stmts_no_control_escape fn_body /\
    well_typed_exprs (defaults_env env_body) dflts /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types id = SOME typ /\
       FLOOKUP env_body.var_assignable id = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = id /\ b = T) /\
    MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args)
Proof
  rw[env_consistent_def, env_context_consistent_def, env_immutables_consistent_def,
     functions_well_typed_def] >>
  `context_function_live cx (src_id_opt,fn)` by
    (gvs[IS_SOME_EXISTS] >> metis_tac[fn_sigs_live_def]) >>
  first_x_assum
    (qspecl_then [`env.fn_sigs`, `env.bare_globals`,
                  `env.bare_global_assignable`,
                  `env.toplevel_vtypes`, `env.flag_members`] mp_tac) >>
  simp[] >>
  impl_tac
  >- (rpt strip_tac >>
      Cases_on `vt` >> gvs[]
      >- (rename1 `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty)` >>
          rename1 `get_module_code cx src = SOME ts0` >>
          qpat_x_assum
            `!src id ty ts. FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\ get_module_code cx src = SOME ts ==> _`
            (qspecl_then [`src`,`id`,`ty`,`ts0`] mp_tac) >>
          simp[] >> strip_tac >> simp[] >>
          Cases_on `FLOOKUP env.bare_globals (src,id)`
          >- (qpat_x_assum
                `!src id ty. FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP env.bare_globals (src,id) = NONE ==> _`
                (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
              simp[] >> rw[] >> metis_tac[]) >>
          rename1 `FLOOKUP env.bare_globals (src,id) = SOME bare_ty` >>
          `bare_ty = ty` by (
            qpat_x_assum
              `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==> ?ts. _`
              (qspecl_then [`src`,`id`,`bare_ty`] mp_tac) >>
            simp[] >> rw[]) >>
          qpat_x_assum
            `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==> IS_SOME _`
            (qspecl_then [`src`,`id`,`bare_ty`] mp_tac) >>
          simp[IS_SOME_EXISTS] >> strip_tac >> PairCases_on `x` >>
          qpat_x_assum
            `!src id ty tv v. FLOOKUP env.bare_globals (src,id) = SOME ty /\ FLOOKUP _ id = SOME (tv,v) ==> _`
            (qspecl_then [`src`,`id`,`bare_ty`,`x0`,`x1`] mp_tac) >>
          simp[]) >>
      rename1 `FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt hv)` >>
      qpat_x_assum
        `!src id kt vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt) ==> _`
        (qspecl_then [`src`,`id`,`kt`,`hv`] mp_tac) >>
      simp[] >> rw[] >> metis_tac[]) >>
  rw[] >>
  first_x_assum drule_all >> simp[] >>
  rpt strip_tac >>
  Cases_on `vt` >> gvs[]
  >- (rename1 `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty)` >>
      rename1 `get_module_code cx src = SOME ts0` >>
      qpat_x_assum
        `!src id ty ts. FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\ get_module_code cx src = SOME ts ==> _`
        (qspecl_then [`src`,`id`,`ty`,`ts0`] mp_tac) >>
      simp[] >> strip_tac >> simp[] >>
      Cases_on `FLOOKUP env.bare_globals (src,id)`
      >- (qpat_x_assum
            `!src id ty. FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP env.bare_globals (src,id) = NONE ==> _`
            (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
          simp[] >> rw[] >> metis_tac[]) >>
      rename1 `FLOOKUP env.bare_globals (src,id) = SOME bare_ty` >>
      `bare_ty = ty` by (
        qpat_x_assum
          `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==> ?ts. _`
          (qspecl_then [`src`,`id`,`bare_ty`] mp_tac) >>
        simp[] >> rw[]) >>
      qpat_x_assum
        `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==> IS_SOME _`
        (qspecl_then [`src`,`id`,`bare_ty`] mp_tac) >>
      simp[IS_SOME_EXISTS] >> strip_tac >> PairCases_on `x` >>
      qpat_x_assum
        `!src id ty tv v. FLOOKUP env.bare_globals (src,id) = SOME ty /\ FLOOKUP _ id = SOME (tv,v) ==> _`
        (qspecl_then [`src`,`id`,`bare_ty`,`x0`,`x1`] mp_tac) >>
      simp[]) >>
  rename1 `FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt hv)` >>
  qpat_x_assum
    `!src id kt vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt) ==> _`
    (qspecl_then [`src`,`id`,`kt`,`hv`] mp_tac) >>
  simp[] >> rw[] >> metis_tac[]
QED

Theorem intcall_env_body_consistency_for_defaults[local]:
  !env env_body cx st src_id_opt fn.
    env_consistent env cx st /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members ==>
    env_context_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) st
Proof
  rw[env_consistent_def]
  >- (gvs[env_context_consistent_def] >>
      rw[env_context_consistent_def, get_tenv_stk_irrelevant,
         fn_sigs_consistent_stk_irrelevant,
         fn_sigs_declared_complete_stk_irrelevant,
         toplevel_vtypes_complete_stk_irrelevant,
         bare_globals_complete_stk_irrelevant,
         bare_global_assignable_complete_stk_irrelevant,
         flag_members_complete_stk_irrelevant,
         get_module_code_stk_irrelevant, current_module_def] >>
      first_x_assum drule_all >> simp[lookup_var_slot_from_layout_def])
  >- (gvs[env_immutables_consistent_def] >>
      rw[env_immutables_consistent_def, get_tenv_stk_irrelevant,
         get_module_code_stk_irrelevant] >>
      first_x_assum drule_all >> simp[] >>
      strip_tac >>
      first_x_assum (qspecl_then [`id_str`, `tv`, `v`] mp_tac) >>
      simp[])
QED

Theorem intcall_default_env_side_conditions:
  !env env_body cx st src_id_opt fn.
    env_consistent env cx st /\
    state_well_typed st /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    functions_well_typed cx /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members ==>
    env_context_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) st /\
    state_well_typed st /\
    context_well_typed (cx with stk updated_by CONS (src_id_opt,fn)) /\
    accounts_well_typed st.accounts /\
    functions_well_typed (cx with stk updated_by CONS (src_id_opt,fn))
Proof
  rpt strip_tac >>
  qspecl_then [`env`, `env_body`, `cx`, `st`, `src_id_opt`, `fn`] mp_tac
    intcall_env_body_consistency_for_defaults >>
  impl_tac >- simp[] >>
  strip_tac >>
  simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant]
QED
Theorem no_fallthrough_eval_no_success:
  (!s cx st st'.
      stmt_no_fallthrough s ==>
      eval_stmt cx s st <> (INL (), st')) /\
  (!ss cx st st'.
      stmts_no_fallthrough ss ==>
      eval_stmts cx ss st <> (INL (), st'))
Proof
  ho_match_mp_tac (legacyInduction.mutual_ind_from_ops stmt_induction) >>
  rw[stmt_no_fallthrough_def, evaluate_def, bind_def, return_def, raise_def,
     pairTheory.UNCURRY, finally_def, ignore_bind_def, switch_BoolV_def, AllCaseEqs()] >>
  (fn g =>
    if can (find_term (fn t => is_const t andalso #Name (dest_thy_const t) = "Raise")) (snd g)
    then (rename1 `Raise reason` >> Cases_on `reason`) g
    else if can (find_term (fn t => is_const t andalso #Name (dest_thy_const t) = "Return")) (snd g)
    then (rename1 `Return opt_e` >> Cases_on `opt_e`) g
    else all_tac g) >>
  gvs[evaluate_def, bind_def, return_def, raise_def,
      pairTheory.UNCURRY, COND_RATOR, AllCaseEqs()] >>
  Cases_on `c` >> simp[] >>
  BasicProvers.TOP_CASE_TAC >- simp[raise_def] >>
  BasicProvers.TOP_CASE_TAC >- simp[raise_def] >>
  BasicProvers.TOP_CASE_TAC >- simp[raise_def] >>
  simp[bind_def, raise_def, lift_option_def, return_def,
       pairTheory.UNCURRY, AllCaseEqs()]
QED
Theorem no_control_exc_no_loop_control[local]:
  no_control_exc exn ==> exn <> BreakException /\ exn <> ContinueException
Proof
  Cases_on `exn` >> rw[no_control_exc_def]
QED
Theorem push_scope_no_control[local]:
  push_scope st = (INR exn,st') ==> no_control_exc exn
Proof
  rw[push_scope_def, return_def, no_control_exc_def]
QED

Theorem pop_scope_no_control[local]:
  pop_scope st = (INR exn,st') ==> no_control_exc exn
Proof
  Cases_on `st.scopes` >> rw[pop_scope_def, return_def, raise_def, no_control_exc_def]
QED

Theorem new_variable_no_control[local]:
  new_variable id tv v st = (INR exn,st') ==> no_control_exc exn
Proof
  rw[new_variable_def, bind_def, ignore_bind_def, type_check_def, assert_def,
     get_scopes_def, AllCaseEqs()] >>
  Cases_on `s''.scopes` >>
  gvs[set_scopes_def, return_def, raise_def, no_control_exc_def]
QED


Theorem eval_for_no_loop_control[local]:
  !vs cx tyv nm body st exn st'.
    eval_for cx tyv nm body vs st = (INR exn,st') ==>
    exn <> BreakException /\ exn <> ContinueException
Proof
  Induct >>
  rw[Once evaluate_def, bind_def, ignore_bind_def, try_def, finally_def,
     push_scope_with_var_def, pop_scope_def, handle_loop_exception_def,
     return_def, raise_def, AllCaseEqs()] >>
  gvs[return_def] >>
  TRY (Cases_on `e` >> gvs[handle_loop_exception_def, return_def, raise_def]) >>
  res_tac >>
  gvs[]
QED
Theorem eval_stmt_assert_no_loop_control[local]:
  !a e cx st exn st'.
    eval_stmt cx (Assert e a) st = (INR exn,st') ==>
    exn <> BreakException /\ exn <> ContinueException
Proof
  Cases >> rpt gen_tac >>
  TRY (rename1 `eval_stmt cx (Assert e (AssertCustomError err)) st = _` >>
       Cases_on `err`) >>
  rw[Once evaluate_def, bind_def, switch_BoolV_def, return_def, raise_def,
     lift_option_def, vyperMiscTheory.option_CASE_rator,
     COND_RATOR, AllCaseEqs(), no_control_exc_def] >>
  metis_tac[eval_expr_no_control, read_result_no_control,
            lift_option_type_no_control, no_control_exc_no_loop_control]
QED
Theorem eval_stmt_raise_no_loop_control[local]:
  !r cx st exn st'.
    eval_stmt cx (Raise r) st = (INR exn,st') ==>
    exn <> BreakException /\ exn <> ContinueException
Proof
  Cases >> rpt gen_tac >>
  TRY (rename1 `eval_stmt cx (Raise (RaiseCustomError err)) st = _` >>
       Cases_on `err`) >>
  rw[Once evaluate_def, bind_def, return_def, raise_def,
     lift_option_def, vyperMiscTheory.option_CASE_rator,
     AllCaseEqs(), no_control_exc_def] >>
  metis_tac[eval_expr_no_control, read_result_no_control,
            lift_option_type_no_control, no_control_exc_no_loop_control]
QED

Theorem eval_stmt_return_no_loop_control[local]:
  !opt_e cx st exn st'.
    eval_stmt cx (Return opt_e) st = (INR exn,st') ==>
    exn <> BreakException /\ exn <> ContinueException
Proof
  Cases >>
  rw[Once evaluate_def, bind_def, return_def, raise_def,
     AllCaseEqs(), no_control_exc_def] >>
  metis_tac[cj 1 eval_expr_no_control, read_result_no_control,
            no_control_exc_no_loop_control]
QED



Theorem assign_stmt_no_control[local]:
  eval_stmt cx (Assign g e) st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `g` >> simp[Once evaluate_def, bind_def, ignore_bind_def,
    AllCaseEqs()] >> rpt strip_tac >>
  metis_tac[eval_target_place_no_control, read_result_no_control,
    write_place_no_control, assign_tuple_targets_no_control, cj 1 eval_expr_no_control]
QED

Theorem augassign_stmt_no_control[local]:
  eval_stmt cx (AugAssign ty t bop e) st = (INR exc,st') ==> no_control_exc exc
Proof
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  rpt strip_tac >>
  metis_tac[eval_target_place_no_control, read_place_no_control,
    place_type_value_no_control, cj 1 eval_expr_no_control, read_result_no_control,
    lift_sum_no_control, lift_option_type_no_control, write_place_no_control]
QED

Theorem stmt_no_control_escape_eval_no_loop_control:
  (!s cx st exn st'.
     stmt_no_control_escape s /\
     eval_stmt cx s st = (INR exn,st') ==>
     exn <> BreakException /\ exn <> ContinueException) /\
  (!ss cx st exn st'.
     stmts_no_control_escape ss /\
     eval_stmts cx ss st = (INR exn,st') ==>
     exn <> BreakException /\ exn <> ContinueException)
Proof
  ho_match_mp_tac (legacyInduction.mutual_ind_from_ops stmt_induction) >>
  rw[stmt_no_control_escape_def, evaluate_def, bind_def, ignore_bind_def,
     finally_def, try_def, switch_BoolV_def, return_def, raise_def,
     pairTheory.UNCURRY, COND_RATOR, AllCaseEqs()] >>
  map_every imp_res_tac
    [assign_stmt_no_control, augassign_stmt_no_control,
     read_place_no_control, place_type_value_no_control,
     eval_target_place_no_control, eval_base_place_no_control,
     get_place_no_control, write_place_no_control, append_place_no_control,
     check_no_control, type_check_no_control, lift_option_no_control,
     lift_option_type_no_control, lift_sum_no_control,
     push_scope_no_control, pop_scope_no_control, new_variable_no_control,
     read_result_no_control, push_log_no_control, assign_tuple_targets_no_control,
     eval_iterator_no_control, cj 1 eval_expr_no_control, cj 2 eval_expr_no_control] >>
  gvs[no_control_exc_def] >>
  metis_tac[eval_for_no_loop_control, eval_stmt_assert_no_loop_control,
    eval_stmt_raise_no_loop_control, eval_stmt_return_no_loop_control,
    no_fallthrough_eval_no_success]
QED

Theorem stmts_no_control_escape_eval_stmts_no_loop_control:
  stmts_no_control_escape ss /\ eval_stmts cx ss st = (INR exn,st') ==>
  exn <> BreakException /\ exn <> ContinueException
Proof
  metis_tac[stmt_no_control_escape_eval_no_loop_control]
QED



Theorem intcall_pushed_body_preconditions[local]:
  !env_body pushed_cx dflt_st lock_st call_env.
    env_context_consistent env_body pushed_cx /\
    env_immutables_consistent env_body pushed_cx dflt_st /\
    env_scopes_consistent env_body pushed_cx (dflt_st with scopes := [call_env]) /\
    state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    scope_well_typed call_env /\
    lock_st.scopes = dflt_st.scopes /\
    lock_st.immutables = dflt_st.immutables /\
    lock_st.accounts = dflt_st.accounts ==>
    env_consistent env_body pushed_cx (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    accounts_well_typed (lock_st with scopes := [call_env]).accounts
Proof
  rw[env_consistent_def, state_well_typed_def] >>
  gvs[env_scopes_consistent_def, env_immutables_consistent_def] >>
  metis_tac[]
QED

Theorem acquire_nonreentrant_lock_accounts[local]:
  !addr slot is_view st res st'.
    acquire_nonreentrant_lock addr slot is_view st = (res, st') ==>
    st'.accounts = st.accounts
Proof
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED
Theorem release_nonreentrant_lock_accounts[local]:
  !addr slot st res st'.
    release_nonreentrant_lock addr slot st = (res, st') ==>
    st'.accounts = st.accounts
Proof
  rw[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED

Theorem intcall_unlock_state_preserves_frame[local]:
  !cx nr is_view st res st'.
    (if nr /\ ~is_view then
       case cx.nonreentrant_slot of
       | NONE => return ()
       | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return ()) st = (res,st') ==>
    st'.scopes = st.scopes /\
    st'.immutables = st.immutables /\
    st'.accounts = st.accounts
Proof
  rpt strip_tac >>
  Cases_on `nr` >> gvs[return_def] >>
  Cases_on `is_view` >> gvs[return_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
  imp_res_tac release_nonreentrant_lock_scopes >>
  imp_res_tac release_nonreentrant_lock_immutables >>
  imp_res_tac release_nonreentrant_lock_accounts >>
  gvs[]
QED

Theorem intcall_cleanup_after_pop_preserves_frame[local]:
  !cx nr is_view prev st res st'.
    (do pop_function prev;
        if nr /\ ~is_view then
          case cx.nonreentrant_slot of
          | NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ()
     od) st = (res,st') ==>
    st'.scopes = prev /\
    st'.immutables = st.immutables /\
    st'.accounts = st.accounts
Proof
  rpt strip_tac >>
  gvs[pop_function_def, set_scopes_def, bind_def, ignore_bind_def,
      return_def] >>
  drule intcall_unlock_state_preserves_frame >>
  simp[]
QED

Theorem intcall_lock_state_preserves_frame[local]:
  !cx nr is_view st lock_st.
    (if nr then
       case cx.nonreentrant_slot of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) st = (INL (),lock_st) ==>
    lock_st.scopes = st.scopes /\
    lock_st.immutables = st.immutables /\
    lock_st.accounts = st.accounts
Proof
  rpt strip_tac >>
  Cases_on `nr` >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  imp_res_tac acquire_nonreentrant_lock_accounts >>
  gvs[]
QED

Theorem intcall_pushed_body_preconditions_from_lock[local]:
  !env_body cx pushed_cx dflt_st lock_st call_env nr is_view.
    env_context_consistent env_body pushed_cx /\
    env_immutables_consistent env_body pushed_cx dflt_st /\
    env_scopes_consistent env_body pushed_cx (dflt_st with scopes := [call_env]) /\
    state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    scope_well_typed call_env /\
    (if nr then
       case cx.nonreentrant_slot of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) dflt_st = (INL (),lock_st) ==>
    env_consistent env_body pushed_cx (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    accounts_well_typed (lock_st with scopes := [call_env]).accounts
Proof
  rpt strip_tac >>
  qspecl_then [`cx`, `nr`, `is_view`, `dflt_st`, `lock_st`] mp_tac
    intcall_lock_state_preserves_frame >>
  simp[] >> strip_tac >>
  qspecl_then [`env_body`, `pushed_cx`, `dflt_st`, `lock_st`, `call_env`] mp_tac
    intcall_pushed_body_preconditions >>
  (impl_tac >- simp[]) >>
  simp[]
QED
Theorem intcall_pushed_body_preconditions_for_defaults_from_lock[local]:
  !env_body cx dflt_st lock_st call_env src_id_opt fn nr is_view.
    env_context_consistent env_body (cx with stk updated_by CONS (src_id_opt,fn)) /\
    env_immutables_consistent env_body (cx with stk updated_by CONS (src_id_opt,fn)) dflt_st /\
    env_scopes_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn))
      (dflt_st with scopes := [call_env]) /\
    state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    scope_well_typed call_env /\
    (if nr then
       case cx.nonreentrant_slot of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) dflt_st = (INL (),lock_st) ==>
    env_consistent env_body (cx with stk updated_by CONS (src_id_opt,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    accounts_well_typed (lock_st with scopes := [call_env]).accounts
Proof
  rpt strip_tac >>
  qspecl_then [`env_body`, `cx`, `cx with stk updated_by CONS (src_id_opt,fn)`,
               `dflt_st`, `lock_st`, `call_env`, `nr`, `is_view`] mp_tac
    intcall_pushed_body_preconditions_from_lock >>
  (impl_tac >- simp[]) >>
  simp[]
QED

Theorem intcall_pushed_body_preconditions_live_from_defaults[local]:
  !env env_body cx args_st dflt_st lock_st call_env src_id_opt fn nr is_view.
    env_consistent env cx args_st /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) dflt_st /\
    env_scopes_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn))
      (dflt_st with scopes := [call_env]) /\
    state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    scope_well_typed call_env /\
    (if nr then
       case cx.nonreentrant_slot of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) dflt_st = (INL (),lock_st) ==>
    env_consistent env_body (cx with stk updated_by CONS (src_id_opt,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    accounts_well_typed (lock_st with scopes := [call_env]).accounts
Proof
  rpt strip_tac >>
  qspecl_then [`env`, `env_body`, `cx`, `args_st`, `src_id_opt`, `fn`] mp_tac
    intcall_env_body_consistency_for_defaults >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  qspecl_then [`env_body`, `cx`, `dflt_st`, `lock_st`, `call_env`,
               `src_id_opt`, `fn`, `nr`, `is_view`] mp_tac
    intcall_pushed_body_preconditions_for_defaults_from_lock >>
  (impl_tac >- simp[]) >>
  simp[]
QED

Theorem intcall_live_pushed_body_preconditions:
  !env env_body cx args_st dflt_st lock_st call_env fn nr is_view.
    env_consistent env cx args_st /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn)) dflt_st /\
    env_scopes_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (dflt_st with scopes := [call_env]) /\
    state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    scope_well_typed call_env /\
    (if nr then
       case cx.nonreentrant_slot of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) dflt_st = (INL (),lock_st) ==>
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    accounts_well_typed (lock_st with scopes := [call_env]).accounts
Proof
  rpt strip_tac >>
  qspecl_then
    [`env`, `env_body`, `cx`, `args_st`, `dflt_st`, `lock_st`, `call_env`,
     `env_body.current_src`, `fn`, `nr`, `is_view`]
    mp_tac intcall_pushed_body_preconditions_live_from_defaults >>
  (impl_tac >- simp[]) >>
  simp[]
QED


(* ===== C5.2 Bridge lemmas: derive shape and assignable context for statement
   assignment branches from evaluation/target-typing/runtime-consistency facts
   actually available at the call site. ===== *)

Theorem env_extends_return_exception_typed:
  env_extends env env' /\ return_exception_typed env' ret_ty exn ==>
  return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  Cases_on `exn` >> gvs[return_exception_typed_def] >>
  metis_tac[value_runtime_typed_env_static, env_extends_def]
QED

(* Generic scope-pop env-consistency facts moved to vyperTypeScopePop. *)

Theorem extend_local_F_env_extends:
  env_maps_wf env /\
  id NOTIN FDOM env.var_types ==>
  env_extends env (extend_local env id ty F)
Proof
  rw[env_extends_def, extend_local_def, FLOOKUP_UPDATE] >>
  Cases_on `id = id'` >> gvs[TO_FLOOKUP] >>
  fs[env_maps_wf_def] >>
  first_x_assum (qspec_then `id` mp_tac) >> simp[]
QED

Theorem return_exception_typed_extend_local_env_extends:
  env_extends (extend_local env id ty assignable) env_exn /\
  return_exception_typed env_exn ret_ty exn ==>
  return_exception_typed env ret_ty exn
Proof
  Cases_on `exn` >> simp[return_exception_typed_def] >>
  strip_tac >>
  irule value_runtime_typed_env_static >>
  qexists_tac `env_exn` >>
  gvs[env_extends_def, extend_local_def]
QED

Theorem for_cons_ordinary_exception_conclusion:
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  no_type_error_result (INR exn) ==>
  (env_extends (extend_local env id ty F) env_exn /\
   return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >>
  strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- fs[no_type_error_result_def] >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >>
  qexists_tac `env_exn` >>
  qexists_tac `id` >>
  qexists_tac `ty` >>
  fs[]
QED

Theorem for_cons_non_loop_exception_suffix_projected_explicit:
  !env cx id ty ret_ty st_body exn env_exn.
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    env_extends (extend_local env id ty F) env_exn /\
    env_consistent env_exn cx st_body /\
    return_exception_typed env_exn ret_ty exn ==>
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + vyperState$exception) of
     | INL _ => T
     | INR exn0 => return_exception_typed env ret_ty exn0)
Proof
  metis_tac[for_cons_ordinary_exception_conclusion, sum_case_def]
QED

Theorem for_cons_non_loop_exception_suffix_projected:
  !env env_after cx id ty ret_ty st_body exn.
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + vyperState$exception) of
     | INL u => env_consistent env_after cx st_body
     | INR exn0 =>
         ?env_exn.
           env_extends (extend_local env id ty F) env_exn /\
           env_consistent env_exn cx st_body /\
           return_exception_typed env_exn ret_ty exn0) ==>
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + vyperState$exception) of
     | INL _ => T
     | INR exn0 => return_exception_typed env ret_ty exn0)
Proof
  rpt strip_tac >>
  gvs[sum_case_def] >>
  qspecl_then [`env`,`cx`,`id`,`ty`,`ret_ty`,`st_body`,`exn`,`env_exn`] mp_tac
    for_cons_non_loop_exception_suffix_projected_explicit >>
  simp[]
QED

Theorem for_body_env_extends_consistent_after_pop:
  env_maps_wf env /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  env_extends (extend_local env id ty F) env_body /\
  env_consistent env_body cx st_body /\
  eval_stmts cx body_stmts
    (st with scopes updated_by CONS
       (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))) =
    (res, st_body) ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  strip_tac >>
  Cases_on `st_body.scopes` >> gvs[]
  >- (drule eval_stmts_preserves_scopes_len >> simp[] >>
      fs[env_consistent_def, env_scopes_consistent_def]) >>
  rename1 `st_body.scopes = h::tl` >>
  irule env_extends_env_consistent_after_pop >> simp[] >>
  conj_tac >- (
    drule eval_stmts_preserves_scopes_len >> simp[] >> strip_tac >>
    fs[env_consistent_def, env_scopes_consistent_def] >>
    Cases_on `st.scopes` >> gvs[] >>
    Cases_on `tl` >> gvs[]) >>
  conj_tac >- (
    conj_tac >> rpt strip_tac
    >- (irule scope_bracket_var_type_head_none >>
        qexists_tac `cx` >> qexists_tac `env` >> qexists_tac `res` >>
        qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)` >>
        qexists_tac `body_stmts` >> qexists_tac `st` >> qexists_tac `st_body` >>
        qexists_tac `tl` >> qexists_tac `ty'` >>
        simp[FLOOKUP_UPDATE, FDOM_FUPDATE]) >>
    `IS_SOME (FLOOKUP env.var_types id')` by fs[env_maps_wf_def] >>
    Cases_on `FLOOKUP env.var_types id'` >> gvs[] >>
    irule scope_bracket_var_type_head_none >>
    qexists_tac `cx` >> qexists_tac `env` >> qexists_tac `res` >>
    qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)` >>
    qexists_tac `body_stmts` >> qexists_tac `st` >> qexists_tac `st_body` >>
    qexists_tac `tl` >> qexists_tac `x` >>
    simp[FLOOKUP_UPDATE, FDOM_FUPDATE]) >>
  conj_tac >- (
    qexists_tac `env_body` >> simp[] >>
    conj_tac >- (
      rpt strip_tac >>
      irule scope_bracket_new_var_tail_none >>
      qexists_tac `cx` >> qexists_tac `env` >> qexists_tac `h` >>
      qexists_tac `res` >>
      qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)` >>
      qexists_tac `body_stmts` >> qexists_tac `st` >> qexists_tac `st_body` >> simp[]) >>
    irule env_extends_trans >>
    qexists_tac `extend_local env id ty F` >> simp[] >>
    irule extend_local_F_env_extends >> simp[]) >>
  qexists_tac `st` >> simp[] >>
  `st_body with scopes := tl =
   st_body with scopes := TL st_body.scopes` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule eval_stmts_scope_bracket_gen_preserves_tv >> simp[] >>
  qexists_tac `res` >>
  qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)` >>
  qexists_tac `body_stmts` >> simp[] >>
  irule (cj 2 eval_preserves_tv) >>
  qexists_tac `res` >> qexists_tac `body_stmts` >> simp[]
QED


Theorem for_cons_popped_env_consistent_from_stmt_case:
  (case (INR exn : unit + vyperState$exception) of
   | INL u => inl_post u
   | INR exn0 =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn0) ==>
  env_consistent env cx st ==>
  id NOTIN FDOM env.var_types ==>
  eval_stmts cx body_stmts
    (st with scopes updated_by CONS
       (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))) =
    (INR exn, st_body) ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  simp[] >> rpt strip_tac >>
  irule for_body_env_extends_consistent_after_pop >> simp[] >>
  conj_tac >- metis_tac[env_consistent_env_maps_wf] >>
  qexists_tac `body_stmts` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `INR exn` >> qexists_tac `st` >>
  qexists_tac `ty` >> qexists_tac `tyv` >> qexists_tac `v` >> simp[]
QED
Theorem for_body_env_consistent_after_pop:
  env_maps_wf env /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  type_stmts (extend_local env id ty F) ret_ty body_stmts = SOME env_after /\
  env_consistent env_after cx st_body /\
  eval_stmts cx body_stmts
    (st with scopes updated_by CONS
       (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))) =
    (res, st_body) ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  strip_tac >>
  irule for_body_env_extends_consistent_after_pop >> simp[] >>
  qexists_tac `body_stmts` >> qexists_tac `env_after` >>
  qexists_tac `id` >> qexists_tac `res` >> qexists_tac `st` >>
  qexists_tac `ty` >> qexists_tac `tyv` >> qexists_tac `v` >> simp[] >>
  irule type_stmts_env_extends >> simp[] >>
  conj_tac >- (irule extend_local_env_maps_wf >> simp[]) >>
  qexists_tac `ret_ty` >> qexists_tac `body_stmts` >> simp[]
QED

(* ===== Mutual theorem skeleton and statement/target cases ===== *)

(* TOP-LEVEL WORKHORSE: mutual type-soundness proof for statements, statement
 * lists, iterators, targets, and expressions.  The main theorem uses
 * suspend/Resume extensively; keep the theorem, all Resume blocks, and the
 * Finalise in this theory unless deliberately redesigning the proof. *)

(* ===== Scope-bracket helpers for block statements ===== *)

Theorem scope_bracket_decompose:
  (!q st_body. body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) ==> st_body.scopes <> []) /\
  (do push_scope; finally body_fun pop_scope od) st = (res, st') ==>
  ?q st_body.
    body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) /\
    st' = st_body with scopes := TL st_body.scopes /\
    (((?x. q = INL x) ==> ?u. res = INL u) /\
     (!e. q = INR e ==> res = INR e))
Proof
  rpt strip_tac >>
  gvs[push_scope_def, finally_def, pop_scope_def,
      return_def, raise_def, bind_def, ignore_bind_def,
      AllCaseEqs()] >>
  Cases_on `body_fun (st with scopes updated_by CONS FEMPTY)` >>
  Cases_on `q` >>
  gvs[AllCaseEqs(), pop_scope_def, return_def, raise_def] >>
  imp_res_tac eval_stmts_preserves_scopes_len >>
  Cases_on `r.scopes` >> gvs[return_def, raise_def,
    evaluation_state_component_equality]
QED

Theorem for_body_decompose_any[local]:
  !cx body_stmts stp res st'.
    stp.scopes <> [] /\
    finally (try do eval_stmts cx body_stmts; return F od handle_loop_exception)
      pop_scope stp = (res, st') ==>
    ?res_body st_body.
      eval_stmts cx body_stmts stp = (res_body, st_body) /\
      st' = st_body with scopes := TL st_body.scopes /\
      ((?x. res_body = INL x) ==> res = INL F) /\
      (res_body = INR ContinueException ==> res = INL F) /\
      (res_body = INR BreakException ==> res = INL T) /\
      (!e. res_body = INR e /\
           e <> ContinueException /\ e <> BreakException ==>
           res = INR e) /\
      (!e. res = INR e ==> res_body = INR e)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [finally_def, bind_apply, ignore_bind_apply,
    try_def, return_def, pop_scope_def, raise_def,
    handle_loop_exception_def] >>
  Cases_on `eval_stmts cx body_stmts stp` >>
  `?hd tl. r.scopes = hd :: tl` by (
    imp_res_tac eval_stmts_preserves_scopes_len >>
    Cases_on `r.scopes` >> gvs[]) >>
  Cases_on `q` >> gvs[] >>
  Cases_on `y = ContinueException` >> gvs[return_def] >>
  Cases_on `y = BreakException` >> gvs[return_def, raise_def] >>
  strip_tac >> gvs[]
QED
Theorem for_body_decompose_for_cons_pushed[local]:
  !cx body_stmts st id tyv v res st' stp.
    stp =
      st with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)) /\
    finally (try do eval_stmts cx body_stmts; return F od handle_loop_exception)
      pop_scope stp = (res, st') ==>
    ?res_body st_body.
      eval_stmts cx body_stmts stp = (res_body, st_body) /\
      st' = st_body with scopes := TL st_body.scopes /\
      ((?x. res_body = INL x) ==> res = INL F) /\
      (res_body = INR ContinueException ==> res = INL F) /\
      (res_body = INR BreakException ==> res = INL T) /\
      (!e. res_body = INR e /\
           e <> ContinueException /\ e <> BreakException ==>
           res = INR e) /\
      (!e. res = INR e ==> res_body = INR e)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `body_stmts`, `stp`, `res`, `st'`]
    mp_tac for_body_decompose_any >>
  impl_tac >- (
    conj_tac >- gvs[] >>
    qpat_assum `finally _ _ _ = _` ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED


Theorem for_cons_pushed_state_well_typed[local]:
  state_well_typed st /\ value_has_type tyv v /\ well_formed_type_value tyv ==>
  state_well_typed
    (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)))
Proof
  rw[state_well_typed_def, scope_well_typed_def, FLOOKUP_UPDATE]
QED

Theorem scope_bracket_post:
  env_maps_wf env /\
  env_consistent env cx st /\
  (!q st_body. body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) ==> st_body.scopes <> []) /\
  (do push_scope; finally body_fun pop_scope od) st = (res, st_final) /\
  (!q st_body.
     body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) ==>
     state_well_typed st_body /\ accounts_well_typed st_body.accounts /\
     no_type_error_result q /\
     case q of
     | INL _ => env_consistent env cx (st_body with scopes := TL st_body.scopes)
     | INR exn => env_consistent env cx (st_body with scopes := TL st_body.scopes) /\ return_exception_typed env ret_ty exn) ==>
  state_well_typed st_final /\ accounts_well_typed st_final.accounts /\ no_type_error_result res /\
  case res of
  | INL _ => env_consistent env cx st_final
  | INR exn => env_consistent env cx st_final /\ return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  qpat_x_assum `do push_scope; finally body_fun pop_scope od st = (res,st_final)` mp_tac >>
  qpat_x_assum `!q st_body. body_fun _ = _ ==> st_body.scopes <> []` mp_tac >>
  strip_tac >> strip_tac >>
  `?q st_body.
     body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) /\
     st_final = st_body with scopes := TL st_body.scopes /\
     (((?x. q = INL x) ==> ?u. res = INL u) /\
      (!e. q = INR e ==> res = INR e))` by
    (irule scope_bracket_decompose >> simp[]) >>
  gvs[] >>
  qmatch_assum_rename_tac`no_type_error_result r1` >>
  Cases_on `st_body.scopes` >> gvs[] >>
  `state_well_typed (st_body with scopes := t)` by (
    drule pop_scope_preserves_state_well_typed >>
    simp[pop_scope_def, return_def, raise_def]) >>
  Cases_on`r1` >> gvs[no_type_error_result_def]
QED

Theorem extract_elements_well_typed[local]:
  !arr_tv av elem_tv bd vs.
    value_has_type (ArrayTV elem_tv bd) (ArrayV av) /\
    well_formed_type_value (ArrayTV elem_tv bd) /\
    extract_elements (ArrayTV elem_tv bd) (ArrayV av) = SOME vs ==>
    EVERY (value_has_type elem_tv) vs
Proof
  rpt gen_tac >>
  simp[extract_elements_def] >>
  Cases_on `av` >> simp[value_has_type_inv]
  >- (rpt strip_tac >> gvs[array_elements_def, all_have_type_EVERY])
  >- (rpt strip_tac >> gvs[] >>
      fs[array_elements_def, LET_THM, EVERY_GENLIST] >>
      rpt strip_tac >>
      Cases_on `ALOOKUP l i` >> simp[]
      >- (match_mp_tac default_value_well_typed >> fs[well_formed_type_value_def]) >>
      metis_tac[ALOOKUP_sparse_has_type])
QED

Theorem Num_pos_le[local]:
  !x (m:num). 0 <= x ==> (Num x <= m <=> x <= &m)
Proof
  rpt strip_tac >>
  `&(Num x) = x` by metis_tac[integerTheory.INT_OF_NUM] >>
  pop_assum (fn th => REWRITE_TAC[GSYM integerTheory.INT_LE, th])
QED

Theorem within_int_bound_convex[local]:
  !b n1 n2 k.
    within_int_bound b n1 /\ within_int_bound b n2 /\
    n1 <= n2 /\ &k < n2 - n1 ==>
    within_int_bound b (n1 + &k)
Proof
  Cases_on `b` >> simp[within_int_bound_def] >> rpt strip_tac
  >- (
    Cases_on `n = 0` >- gvs[] >>
    gvs[] >>
    Cases_on `n1 + &k < 0` >> simp[]
    >- (
      `n1 < 0` by intLib.ARITH_TAC >> fs[] >>
      `0 <= -(n1 + &k)` by intLib.ARITH_TAC >>
      `0 <= -n1` by intLib.ARITH_TAC >>
      `-(n1 + &k) <= -n1` by intLib.ARITH_TAC >>
      fs[Num_pos_le] >> intLib.ARITH_TAC) >>
    Cases_on `n2 < 0`
    >- (`n1 + &k < n2` by intLib.ARITH_TAC >> intLib.ARITH_TAC) >>
    fs[] >>
    `0 <= n1 + &k` by intLib.ARITH_TAC >>
    `0 <= n2` by intLib.ARITH_TAC >>
    `n1 + &k < n2` by intLib.ARITH_TAC >>
    `Num (n1 + &k) < Num n2` by simp[integerTheory.NUM_LT] >>
    simp[]) >>
  `0 <= n1 + &k` by intLib.ARITH_TAC >>
  `0 <= n2` by intLib.ARITH_TAC >>
  `n1 + &k < n2` by intLib.ARITH_TAC >>
  `Num (n1 + &k) < Num n2` by simp[integerTheory.NUM_LT] >>
  simp[]
QED

Theorem range_values_well_typed[local]:
  !n1 n2 count tyv.
    value_has_type tyv (IntV n1) /\
    value_has_type tyv (IntV n2) /\
    get_range_limits (IntV n1) (IntV n2) = INL (n1, count) ==>
    EVERY (value_has_type tyv) (GENLIST (\n. IntV (n1 + &n)) count)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[get_range_limits_def] >>
  simp[EVERY_GENLIST] >> rpt strip_tac >>
  `0 <= n2 - n1` by intLib.ARITH_TAC >>
  `&n < n2 - n1` by (
    `&(Num (n2 - n1)) = n2 - n1` by metis_tac[integerTheory.INT_OF_NUM] >>
    intLib.ARITH_TAC) >>
  Cases_on `tyv` >> gvs[value_has_type_def] >>
  Cases_on `b` >> gvs[value_has_type_def]
  >- (
    `0 <= n1 + &n` by intLib.ARITH_TAC >>
    `0 <= n2` by intLib.ARITH_TAC >>
    `n1 + &n < n2` by intLib.ARITH_TAC >>
    `Num (n1 + &n) < Num n2` by simp[integerTheory.NUM_LT] >>
    simp[]) >>
  metis_tac[within_int_bound_convex]
QED

Theorem iterator_range_tail_sound[local]:
  !tv i1 i2 rl st.
    value_has_type tv (IntV i1) /\
    value_has_type tv (IntV i2) /\
    lift_sum (get_range_limits (IntV i1) (IntV i2)) st = (INL rl,st) ==>
    no_type_error_result (INL (GENLIST (\n. IntV (FST rl + &n)) (SND rl))) /\
    EVERY (value_has_type tv) (GENLIST (\n. IntV (FST rl + &n)) (SND rl))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lift_sum _ _ = _` mp_tac >>
  simp[lift_sum_def, get_range_limits_def] >>
  COND_CASES_TAC >> simp[return_def, raise_def] >>
  strip_tac >> gvs[] >>
  conj_tac >- simp[no_type_error_result_def] >>
  irule range_values_well_typed >>
  conj_tac >- simp[] >>
  qexists_tac `i2` >> simp[get_range_limits_def]
QED
Theorem iterator_range_tail_eval_sound[local]:
  !type_defs expr_ty tyv i1 i2 range_res st st_tail res st_final.
    evaluate_type type_defs expr_ty = SOME tyv /\
    value_has_type tyv (IntV i1) /\
    value_has_type tyv (IntV i2) /\
    lift_sum (get_range_limits (IntV i1) (IntV i2)) st = (range_res, st_tail) /\
    (case range_res of
     | INL rl => return (GENLIST (\n. IntV (FST rl + &n)) (SND rl)) st_tail
     | INR err => raise err st_tail) = (res, st_final) ==>
    st_final = st /\
    no_type_error_result res /\
    (case res of
     | INL vs => ?tyv'. evaluate_type type_defs expr_ty = SOME tyv' /\ EVERY (value_has_type tyv') vs
     | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  drule lift_sum_state >> strip_tac >> gvs[] >>
  Cases_on `range_res` >> gvs[return_def, raise_def]
  >- (
    rename1 `lift_sum (get_range_limits (IntV i1) (IntV i2)) st = (INL rl,st)` >>
    qspecl_then [`tyv`, `i1`, `i2`, `rl`, `st`] mp_tac iterator_range_tail_sound >>
    simp[no_type_error_result_def]) >>
  qpat_x_assum `lift_sum _ _ = _` mp_tac >>
  simp[lift_sum_def, get_range_limits_def, return_def, raise_def] >>
  Cases_on `i1 <= i2` >> gvs[return_def, raise_def, no_type_error_result_def]
QED


Theorem iterator_range_expr_error_eq[local]:
  !cx e' y st1 res st'.
    (case (INR y,st1) of
       (INL tv1,s'') =>
         (case read_result cx tv1 s'' of
            (INL v1,s'') =>
              (case eval_expr cx e' s'' of
                 (INL tv2,s'') =>
                   (case read_result cx tv2 s'' of
                      (INL v2,s'') =>
                        (case lift_sum (get_range_limits v1 v2) s'' of
                           (INL rl,s'') =>
                             (let n1 = FST rl; n2 = SND rl in
                                return (GENLIST (\n. IntV (n1 + &n)) n2)) s''
                         | (INR err,s'') => (INR err,s''))
                    | (INR err,s'') => (INR err,s''))
               | (INR err,s'') => (INR err,s''))
          | (INR err,s'') => (INR err,s''))
     | (INR err,s'') => (INR err,s'')) = (res,st') ==>
    res = INR y /\ st' = st1
Proof
  rpt strip_tac >>
  qpat_x_assum `(case (INR y,st1) of _ => _ | _ => _) = (res,st')` mp_tac >>
  simp[]
QED


(* The trusted history is only the prefix created while a place is live. *)
Definition typed_scope_transition_def:
  typed_scope_transition st st' <=>
    ?events. scope_pop_trace st.scopes events st'.scopes /\
      EVERY (\ev. entry_pop_event_valid (SND ev)) events
End

Theorem lookup_global_live[local]:
  lookup_global cx src id st = (res,st') ==>
  (case res of INL pv => live_memory_result st' pv | INR _ => T)
Proof
  simp[lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
      var_decl_info_CASE_rator, bind_def, lift_option_type_def, return_def,
      raise_def, AllCaseEqs(), live_memory_result_def]
QED

Theorem live_memory_result_fresh[local]:
  lookup_scopes id st.scopes = SOME entry /\
  memory_eval_path entry.type path /\
  evaluate_subscripts entry.type entry.value path = INL v ==>
  live_memory_result st (PlaceR (MemoryPlace id path))
Proof
  simp[live_memory_result_def] >> rpt strip_tac >>
  qexistsl_tac [`[]`, `entry.popped`] >>
  simp[memory_history_region_def, memory_path_covered_def,
       vyperPlaceInvariantsTheory.popped_history_typed_def] >> metis_tac[]
QED

Theorem typed_scope_transition_scopes[local]:
  st'.scopes = st.scopes ==> typed_scope_transition st st'
Proof
  simp[typed_scope_transition_def] >> strip_tac >>
  qexists_tac `[]` >> simp[scope_pop_trace_def]
QED

Theorem typed_scope_transition_refl[local]:
  typed_scope_transition st st
Proof
  simp[typed_scope_transition_def] >> qexists_tac `[]` >>
  simp[scope_pop_trace_def]
QED

Theorem typed_scope_transition_trans[local]:
  typed_scope_transition st middle /\ typed_scope_transition middle st' ==>
  typed_scope_transition st st'
Proof
  simp[typed_scope_transition_def] >> rpt strip_tac >>
  drule_all typed_scope_trace_append >> metis_tac[]
QED

(* Typed Hoare boundary: only newly emitted scope events are trusted. *)
Definition typed_scope_spec_def:
  typed_scope_spec P f Q <=>
    !st res st'. P st /\ f st = (res,st') ==>
      typed_scope_transition st st' /\
      (case res of INL x => Q x st' | INR _ => T)
End

Theorem typed_scope_spec_frame[local]:
  (!st res st'. P st /\ f st = (res,st') ==>
    st'.scopes = st.scopes /\
    (case res of INL x => Q x st' | INR _ => T)) ==>
  typed_scope_spec P f Q
Proof
  simp[typed_scope_spec_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[typed_scope_transition_scopes]
QED

Theorem typed_scope_spec_bind[local]:
  typed_scope_spec P f Q /\
  (!x. typed_scope_spec (Q x) (g x) R) ==>
  typed_scope_spec P (bind f g) R
Proof
  simp[typed_scope_spec_def] >> rpt strip_tac >>
  Cases_on `f st` >> rename1 `f st = (first_res,mid)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `first_res` >> gvs[bind_def] >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[typed_scope_transition_trans]
QED

Theorem typed_scope_spec_scopes[local]:
  (!st res st'. f st = (res,st') ==> st'.scopes = st.scopes) ==>
  typed_scope_spec P f (\x st. T)
Proof
  strip_tac >> irule typed_scope_spec_frame >> rpt strip_tac >>
  first_x_assum drule >> Cases_on `res` >> simp[]
QED

Theorem typed_scope_spec_trace_bind[local]:
  typed_scope_spec P f (\x st. T) /\
  (!x. typed_scope_spec (\st. T) (g x) (\y st. T)) ==>
  typed_scope_spec P (bind f g) (\y st. T)
Proof
  strip_tac >> irule typed_scope_spec_bind >>
  qexists_tac `\x st. T` >> simp[]
QED

Theorem typed_scope_spec_primitives[local,simp]:
  typed_scope_spec P (return v) (\x st. T) /\
  typed_scope_spec P (raise exn) (\x st. T) /\
  typed_scope_spec P get_scopes (\x st. T) /\
  typed_scope_spec P (type_check b msg) (\x st. T) /\
  typed_scope_spec P (check b msg) (\x st. T) /\
  typed_scope_spec P (lift_option_type opt msg) (\x st. T) /\
  typed_scope_spec P (read_result cx tv) (\x st. T)
Proof
  rpt conj_tac >> irule typed_scope_spec_scopes >>
  metis_tac[return_scopes, raise_scopes, get_scopes_scopes, type_check_scopes,
            check_scopes, lift_option_type_scopes, read_result_scopes]
QED

Theorem typed_scope_spec_name_target[local,simp]:
  typed_scope_spec P (eval_base_place cx (NameTarget id)) (\x st. T)
Proof
  rewrite_tac[Once evaluate_def] >>
  irule typed_scope_spec_trace_bind >> simp[] >> gen_tac >>
  rewrite_tac[ignore_bind_def] >>
  irule typed_scope_spec_trace_bind >> simp[]
QED

Theorem typed_scope_spec_name_expr[local,simp]:
  typed_scope_spec P (eval_expr cx (Name ty id)) (\x st. T)
Proof
  rewrite_tac[Once evaluate_def] >>
  irule typed_scope_spec_trace_bind >> simp[] >> gen_tac >>
  rewrite_tac[ignore_bind_def] >>
  irule typed_scope_spec_trace_bind >> simp[]
QED

Theorem typed_scope_spec_toplevel_target[local,simp]:
  typed_scope_spec P (eval_base_place cx (TopLevelNameTarget (src,id))) (\x st. T)
Proof
  rewrite_tac[Once evaluate_def] >> irule typed_scope_spec_scopes >>
  metis_tac[lookup_global_scopes]
QED

Theorem typed_scope_spec_global_expr[local,simp]:
  typed_scope_spec P (eval_expr cx (TopLevelName ty (src,id))) (\x st. T)
Proof
  rewrite_tac[Once evaluate_def] >> irule typed_scope_spec_scopes >>
  metis_tac[lookup_global_scopes]
QED

Theorem typed_scope_spec_flag_expr[local,simp]:
  typed_scope_spec P (eval_expr cx (FlagMember ty nsid mid)) (\x st. T)
Proof
  rewrite_tac[Once evaluate_def] >> irule typed_scope_spec_scopes >>
  metis_tac[lookup_flag_mem_scopes]
QED

Theorem pop_place_typed_transition[local]:
  runtime_consistent env cx st /\
  runtime_place_typed cx st p (ArrayTV etv (Dynamic n)) /\
  runtime_place_writable cx st p /\ live_memory_result st (PlaceR p) /\
  pop_place cx p st = (res,st') ==>
  typed_scope_transition st st'
Proof
  rpt strip_tac >>
  drule_at (Pat `pop_place _ _ _ = _`) pop_place_valid_scope_trace >>
  simp[GSYM typed_scope_transition_def] >>
  Cases_on `p` >> gvs[live_memory_result_def] >> metis_tac[]
QED

Theorem runtime_place_typed_transport:
  typed_scope_transition st st' /\ vyperImmutableMetadataFrame$immutable_metadata_frame st st' /\
  runtime_place_typed cx st p tv ==> runtime_place_typed cx st' p tv
Proof
  Cases_on `p`
  >- simp[]
  >- (simp[typed_scope_transition_def, runtime_place_typed_memory] >>
      rpt strip_tac >> drule_all scope_pop_trace_lookup >> strip_tac >>
      drule entry_pop_trace_metadata >> strip_tac >> metis_tac[]) >>
  simp[runtime_place_typed_immutable] >> rpt strip_tac >>
  drule_all immutable_metadata_frame_lookup >> strip_tac >> metis_tac[]
QED

Theorem eval_result_typed_transport[local]:
  typed_scope_transition st st' /\ vyperImmutableMetadataFrame$immutable_metadata_frame st st' /\
  eval_result_typed (env,cx,st) pv vt ==> eval_result_typed (env,cx,st') pv vt
Proof
  Cases_on `pv` >> Cases_on `vt` >> simp[eval_result_typed_def] >>
  metis_tac[runtime_place_typed_transport]
QED

(* Captured arguments retain typing and trusted read paths until loading. *)
Definition expr_results_typed_def:
  expr_results_typed (env,cx,st) es results <=>
    LIST_REL (\e pv. eval_result_typed (env,cx,st) pv (Type (expr_type e)) /\
                    live_memory_result st pv) es results
End

Theorem writable_place_result_transport[local]:
  typed_scope_transition st st' /\
  vyperImmutableMetadataFrame$immutable_metadata_frame st st' /\
  writable_place_result cx st pv ==> writable_place_result cx st' pv
Proof
  simp[typed_scope_transition_def] >> rpt strip_tac >>
  drule_all writable_place_result_frame >> simp[]
QED

Theorem live_memory_result_transport[local]:
  typed_scope_transition st st' /\ live_memory_result st (PlaceR (MemoryPlace id path)) ==>
  live_memory_result st' (PlaceR (MemoryPlace id path))
Proof
  simp[typed_scope_transition_def, live_memory_result_def] >> rpt strip_tac >>
  drule_all scope_pop_trace_lookup >> strip_tac >>
  drule entry_pop_trace_metadata >> strip_tac >>
  drule_all typed_scope_trace_live_region >> strip_tac >> gvs[] >>
  qexistsl_tac [`fresh'`, `old'`] >> simp[]
QED

Theorem live_result_transport:
  typed_scope_transition st st' /\ live_memory_result st pv ==>
  live_memory_result st' pv
Proof
  Cases_on `pv`
  >- simp[live_memory_result_def]
  >- (Cases_on `p`
      >- simp[live_memory_result_def]
      >- (strip_tac >> drule_all live_memory_result_transport >> simp[])
      >- simp[live_memory_result_def]) >>
  simp[live_memory_result_def]
QED

Theorem expr_results_typed_transport[local]:
  typed_scope_transition st st' /\
  vyperImmutableMetadataFrame$immutable_metadata_frame st st' /\
  expr_results_typed (env,cx,st) es results ==>
  expr_results_typed (env,cx,st') es results
Proof
  simp[expr_results_typed_def, LIST_REL_EL_EQN] >>
  metis_tac[eval_result_typed_transport, live_result_transport]
QED

Theorem exprs_runtime_typed_cons[local]:
  value_runtime_typed env (expr_type e) v /\ exprs_runtime_typed env es vs ==>
  exprs_runtime_typed env (e::es) (v::vs)
Proof
  rw[value_runtime_typed_def, exprs_runtime_typed_def] >>
  rename1 `evaluate_type env.type_defs (expr_type e) = SOME tyv` >>
  rename1 `LIST_REL _ es tvs` >>
  qexists_tac `tyv::tvs` >> simp[]
QED

Theorem read_results_typed:
  !es results st res st'.
    state_well_typed st /\ expr_results_typed (env,cx,st) es results /\
    read_results cx results st = (res,st') ==>
    no_type_error_result res /\
    case res of INL vs => exprs_runtime_typed env es vs | INR _ => T
Proof
  Induct
  >- (Cases_on `results` >>
      simp[expr_results_typed_def, read_results_def, return_def,
           no_type_error_result_def, exprs_runtime_typed_def]) >>
  Cases_on `results` >> simp[expr_results_typed_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `eval_result_typed (env,cx,st) pv (Type (expr_type e))` >>
  rename1 `LIST_REL _ es rest` >>
  qpat_x_assum `read_results _ _ _ = _` mp_tac >>
  simp[Once read_results_def, bind_def] >>
  Cases_on `read_result cx pv st` >>
  rename1 `read_result cx pv st = (head_res,head_st)` >>
  drule_all live_result_read_typed >> strip_tac >> gvs[] >>
  Cases_on `head_res` >> simp[] >>
  Cases_on `read_results cx rest head_st` >>
  rename1 `read_results cx rest head_st = (tail_res,tail_st)` >>
  `expr_results_typed (env,cx,head_st) es rest` by simp[expr_results_typed_def] >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `tail_res` >> simp[return_def] >> strip_tac >> gvs[] >>
  gvs[no_type_error_result_def] >>
  metis_tac[exprs_runtime_typed_cons]
QED

Theorem delayed_read_results_sound[local]:
  state_well_typed s1 /\ typed_scope_transition s0 s1 /\
  vyperImmutableMetadataFrame$immutable_metadata_frame s0 s1 /\
  expr_results_typed (env,cx,s0) es rs /\
  read_results cx rs s1 = (r,s2) ==>
  s2 = s1 /\ no_type_error_result r /\
  (case r of INL vs => exprs_runtime_typed env es vs | INR _ => T)
Proof
  strip_tac >>
  drule_all expr_results_typed_transport >> strip_tac >>
  drule_all read_results_typed >> strip_tac >>
  drule read_results_state >> simp[]
QED

Theorem exprs_runtime_typed_slices[local]:
  exprs_runtime_typed env (TAKE a es) xs /\
  exprs_runtime_typed env (TAKE b (DROP a es)) ys /\
  exprs_runtime_typed env (DROP b (DROP a es)) zs ==>
  exprs_runtime_typed env es (xs ++ ys ++ zs)
Proof
  strip_tac >>
  `exprs_runtime_typed env (DROP a es) (ys ++ zs)` by
    metis_tac[exprs_runtime_typed_APPEND, TAKE_DROP] >>
  `exprs_runtime_typed env (TAKE a es ++ DROP a es) (xs ++ (ys ++ zs))` by
    (irule exprs_runtime_typed_APPEND >> simp[]) >>
  gvs[TAKE_DROP, APPEND_ASSOC]
QED

Theorem expr_results_typed_restore_scopes[local]:
  st'.scopes = st.scopes /\
  vyperImmutableMetadataFrame$immutable_metadata_frame st st' /\
  expr_results_typed (env,cx,st) es results ==>
  expr_results_typed (env,cx,st') es results
Proof
  metis_tac[typed_scope_transition_scopes, expr_results_typed_transport]
QED

Theorem read_results_restored_typed[local]:
  st'.scopes = st.scopes /\
  vyperImmutableMetadataFrame$immutable_metadata_frame st st' /\
  expr_results_typed (env,cx,st) es results /\ state_well_typed st' /\
  read_results cx results st' = (res,st'') ==>
  st'' = st' /\ no_type_error_result res /\
  (case res of INL vs => exprs_runtime_typed env es vs | INR _ => T)
Proof
  rpt strip_tac >>
  drule_all expr_results_typed_restore_scopes >> strip_tac >>
  drule_all read_results_typed >> strip_tac >>
  drule read_results_state >> simp[]
QED

Theorem read_results_restored_runtime_typed:
  st'.scopes = st.scopes /\
  vyperImmutableMetadataFrame$immutable_metadata_frame st st' /\
  expr_results_typed (env,cx,st) es results /\ state_well_typed st' /\
  read_results cx results st' = (INL vs,st'') ==>
  st'' = st' /\ exprs_runtime_typed env es vs
Proof
  strip_tac >> drule_all read_results_restored_typed >> simp[]
QED

Theorem live_memory_result_read[local]:
  typed_scope_transition st st' /\ state_well_typed st' /\
  live_memory_result st (PlaceR (MemoryPlace id path)) /\
  runtime_place_typed cx st (MemoryPlace id path) tv ==>
  ?v. read_place cx (MemoryPlace id path) st' = (INL v,st') /\ value_has_type tv v
Proof
  simp[typed_scope_transition_def, live_memory_result_def, runtime_place_typed_memory] >>
  rpt strip_tac >> gvs[] >>
  drule_all typed_scope_trace_memory_read >> metis_tac[]
QED

Theorem read_live_place_success_type[local]:
  state_well_typed st /\ runtime_place_typed cx st p tv /\
  live_memory_result st (PlaceR p) /\ read_place cx p st = (INL v,st') ==>
  value_has_type tv v
Proof
  rpt strip_tac >> Cases_on `p`
  >- (irule read_nonmemory_place_success_type >> simp[] >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[])
  >- (mp_tac typed_scope_transition_refl >>
      disch_then (mp_then Any mp_tac live_memory_result_read) >>
      disch_then drule_all >> strip_tac >> gvs[]) >>
  irule read_nonmemory_place_success_type >> simp[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem read_live_result_success_type:
  state_well_typed st /\
  eval_result_typed (env,cx,st) res (Type ty) /\
  live_memory_result st res /\ read_result cx res st = (INL v,st') ==>
  value_runtime_typed env ty v
Proof
  Cases_on `res` >>
  gvs[eval_result_typed_def, read_result_def, return_def,
      value_runtime_typed_def] >>
  metis_tac[read_live_place_success_type]
QED

Theorem read_typed_result_error:
  state_well_typed st /\
  eval_result_typed (env,cx,st) res (Type ty) /\
  read_result cx res st = (INR err,st') ==>
  !msg. err <> Error (TypeError msg)
Proof
  Cases_on `res` >>
  gvs[eval_result_typed_def, read_result_def, return_def] >>
  metis_tac[read_place_typed_error]
QED

Theorem extend_storage_place_live[local]:
  extend_storage_place cx tr slot tv sb st = (INL p,st') ==>
  live_memory_result st' (PlaceR p)
Proof
  Cases_on `tv` >> Cases_on `sb` >>
  TRY (rename1 `ValueSubscript sv` >> Cases_on `sv`) >>
  simp[extend_storage_place_def, bind_def, raise_def, return_def,
       ignore_bind_def, check_def, assert_def, lift_option_type_def,
       vyperMiscTheory.option_CASE_rator, UNCURRY, AllCaseEqs()] >> rpt strip_tac >>
  gvs[live_memory_result_def] >> pairarg_tac >> gvs[] >>
  gvs[return_def, live_memory_result_def]
QED

Theorem typed_successful_step_declared[local]:
  value_has_type tv v /\ well_formed_type_value tv /\
  evaluate_subscripts tv v [sb] = INL w ==>
  ?etv. subscript_type tv sb = SOME etv
Proof
  rpt strip_tac >>
  `?etv. subscripts_type tv [sb] = SOME etv` by
    metis_tac[vyperPlaceStatePreservationTheory.evaluate_subscripts_declared_type_exists] >>
  gvs[subscripts_type_def, AllCaseEqs()]
QED

Theorem extend_live_memory_success[local]:
  state_well_typed st /\
  live_memory_result st (PlaceR (MemoryPlace id path)) /\
  place_type_value cx (MemoryPlace id path) st = (INL tv,st) /\
  subscript_type tv sb = SOME etv /\
  extend_place cx (PlaceR (MemoryPlace id path)) sb st = (INL pv,st') ==>
  live_memory_result st' pv
Proof
  simp[live_memory_result_def, extend_place_def, bind_def, ignore_bind_def,
       lift_sum_def, return_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[place_type_value_def, get_scopes_def, lift_option_type_def,
      bind_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[read_place_def, get_scopes_def, lift_option_type_def,
      bind_def, return_def, lift_sum_def, AllCaseEqs(), extend_memory_place_def,
      live_memory_result_def] >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  `memory_eval_path entry.type (path ++ [sb])` by
    (drule_all memory_eval_path_append >>
     simp[memory_eval_path_def, subscripts_type_def]) >>
  `value_has_type entry.type entry.value` by
    metis_tac[lookup_scopes_state_well_typed_value_has_type] >>
  `well_formed_type_value entry.type` by
    metis_tac[lookup_scopes_well_typed_type, state_well_typed_def] >>
  `MEM path [path]` by simp[] >>
  drule_all memory_history_region_extend >> strip_tac >>
  qexistsl_tac [`fresh`, `old`] >>
  gvs[memory_history_region_def]
QED

Theorem extend_live_memory_typed_success[local]:
  state_well_typed st /\
  runtime_place_typed cx st (MemoryPlace id path) tv /\
  live_memory_result st (PlaceR (MemoryPlace id path)) /\
  extend_place cx (PlaceR (MemoryPlace id path)) sb st = (INL pv,st') ==>
  live_memory_result st' pv
Proof
  rpt strip_tac >>
  `place_type_value cx (MemoryPlace id path) st = (INL tv,st)` by
    gvs[runtime_place_typed_def] >>
  `?v w. read_place cx (MemoryPlace id path) st = (INL v,st) /\
         evaluate_subscripts tv v [sb] = INL w` by
    (gvs[extend_place_def, bind_def, ignore_bind_def, lift_sum_def,
         return_def, AllCaseEqs()] >>
     gvs[vyperMiscTheory.sum_CASE_rator, raise_def, return_def, AllCaseEqs()] >>
     metis_tac[read_place_preserves_state]) >>
  `value_has_type tv v` by metis_tac[read_live_place_success_type] >>
  `well_formed_type_value tv` by gvs[runtime_place_typed_def] >>
  drule_all typed_successful_step_declared >> strip_tac >>
  drule_all extend_live_memory_success >> simp[]
QED

Theorem extend_live_place_typed_success[local]:
  state_well_typed st /\ runtime_place_typed cx st p tv /\
  live_memory_result st (PlaceR p) /\
  extend_place cx (PlaceR p) sb st = (INL pv,st') ==>
  live_memory_result st' pv
Proof
  rpt strip_tac >> Cases_on `p`
  >- (gvs[extend_place_def, bind_def, return_def, AllCaseEqs()] >>
      drule extend_storage_place_live >> simp[])
  >- metis_tac[extend_live_memory_typed_success] >>
  gvs[extend_place_def, bind_def, ignore_bind_def, return_def,
      AllCaseEqs(), extend_memory_place_def, live_memory_result_def]
QED

Theorem select_value_result_live[local]:
  select_result cx input_ty (Value vv) sb s = (INL pv,t) ==>
  live_memory_result t pv
Proof
  simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[live_memory_result_def]
QED

Theorem transported_typed_result_extend_live[local]:
  !t s env cx bp vt input_ty sb pv u.
  state_well_typed t /\ typed_scope_transition s t /\
  vyperImmutableMetadataFrame$immutable_metadata_frame s t /\
  eval_result_typed (env,cx,s) bp vt /\ live_memory_result s bp /\
  select_result cx input_ty bp sb t = (INL pv,u) ==>
  live_memory_result u pv
Proof
  rpt strip_tac >> Cases_on `bp`
  >- metis_tac[select_value_result_live]
  >- (rename1 `PlaceR p` >> Cases_on `vt` >> gvs[eval_result_typed_def] >>
      `runtime_place_typed cx t p tv` by
        metis_tac[runtime_place_typed_transport] >>
      `live_memory_result t (PlaceR p)` by
        (Cases_on `p`
         >- simp[live_memory_result_def]
         >- (irule live_memory_result_transport >> goal_assum drule_all)
         >> simp[live_memory_result_def]) >>
      gvs[select_result_def] >>
      drule_all extend_live_place_typed_success >> simp[]) >>
  gvs[select_result_def, extend_place_def, bind_def, lift_option_type_def,
      return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  Cases_on `sb` >> gvs[extend_place_def, bind_def, lift_option_type_def,
      return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  rename1 `HashMapRef tr slot kt value_ty` >> Cases_on `value_ty` >>
  gvs[bind_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def]
QED

Theorem extend_typed_result_live[local]:
  state_well_typed st /\ eval_result_typed (env,cx,st) bp vt /\
  live_memory_result st bp /\
  extend_place cx bp sb st = (INL pv,u) ==>
  live_memory_result u pv
Proof
  rpt strip_tac >> Cases_on `bp`
  >- gvs[extend_place_def, raise_def]
  >- (Cases_on `vt` >> gvs[eval_result_typed_def] >>
      drule_all extend_live_place_typed_success >> simp[]) >>
  Cases_on `sb` >> gvs[extend_place_def, raise_def] >>
  rename1 `HashMapRef tr slot kt value_ty` >> Cases_on `value_ty` >>
  gvs[extend_place_def, bind_def, lift_option_type_def, return_def,
      raise_def, AllCaseEqs(), live_memory_result_def]
QED

Theorem extend_live_place_attribute_no_type_error[local]:
  state_well_typed st /\ runtime_place_typed cx st p tv /\
  live_memory_result st (PlaceR p) /\
  subscript_type tv (AttrSubscript id) = SOME etv /\
  extend_place cx (PlaceR p) (AttrSubscript id) st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `place_type_value cx p st = (INL tv,st)` by
    gvs[runtime_place_typed_def] >>
  Cases_on `p`
  >- (gvs[runtime_place_typed_storage, extend_place_def] >>
      drule extend_storage_place_attribute_ready >>
      disch_then (qspecl_then [`b`, `st`, `c`, `cx`] strip_assume_tac) >>
      gvs[bind_def, return_def, no_type_error_result_def]) >>
  gvs[extend_place_def, bind_def, ignore_bind_def, AllCaseEqs(),
      return_def, no_type_error_result_def] >>
  TRY (rename1 `read_place cx loc st = (INR err,st')` >>
       drule_all read_place_typed_error >> simp[] >> NO_TAC) >>
  drule_all read_live_place_success_type >> strip_tac >>
  drule_all evaluate_subscripts_attribute_ready >> strip_tac >>
  gvs[lift_sum_def, return_def]
QED

Theorem array_subscript_place_check[local]:
  value_has_type (ArrayTV etv bd) a /\
  evaluate_subscripts (ArrayTV etv bd) a [ValueSubscript (IntV i)] = r ==>
  (!msg. r <> INR (TypeError msg)) /\
  (case r of INL v => subscript_type (ArrayTV etv bd) (ValueSubscript (IntV i)) = SOME etv
   | INR err => T)
Proof
  Cases_on `a` >> simp[value_has_type_inv] >>
  TRY (rename1 `value_has_type (ArrayTV _ _) (StructV _)` >>
       simp[value_has_type_inv] >> NO_TAC) >>
  simp[evaluate_subscripts_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `a'` >> Cases_on `bd` >>
  gvs[value_has_type_inv, array_index_def, subscript_type_def,
      bound_length_def, AllCaseEqs(), oEL_THM]
QED

Theorem extend_storage_array_place_sound[local]:
  well_formed_type_value (ArrayTV etv bd) /\
  extend_storage_place cx tr slot (ArrayTV etv bd) (ValueSubscript (IntV i)) st = (res,st') ==>
  no_type_error_result res /\
  case res of INL p => runtime_place_typed cx st' p etv | INR err => T
Proof
  Cases_on `bd` >>
  simp[extend_storage_place_def, resolve_array_element_def, bind_def,
       ignore_bind_def, check_def, assert_def, return_def, raise_def,
       AllCaseEqs(), get_storage_backend_def, get_accounts_def,
       get_transient_storage_def] >>
  rpt strip_tac >> gvs[no_type_error_result_def, well_formed_type_value_def] >>
  Cases_on `etv` >>
  gvs[resolve_array_element_def, return_def, runtime_place_typed_storage,
      vyperMiscTheory.prod_CASE_rator, AllCaseEqs()] >>
  metis_tac[get_storage_backend_no_error]
QED

Theorem extend_storage_tuple_place_sound[local]:
  well_formed_type_value (TupleTV tvs) /\
  extend_storage_place cx tr slot (TupleTV tvs) (ValueSubscript (IntV i)) st = (res,st') ==>
  no_type_error_result res /\
  case res of INL p => runtime_place_typed cx st' p (EL (Num i) tvs) | INR err => T
Proof
  simp[extend_storage_place_def, bind_def, ignore_bind_def, check_def,
       assert_def, return_def, raise_def, lift_option_type_def,
       vyperMiscTheory.option_CASE_rator, oEL_THM, AllCaseEqs()] >>
  rpt strip_tac >> gvs[no_type_error_result_def] >>
  irule vyperPlaceStatePreservationTheory.subscript_type_well_formed >>
  qexistsl_tac [`ValueSubscript (IntV i)`, `TupleTV tvs`] >>
  simp[subscript_type_def]
QED

Theorem extend_live_array_place_sound[local]:
  state_well_typed st /\ runtime_place_typed cx st p (ArrayTV etv bd) /\
  live_memory_result st (PlaceR p) /\
  extend_place cx (PlaceR p) (ValueSubscript (IntV i)) st = (res,st') ==>
  no_type_error_result res /\
  case res of INL pv => ?q. pv = PlaceR q /\ runtime_place_typed cx st' q etv | INR err => T
Proof
  rpt gen_tac >> strip_tac >>
  `st' = st` by metis_tac[vyperPlaceFramesTheory.extend_place_state, SND] >> gvs[] >>
  `place_type_value cx p st = (INL (ArrayTV etv bd),st)` by
    gvs[runtime_place_typed_def] >>
  Cases_on `p`
  >- (gvs[runtime_place_typed_storage, extend_place_def, bind_def, AllCaseEqs()] >>
      drule_all extend_storage_array_place_sound >>
      gvs[return_def, no_type_error_result_def] >> metis_tac[]) >>
  gvs[extend_place_def, bind_def, ignore_bind_def, return_def,
      AllCaseEqs()] >>
  TRY (rename1 `read_place cx _ st = (INR err,_)` >>
       drule_all read_place_typed_error >> simp[no_type_error_result_def] >> NO_TAC) >>
  imp_res_tac read_place_preserves_state >> gvs[] >>
  drule_all read_live_place_success_type >> strip_tac >>
  gvs[lift_sum_def, return_def, raise_def, vyperMiscTheory.sum_CASE_rator, AllCaseEqs()] >>
  drule_all array_subscript_place_check >> strip_tac >>
  gvs[no_type_error_result_def] >>
  irule extend_memory_place_type >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem extend_live_tuple_place_sound[local]:
  state_well_typed st /\ runtime_place_typed cx st p (TupleTV tvs) /\
  live_memory_result st (PlaceR p) /\
  subscript_type (TupleTV tvs) (ValueSubscript (IntV i)) = SOME etv /\
  extend_place cx (PlaceR p) (ValueSubscript (IntV i)) st = (res,st') ==>
  no_type_error_result res /\
  case res of INL pv => ?q. pv = PlaceR q /\ runtime_place_typed cx st' q etv | INR err => T
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (`st' = st` by metis_tac[vyperPlaceFramesTheory.extend_place_state, SND] >> gvs[] >>
      `place_type_value cx p st = (INL (TupleTV tvs),st)` by
        gvs[runtime_place_typed_def] >>
      Cases_on `p`
      >- (gvs[runtime_place_typed_storage, extend_place_def, bind_def, AllCaseEqs()] >>
          drule_all extend_storage_tuple_place_sound >>
          gvs[return_def, no_type_error_result_def]) >>
      gvs[extend_place_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()] >>
      TRY (rename1 `read_place cx _ st = (INR err,_)` >>
           drule_all read_place_typed_error >> simp[no_type_error_result_def] >> NO_TAC) >>
      imp_res_tac read_place_preserves_state >> gvs[] >>
      drule_all read_live_place_success_type >> strip_tac >>
      `well_formed_type_value (TupleTV tvs)` by gvs[runtime_place_typed_def] >>
      gvs[lift_sum_def, return_def, raise_def, vyperMiscTheory.sum_CASE_rator,
          AllCaseEqs(), no_type_error_result_def] >>
      drule_at (Pat `evaluate_subscripts _ _ _ = _`) evaluate_subscripts_typed_error >>
      simp[subscripts_type_def]) >>
  Cases_on `res` >> simp[] >>
  drule extend_place_place_success_shape >> strip_tac >> gvs[] >>
  metis_tac[extend_place_typed]
QED

Theorem subscript_vtype_well_formed_stmt[local]:
  !tenv base_vt idx_ty result_vt.
    well_formed_vtype tenv base_vt /\
    subscript_vtype base_vt idx_ty = SOME result_vt ==>
    well_formed_vtype tenv result_vt
Proof
  Cases_on `base_vt` >>
  simp[subscript_vtype_def, well_formed_vtype_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `t` >>
      gvs[subscript_vtype_def, well_formed_vtype_def,
          well_formed_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `evaluate_type tenv t'` >> gvs[]) >>
  gvs[]
QED

(* One-step interface for the pinned HOL mutual AST induction bug HOL#2115. *)
Theorem base_assignment_target_induct[local]:
  !P. (!id. P (NameTarget id)) /\ (!nsid. P (TopLevelNameTarget nsid)) /\
      (!bt e. P bt ==> P (SubscriptTarget bt e)) /\
      (!bt s. P bt ==> P (AttributeTarget bt s)) ==> !bt. P bt
Proof
  rpt strip_tac >>
  `(!e:expr. T) /\ !bt. P bt` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[]
QED

Theorem type_place_target_well_formed_vtype_stmt[local]:
  !bt env cx st vt. env_consistent env cx st /\
    type_place_target env bt = SOME vt ==> well_formed_vtype env.type_defs vt
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> BETA_TAC >> rpt gen_tac
  >- (simp[type_place_target_NameTarget] >> rpt strip_tac >> gvs[] >>
      gvs[env_consistent_def, env_scopes_consistent_def] >>
      first_x_assum drule >> strip_tac >>
      qpat_x_assum `!id ty entry. _ ==> evaluate_type _ _ = _`
        (drule_all_then assume_tac) >>
      fs[env_context_consistent_def, well_formed_vtype_def,
         well_formed_type_def, IS_SOME_EXISTS] >> metis_tac[])
  >- (rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      simp[type_place_target_TopLevelNameTarget] >>
      rpt strip_tac >> gvs[env_consistent_def, env_context_consistent_def] >>
      metis_tac[])
  >- (simp[type_place_target_SubscriptTarget] >> rpt strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      metis_tac[subscript_vtype_well_formed_stmt]) >>
  simp[type_place_target_AttributeTarget] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  gvs[well_formed_vtype_def, well_formed_type_def, IS_SOME_EXISTS] >>
  drule_all attribute_type_runtime_step >> strip_tac >> metis_tac[]
QED

Theorem extend_target_array_place_sound[local]:
  state_well_typed st /\ live_memory_result st (PlaceR p) /\
  eval_result_typed (env,cx,st) (PlaceR p) (Type (ArrayT elem bd)) /\
  expr_result_typed env e (Value v) /\ is_int_type (expr_type e) /\
  extend_place cx (PlaceR p) (ValueSubscript v) st = (res,st') ==>
  no_type_error_result res /\
  case res of INL pv => eval_result_typed (env,cx,st') pv (Type elem) | INR err => T
Proof
  simp[eval_result_typed_def, evaluate_type_def,
       expr_result_typed_def, expr_runtime_typed_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `expr_type e` >> gvs[is_int_type_def, evaluate_type_def,
       AllCaseEqs(), value_result_typed_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  drule_all extend_live_array_place_sound >> strip_tac >> simp[] >>
  Cases_on `res` >> gvs[] >> simp[eval_result_typed_def] >> metis_tac[]
QED

Theorem extend_target_hashmap_place_sound[local]:
  env_consistent env cx st /\
  well_formed_vtype env.type_defs (HashMapT kt leaf) /\
  subscript_vtype (HashMapT kt leaf) (expr_type e) = SOME out /\
  extend_place cx (HashMapRef tr slot kt leaf) (ValueSubscript v) st = (res,st') ==>
  no_type_error_result res /\
  case res of INL pv => eval_result_typed (env,cx,st') pv out | INR err => T
Proof
  simp[subscript_vtype_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  Cases_on `leaf` >>
  gvs[well_formed_vtype_def, well_formed_type_def, IS_SOME_EXISTS,
      extend_place_def, bind_def, lift_option_type_def, return_def, raise_def,
      AllCaseEqs()] >>
  simp[no_type_error_result_def, eval_result_typed_def, runtime_place_typed_def,
       place_type_value_def, return_def] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

Theorem extend_target_subscript_place_sound[local]:
  env_consistent env cx st /\ state_well_typed st /\
  well_formed_vtype env.type_defs bvt /\
  eval_result_typed (env,cx,st) pv bvt /\ live_memory_result st pv /\
  (case pv of Value _ => F | _ => T) /\
  subscript_vtype bvt (expr_type e) = SOME out /\ expr_result_typed env e (Value v) /\
  extend_place cx pv (ValueSubscript v) st = (res,st') ==>
  no_type_error_result res /\
  case res of INL q => eval_result_typed (env,cx,st') q out | INR err => T
Proof
  rpt gen_tac >> strip_tac >> Cases_on `pv`
  >- gvs[]
  >- (Cases_on `bvt`
      >- (rename1 `Type base_ty` >> Cases_on `base_ty` >>
          gvs[subscript_vtype_def] >>
          `eval_result_typed (env,cx,st) (PlaceR p) (Type (ArrayT t b))` by
            simp[eval_result_typed_def] >>
          drule_all extend_target_array_place_sound >> simp[]) >>
      gvs[eval_result_typed_def]) >>
  Cases_on `bvt` >> gvs[eval_result_typed_def] >>
  drule_all extend_target_hashmap_place_sound >>
  simp[eval_result_typed_def]
QED

(* Split only the new outer contracts, not the old ordinary/place result pair. *)
fun has_soundness_aux_conj tm =
  if is_forall tm then has_soundness_aux_conj (snd (dest_forall tm))
  else if is_imp tm then has_soundness_aux_conj (snd (dest_imp tm))
  else is_conj tm andalso
    (free_in ``typed_scope_transition`` (snd (dest_conj tm)) orelse
     free_in ``live_memory_result`` (snd (dest_conj tm)) orelse
     free_in ``writable_place_result`` (snd (dest_conj tm)));

fun expose_soundness_aux_tac g =
  if has_soundness_aux_conj (snd g) then
    ((if is_conj (snd g) then conj_tac
      else if is_forall (snd g) then gen_tac
      else disch_then strip_assume_tac) >> expose_soundness_aux_tac) g
  else all_tac g;

(* Trace roots are keyed by the outer evaluator equation, never by an IH. *)
val soundness_root_inventory = ref ([] : string list);
val trace_root_inventory = ref ([] : (string * term) list);
fun trace_root_key tm =
  let val body = #2 (strip_forall tm)
      val (premises,conclusion) = dest_imp body
      val _ = if same_const (fst (strip_comb conclusion)) ``typed_scope_transition``
              then () else raise Fail "Not a scope-transition conclusion"
      val equation = List.last (strip_conj premises)
      val (evaluator,args) = strip_comb (lhs equation)
      fun name t = #1 (dest_const (fst (strip_comb t)))
      val operation = name evaluator
      val arg = el 2 args
      val constructor = if operation = "eval_target_place" then "" else name arg
      val suffix =
        case operation of
          "eval_target_place" => "Target"
        | "eval_base_place" => "Base_" ^ constructor
        | "eval_exprs" => if listSyntax.is_nil arg then "Exprs_nil" else "Exprs_cons"
        | "eval_expr_results" =>
            if listSyntax.is_nil arg then "Results_nil" else "Results_cons"
        | "eval_abi_expr" => "AbiExpr_" ^ constructor
        | "eval_abi_exprs" => if listSyntax.is_nil arg then "AbiExprs_nil" else "AbiExprs_cons"
        | "eval_expr" => "Expr_" ^ constructor ^
            (if constructor = "Call" then "_" ^ name (el 2 (#2 (strip_comb arg))) else "")
        | _ => raise Fail ("Unknown transition evaluator: " ^ operation)
  in "Trace_" ^ suffix end;
fun suspend_trace_root g =
  let val tm = #2 g
      val label = trace_root_key tm
      val _ = if List.exists (fn (key,_) => key = label) (!trace_root_inventory)
              then raise Fail ("Duplicate transition root: " ^ label) else ()
      val _ = trace_root_inventory := !trace_root_inventory @ [(label,tm)]
  in suspend label g end;

val live_root_inventory = ref ([] : (string * term) list);
fun live_root_key tm =
  let val body = #2 (strip_forall tm)
      val (premises,conclusion) = dest_imp body
      val _ = if free_in ``live_memory_result`` conclusion then ()
              else raise Fail "Not a live-result conclusion"
      val (evaluator,args) = strip_comb (lhs (List.last (strip_conj premises)))
      fun name t = #1 (dest_const (fst (strip_comb t)))
      val operation = name evaluator
      val arg = el 2 args
      val suffix =
        case operation of
          "eval_target_place" => "Target"
        | "eval_base_place" => "Base_" ^ name arg
        | "eval_expr" => "Expr_" ^ name arg ^
            (if name arg = "Call" then "_" ^ name (el 2 (#2 (strip_comb arg))) else "")
        | _ => raise Fail ("Unknown live-result evaluator: " ^ operation)
  in "LiveRoot" ^ suffix end;
fun suspend_live_root g =
  let val tm = #2 g
      val label = live_root_key tm
      val _ = if List.exists (fn (key,_) => key = label) (!live_root_inventory)
              then raise Fail ("Duplicate live-result root: " ^ label) else ()
      val _ = live_root_inventory := !live_root_inventory @ [(label,tm)]
  in suspend label g end;

Theorem eval_scc_type_sound_results_mutual:
  (!cx s. !env ret_ty env' st res st'.
    type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    eval_stmt cx s st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL _ => env_consistent env' cx st'
    | INR exn => env_consistent env cx st' /\ return_exception_typed env ret_ty exn) /\
  (!cx ss. !env ret_ty env' st res st'.
    type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    eval_stmts cx ss st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL _ => env_consistent env' cx st'
    | INR exn => ?env_exn. env_extends env env_exn /\ env_consistent env_exn cx st' /\
                           return_exception_typed env_exn ret_ty exn) /\
  (!cx it. !env ty st res st'.
    well_typed_iterator env ty it /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_iterator it) /\
    eval_iterator cx it st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL vs => ?tyv. evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs
    | INR _ => T) /\
  (!cx tyv id body vs. !env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    eval_for cx tyv id body vs st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ env_consistent env cx st' /\
    no_type_error_result res /\
    case res of
    | INR exn => return_exception_typed env ret_ty exn
    | INL _ => T) /\
  (!cx e. (!env st res st'.
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\ eval_expr cx e st = (res,st') ==>
    ((well_typed_expr env e ==>
      state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
      no_type_error_result res /\
      case res of INL pv => eval_result_typed (env,cx,st') pv (Type (expr_type e)) | INR _ => T) /\
     (!vt. type_place_expr env e = SOME vt ==>
      state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
      no_type_error_result res /\
      case res of INL pv => eval_result_typed (env,cx,st') pv vt | INR _ => T))) /\
   (!env st res st'.
    (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\ eval_expr cx e st = (res,st') ==>
    typed_scope_transition st st') /\
   (!env st res st'.
    (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\ eval_expr cx e st = (res,st') ==>
    case res of INL pv => live_memory_result st' pv | INR _ => T)) /\
  (!cx es. (!env st res st'.
    well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    eval_exprs cx es st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL vs => exprs_runtime_typed env es vs
    | INR _ => T) /\
   (!env st res st'.
    well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\ eval_exprs cx es st = (res,st') ==>
    typed_scope_transition st st')) /\
  (!cx bt. (!env vt st res st'.
    type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_base_place cx bt st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of INL pv => eval_result_typed (env,cx,st') pv vt | INR _ => T) /\
   (!env vt st res st'.
    type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_base_place cx bt st = (res,st') ==>
    typed_scope_transition st st') /\
   (!env vt st res st'.
    type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_base_place cx bt st = (res,st') ==>
    case res of INL pv => live_memory_result st' pv | INR _ => T) /\
   (!env vt st res st'.
    type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_base_place cx bt st = (res,st') ==>
    case res of INL pv => writable_place_result cx st' pv | INR _ => T)) /\
  (!cx bt. (!env ty st res st'.
    well_typed_target env bt ty /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_target_place cx bt st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of INL p => eval_result_typed (env,cx,st') (PlaceR p) (Type ty) | INR _ => T) /\
   (!env ty st res st'.
    well_typed_target env bt ty /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_target_place cx bt st = (res,st') ==>
    typed_scope_transition st st') /\
   (!env ty st res st'.
    well_typed_target env bt ty /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_target_place cx bt st = (res,st') ==>
    case res of INL p => live_memory_result st' (PlaceR p) | INR _ => T) /\
   (!env ty st res st'.
    well_typed_target env bt ty /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_target_place cx bt st = (res,st') ==>
    case res of INL p => writable_place_result cx st' (PlaceR p) | INR _ => T)) /\
  (!cx g v. !env ty st res st'.
    well_typed_atarget env g ty /\ value_runtime_typed env ty v /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget g) /\ assign_tuple_targets cx g v st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res) /\
  (!cx gs vs. !env tys st res st'.
    LIST_REL (\g ty. well_typed_atarget env g ty) gs tys /\
    LIST_REL (value_runtime_typed env) tys vs /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets gs) /\ assign_tuple_target_list cx gs vs st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res) /\
  (!cx es. (!env st res st'.
    well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    eval_expr_results cx es st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of INL results => expr_results_typed (env,cx,st') es results | INR _ => T) /\
   (!env st res st'.
    well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    eval_expr_results cx es st = (res,st') ==> typed_scope_transition st st')) /\
  (!cx e. (!env st res st'.
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\ eval_abi_expr cx e st = (res,st') ==>
    ((well_typed_expr env e ==>
      state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
      no_type_error_result res /\
      case res of INL arg => abi_expr_result_valid env st' e arg | INR _ => T) /\
     (!vt. type_place_expr env e = SOME vt ==>
      state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
      no_type_error_result res /\
      case res of INL arg => abi_place_result_valid env st' arg vt | INR _ => T))) /\
   (!env st res st'.
    (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\ eval_abi_expr cx e st = (res,st') ==>
    typed_scope_transition st st')) /\
  (!cx es. (!env st res st'.
    well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\ eval_abi_exprs cx es st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of INL args => abi_exprs_result_valid env st' es args | INR _ => T) /\
   (!env st res st'.
    well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\ eval_abi_exprs cx es st = (res,st') ==>
    typed_scope_transition st st'))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> expose_soundness_aux_tac >>
  (fn (g as (asms,w)) =>
    let
      fun head tm = #Name (dest_thy_const (#1 (strip_comb tm)))
      fun app tm =
        let val (h,args) = strip_comb tm
            val n = #Name (dest_thy_const h)
        in (List.exists (fn s => s = n) ["eval_stmt", "eval_stmts", "eval_iterator", "eval_for",
              "eval_expr", "eval_exprs", "eval_expr_results", "eval_base_place", "eval_target_place",
              "eval_abi_expr", "eval_abi_exprs"]
            andalso length args = (if n = "eval_for" then 6 else 3)) orelse
           (List.exists (fn s => s = n) ["assign_tuple_targets", "assign_tuple_target_list"] andalso
            length args = 4)
        end handle HOL_ERR _ => false
      val body = #2 (strip_forall w)
      val equations = if is_imp body then strip_conj (fst (dest_imp body)) else asms
      val outer = List.filter (fn a => is_eq a andalso app (lhs a)) equations
      val tm = case outer of [equation] => lhs equation
             | _ => raise Fail "Expected one outer evaluator equation"
      val (h,args) = strip_comb tm
      val n = head h
      val arg = el 2 args
      fun shape t = if listSyntax.is_nil t then "nil" else "cons"
      fun expr_label e =
        let val (_,xs) = strip_comb e
        in if head e = "Call" then "Expr_Call_" ^ head (el 2 xs)
           else "Expr_" ^ head e end
      fun stmt_label s =
        let val (_,xs) = strip_comb s
            val c = head s
        in if c = "Return" then "Return_" ^ head (hd xs)
           else if c = "Raise" then head (hd xs)
           else if c = "Assert" then head (el 2 xs)
           else if c = "Assign" then
             (if head (hd xs) = "BaseTarget" then "Assign_Base" else "Assign_Tuple")
           else c end
      val is_trace = free_in ``typed_scope_transition`` w
      val is_live = free_in ``live_memory_result`` w
      val is_writable = free_in ``writable_place_result`` w
      val label =
        if is_writable then
          (if n = "eval_target_place" then "WritableRootTarget"
           else "WritableRootBase_" ^ head arg)
        else if is_live then
          (if n = "eval_target_place" then "LiveRootTarget"
           else if n = "eval_base_place" then "LiveRootBase_" ^ head arg
           else "LiveRootExpr_" ^ head arg)
        else if n = "eval_stmt" then stmt_label arg
        else if n = "eval_stmts" then "Stmts_" ^ shape arg
        else if n = "eval_iterator" then "Iterator_" ^ head arg
        else if n = "eval_for" then "For_" ^ shape (el 5 args)
        else if n = "eval_abi_expr" then "AbiExpr_" ^ head arg
        else if n = "eval_abi_exprs" then "AbiExprs_" ^ shape arg
        else if n = "eval_expr" then expr_label arg
        else if n = "eval_exprs" then "Exprs_" ^ shape arg
        else if n = "eval_expr_results" then "Results_" ^ shape arg
        else if n = "eval_base_place" then "BasePlaceRoot_" ^ head arg
        else if n = "eval_target_place" then "TargetPlace"
        else if n = "assign_tuple_targets" then "TupleStore_" ^ head arg
        else if n = "assign_tuple_target_list" then
          "TupleStores_" ^ shape arg ^ "_" ^ shape (el 3 args)
        else raise Fail ("Unknown soundness evaluator: " ^ n)
      val key = if is_trace then trace_root_key w
                else if is_live then live_root_key w else label
      val _ = if List.exists (fn seen => seen = key) (!soundness_root_inventory)
              then raise Fail ("Duplicate soundness root: " ^ key) else ()
      val _ = soundness_root_inventory := key :: !soundness_root_inventory
    in
      if is_trace then suspend_trace_root g
      else if is_live then suspend_live_root g
      else if label = "Expr_Call_ExtCall" then
        (rpt gen_tac >> strip_tac >>
         reverse conj_tac >- (
           rpt gen_tac >> strip_tac >>
           qpat_x_assum `type_place_expr _ (Call _ (ExtCall _ _ _ _) _ _) = SOME _` mp_tac >>
           simp[type_place_expr_Call_ExtCall_NONE]) >>
         suspend "Expr_Call_ExtCall_result") g
      else suspend label g
    end)
QED

Resume eval_scc_type_sound_results_mutual[Pass]:
  gvs[evaluate_def, return_def, no_type_error_result_def, type_stmt_def]
QED

Resume eval_scc_type_sound_results_mutual[Continue]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_scc_type_sound_results_mutual[Break]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_scc_type_sound_results_mutual[Return_NONE]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def, value_runtime_typed_def, value_has_type_def,
      evaluate_type_def]
QED

Resume eval_scc_type_sound_results_mutual[Return_SOME]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (er,s1)` >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Return (SOME e)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_expr_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `er` >> gvs[no_type_error_result_def]
  >- (
    rename1 `eval_expr cx e st = (INL tv,s1)` >>
    `live_memory_result s1 tv` by (
      qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
        (qspecl_then [`env`, `st`, `INL tv`, `s1`] mp_tac) >> simp[]) >>
    Cases_on `read_result cx tv s1` >>
    rename1 `read_result cx tv s1 = (mr,s2)` >>
    Cases_on `mr` >> gvs[raise_def, no_type_error_result_def]
    >- (
      drule read_result_state >> strip_tac >> gvs[] >>
      strip_tac >> gvs[] >>
      drule_all live_result_read_typed >> strip_tac >>
      gvs[return_exception_typed_def, value_runtime_typed_def] >>
      metis_tac[type_widens_to_value_has_type]) >>
    drule read_result_state >> strip_tac >> gvs[] >>
    strip_tac >> gvs[] >>
    conj_tac >- (drule_all live_result_read_typed >>
      simp[no_type_error_result_def]) >>
    drule read_result_no_control >> strip_tac >>
    Cases_on `y` >> gvs[no_control_exc_def, return_exception_typed_def]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[RaiseBare]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_scc_type_sound_results_mutual[RaiseUnreachable]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_scc_type_sound_results_mutual[RaiseReason]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_raise_reason_def] >> strip_tac >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  rpt gen_tac >> reverse strip_tac >- (
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum drule_all >> simp[] >>
    drule_all eval_expr_exception_return_typed >>
    rw[] >> gvs[no_type_error_result_def]) >>
  BasicProvers.VAR_EQ_TAC >>
  first_x_assum drule_all >> simp[] >> strip_tac >>
  gvs[] >> rename1 `eval_expr cx e st = (INL pv,mid)` >>
  `live_memory_result mid pv` by (
    qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
      (qspecl_then [`env`, `st`, `INL pv`, `mid`] mp_tac) >> simp[]) >>
  drule_all live_result_read_typed >> strip_tac >>
  gvs[value_runtime_typed_def, evaluate_type_def, no_type_error_result_def,
      return_exception_typed_def, value_has_type_StringTV, AllCaseEqs(),
      dest_StringV_def, lift_option_type_def, return_def, raise_def] >>
  imp_res_tac value_has_type_StringTV >>
  gvs[dest_StringV_def, return_def, raise_def, no_type_error_result_def,
      return_exception_typed_def] >>
  drule read_result_no_control >> strip_tac >>
  Cases_on `e'` >> gvs[no_control_exc_def]
QED

Resume eval_scc_type_sound_results_mutual[AssertBare]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e AssertBare))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def, APPEND_NIL] >> strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    `live_memory_result st1 x` by (
      qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
        (qspecl_then [`env`, `st`, `INL x`, `st1`] mp_tac) >> simp[]) >>
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (loaded,st2)` >>
    drule_all live_result_read_typed >> strip_tac >> gvs[] >>
    reverse (Cases_on `loaded`)
    >- (drule read_result_no_control >> strip_tac >>
        Cases_on `y` >>
        gvs[switch_BoolV_def, bind_def, raise_def, no_control_exc_def,
            no_type_error_result_def, return_exception_typed_def] >>
        rpt strip_tac >> gvs[]) >>
    gvs[value_runtime_typed_def, evaluate_type_def] >>
    drule value_has_type_BoolTV >> strip_tac >> gvs[] >>
    Cases_on `b` >>
    gvs[switch_BoolV_def, bind_def, return_def, raise_def,
        no_type_error_result_def, return_exception_typed_def] >>
    rpt strip_tac >> gvs[]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[AssertUnreachable]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e AssertUnreachable))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def, APPEND_NIL] >> strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    `live_memory_result st1 x` by (
      qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
        (qspecl_then [`env`, `st`, `INL x`, `st1`] mp_tac) >> simp[]) >>
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (loaded,st2)` >>
    drule_all live_result_read_typed >> strip_tac >> gvs[] >>
    reverse (Cases_on `loaded`)
    >- (drule read_result_no_control >> strip_tac >>
        Cases_on `y` >>
        gvs[switch_BoolV_def, bind_def, raise_def, no_control_exc_def,
            no_type_error_result_def, return_exception_typed_def] >>
        rpt strip_tac >> gvs[]) >>
    gvs[value_runtime_typed_def, evaluate_type_def] >>
    drule value_has_type_BoolTV >> strip_tac >> gvs[] >>
    Cases_on `b` >>
    gvs[switch_BoolV_def, bind_def, return_def, raise_def,
        no_type_error_result_def, return_exception_typed_def] >>
    rpt strip_tac >> gvs[]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[AssertReason]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason e')))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac) >>
  Cases_on `expr_res` >> rewrite_tac[no_type_error_result_def]
  >- (
    qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
    qpat_x_assum `!vt. _` kall_tac >>
    qpat_x_assum `case INL x of INL pv => eval_result_typed _ pv _ | INR _ => T` mp_tac >>
    simp_tac (srw_ss()) [] >> strip_tac >>
    `live_memory_result st1 x` by (
      qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
        (qspecl_then [`env`, `st`, `INL x`, `st1`] mp_tac) >> simp[]) >>
    qpat_x_assum `!s tv t. eval_expr cx e s = (INL tv,t) ==> _`
      (drule_then (mk_asm "reason_ih")) >>
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (loaded,st2)` >>
    drule_all live_result_read_typed >> strip_tac >> gvs[] >>
    reverse (Cases_on `loaded`)
    >- (drule read_result_no_control >> strip_tac >>
        Cases_on `y` >>
        gvs[switch_BoolV_def, bind_def, raise_def, no_control_exc_def,
            no_type_error_result_def, return_exception_typed_def] >>
        rpt strip_tac >> gvs[]) >>
    gvs[value_runtime_typed_def, evaluate_type_def] >>
    drule value_has_type_BoolTV >> strip_tac >> gvs[] >>
    Cases_on `b` >> simp[switch_BoolV_def, bind_def, return_def]
    >- (rpt strip_tac >> gvs[no_type_error_result_def]) >>
    asm_x "reason_ih" strip_assume_tac >>
    Cases_on `eval_expr cx e' st1` >>
    rename1 `eval_expr cx e' st1 = (reason_res, st2)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `reason_res` >> gvs[no_type_error_result_def]
    >- (
      `live_memory_result st2 x'` by (
        qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
          (qspecl_then [`env`, `st1`, `INL x'`, `st2`] mp_tac) >> simp[]) >>
      Cases_on `read_result cx x' st2` >>
      rename1 `read_result cx x' st2 = (reason_loaded,st3)` >>
      drule_all live_result_read_typed >> strip_tac >> gvs[] >>
      reverse (Cases_on `reason_loaded`)
      >- (drule read_result_no_control >> strip_tac >>
          Cases_on `y` >>
          gvs[no_control_exc_def, return_exception_typed_def,
              no_type_error_result_def] >> rpt strip_tac >> gvs[]) >>
      gvs[value_runtime_typed_def, evaluate_type_def] >>
      drule value_has_type_StringTV >> strip_tac >>
      gvs[dest_StringV_def, lift_option_type_def, return_def, raise_def,
          no_type_error_result_def, return_exception_typed_def] >>
      rpt strip_tac >> gvs[]) >>
    gvs[bind_def, no_type_error_result_def] >>
    rw[] >>
    drule eval_expr_exception_return_typed >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!s tv t. eval_expr cx e s = (INL tv,t) ==> _` kall_tac >>
  qpat_x_assum `!vt. _` kall_tac >>
  gvs[no_type_error_result_def] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[Log]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Log id es))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, push_log_def,
       no_type_error_result_def, AllCaseEqs()] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (exprs_res, st1)` >>
  qpat_x_assum `!env st res st'. _ ==> _ /\ env_consistent _ _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  Cases_on `exprs_res` >> gvs[no_type_error_result_def]
  >- (
    strip_tac >> gvs[state_well_typed_def, accounts_well_typed_def] >>
    Cases_on `encode_source_event (get_tenv cx) cx.sources cx.txn.target id x` >>
    gvs[lift_option_def, return_def, raise_def] >>
    drule_all env_consistent_logs_append >>
    simp[return_exception_typed_def]) >>
  strip_tac >> gvs[] >>
  drule eval_exprs_exception_return_typed >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[AnnAssign]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  `get_tenv cx = env.type_defs` by fs[env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type env.type_defs typ = SOME tyv` by
    (qspecl_then [`env.type_defs`,`typ`] mp_tac assignable_type_well_formed >>
     simp[] >> rewrite_tac[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  pop_assum strip_assume_tac >>
  irule annassign_statement_sound_from_expr_ih >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (qexists_tac `tyv` >> simp[]) >>
  conj_tac >- simp[] >>
  qexists_tac `e` >> qexists_tac `st` >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!tenv s'' tyv t. _`
        (qspecl_then [`env.type_defs`, `st`, `tyv`, `st`] mp_tac) >>
      simp[lift_option_type_def, return_def] >>
      strip_tac >>
      qpat_x_assum `!env st res st'. _ ==> _ /\ !vt. _`
        (drule_all_then strip_assume_tac) >>
      qpat_x_assum `well_typed_expr env' e ==> _` (drule_then strip_assume_tac) >>
      qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
        (qspecl_then [`env'`, `st''`, `res'`, `st'''`] mp_tac) >>
      simp[] >> Cases_on `res'` >> gvs[]) >>
  rpt conj_tac >> asm_rewrite_tac[]
QED

Resume eval_scc_type_sound_results_mutual[Append]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Append bt e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_target bt` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >>
  Cases_on `type_place_target env bt` >- simp[NoAsms] >>
  simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME vt` >>
  Cases_on `vt` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type ty)` >>
  Cases_on `ty` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty bd))` >>
  Cases_on `bd` >- simp[NoAsms] >>
  simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty (Dynamic n)))` >>
  strip_tac >>
  qpat_x_assum `env = env'` (SUBST_ALL_TAC o SYM) >>
  `well_typed_target env bt (ArrayT elem_ty (Dynamic n))` by
    simp[well_typed_target_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res, st1)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => live_memory_result _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => writable_place_result _ _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  reverse (Cases_on `target_res`)
  >- (qpat_x_assum `!s p t. eval_target_place cx bt s = (INL p,t) ==> _` kall_tac >>
      gvs[no_type_error_result_def] >> strip_tac >> gvs[] >>
      drule eval_target_place_no_control >>
      simp[no_control_exc_return_exception_typed]) >>
  simp_tac(srw_ss()) [] >>
  qpat_x_assum `!s p t. eval_target_place cx bt s = (INL p,t) ==> _`
    (drule_then strip_assume_tac) >>
  Cases_on `eval_expr cx e st1` >>
  rename1 `eval_expr cx e st1 = (expr_res,st2)` >>
  qpat_x_assum `!env st res st'. _ ==> _ /\ !vt. _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (qspecl_then [`env`, `st1`, `expr_res`, `st2`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
    (qspecl_then [`env`, `st1`, `expr_res`, `st2`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!env ty st res st'. _` kall_tac >>
  qpat_x_assum `!vt. _` kall_tac >>
  reverse (Cases_on `expr_res`)
  >- (simp[] >> strip_tac >> gvs[no_type_error_result_def] >>
      drule eval_expr_exception_return_typed >> simp[]) >>
  gvs[] >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame st1 st2` by
    (drule eval_expr_immutable_metadata_frame >> simp[]) >>
  `eval_result_typed (env,cx,st2) (PlaceR x) (Type (ArrayT elem_ty (Dynamic n)))` by
    (irule eval_result_typed_transport >> qexists_tac `st1` >> simp[]) >>
  `writable_place_result cx st2 (PlaceR x)` by
    (irule writable_place_result_transport >> qexists_tac `st1` >> simp[]) >>
  `live_memory_result st2 (PlaceR x)` by
    (Cases_on `x` >> simp[live_memory_result_def] >>
     drule_all live_memory_result_transport >> simp[live_memory_result_def]) >>
  `?elem_tv. evaluate_type env.type_defs elem_ty = SOME elem_tv /\
     runtime_place_typed cx st2 x (ArrayTV elem_tv (Dynamic n))` by
    gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `read_result cx x' st2` >>
  rename1 `read_result cx x' st2 = (loaded,st3)` >>
  drule_all live_result_read_typed >> strip_tac >> gvs[] >>
  reverse (Cases_on `loaded`)
  >- (simp[] >> strip_tac >> gvs[no_type_error_result_def] >>
      drule read_result_no_control >> simp[no_control_exc_return_exception_typed]) >>
  qmatch_assum_rename_tac `read_result cx x' st2 = (INL right,st2)` >>
  `value_runtime_typed env elem_ty right` by
    (drule_all read_live_result_widens_type >> simp[]) >>
  `value_has_type elem_tv right` by gvs[value_runtime_typed_def] >>
  strip_tac >> gvs[] >>
  `runtime_consistent env cx st2` by simp[runtime_consistent_def] >>
  `runtime_place_writable cx st2 x` by gvs[writable_place_result_def] >>
  drule_at (Pat `append_place`) append_place_sound >>
  disch_then (qspecl_then [`n`, `elem_tv`, `env`] mp_tac) >> simp[] >>
  impl_tac >- (Cases_on `x` >> gvs[live_memory_result_def] >> metis_tac[]) >>
  strip_tac >> gvs[runtime_consistent_def] >>
  Cases_on `res` >> gvs[no_type_error_result_def] >>
  drule append_place_no_control >> simp[no_control_exc_return_exception_typed]
QED

Resume eval_scc_type_sound_results_mutual[Assign_Tuple]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once type_stmt_def, atarget_accepts_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac [int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    metis_tac[call_evaluation_safe_append_right] >>
  `call_evaluation_safe cx (int_calls_atarget (TupleTarget gs))` by
    metis_tac[call_evaluation_safe_append_left] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_apply] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (er,s1)` >>
  qpat_x_assum `!env st res st'. _ ==> _ /\ !vt. _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
    (qspecl_then [`env`, `st`, `er`, `s1`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
  qpat_x_assum `!vt. _` kall_tac >>
  reverse (Cases_on `er`)
  >- (qpat_x_assum `!s tv t s' v t'. _` kall_tac >>
      simp[] >> strip_tac >> gvs[no_type_error_result_def] >>
      drule eval_expr_exception_return_typed >> simp[]) >>
  qpat_x_assum `!s tv t s' v t'. _` (mk_asm "tuple_ih") >>
  gvs[] >> rename1 `eval_expr cx e st = (INL tv,s1)` >>
  Cases_on `read_result cx tv s1` >>
  rename1 `read_result cx tv s1 = (mr,s2)` >>
  drule_all live_result_read_typed >> strip_tac >> gvs[] >>
  reverse (Cases_on `mr`)
  >- (simp[] >> strip_tac >> gvs[no_type_error_result_def] >>
      drule read_result_no_control >> simp[no_control_exc_return_exception_typed]) >>
  simp_tac(srw_ss()) [] >>
  strip_tac >> gvs[] >>
  asm_x "tuple_ih" strip_assume_tac >>
  qpat_x_assum `!s tv t s' v t'. _` (drule_all_then strip_assume_tac) >>
  gvs[] >> Cases_on `res` >> gvs[no_type_error_result_def] >>
  drule assign_tuple_targets_no_control >> simp[no_control_exc_return_exception_typed]
QED

Resume eval_scc_type_sound_results_mutual[Assign_Base]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  suspend "Assign_Base_sequence"
QED

Resume eval_scc_type_sound_results_mutual[AugAssign]:
  suspend "AugAssign_place"
QED

Resume eval_scc_type_sound_results_mutual[If]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (If e ss ss'))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  first_x_assum drule_all >> strip_tac >>
  simp_tac (srw_ss()) [] >>
  rename1 `eval_expr cx e st = (cond_res, st1)` >>
  reverse(Cases_on `cond_res`)
  >- (
    simp_tac(srw_ss())[] >>
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    simp_tac(srw_ss())[] >>
    first_x_assum drule >>
    simp_tac(srw_ss())[no_type_error_result_def] >>
    strip_tac >>
    drule_all eval_expr_exception_return_typed >> simp[]
  ) >>
  simp_tac(srw_ss())[ignore_bind_def, bind_def] >>
  CASE_TAC >>
  reverse CASE_TAC >- (
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    qpat_x_assum `push_scope st1 = (INR _,_)` mp_tac >>
    simp_tac(srw_ss())[push_scope_def,return_def]
  ) >>
  rename1 `eval_expr cx e st = (INL tv, st1)` >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result st' pv | INR _ => T`
    (qspecl_then [`env`,`st`,`INL tv`,`st1`] mp_tac) >>
  (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition st st'` kall_tac >>
  qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> _` kall_tac >>
  strip_tac >>
  qpat_x_assum `IS_SOME (type_stmts env ret_ty ss)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (type_stmts env ret_ty ss')`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  irule scope_bracket_post >>
  conj_asm1_tac >- (
    irule env_consistent_env_maps_wf >> simp[] >>
    goal_assum drule >> simp[]
  ) >>
  qmatch_asmsub_abbrev_tac`finally body_fun pop_scope sf` >>
  qexistsl_tac[`body_fun`,`st1`] >>
  PURE_REWRITE_TAC[bind_def, ignore_bind_def] >>
  ASM_REWRITE_TAC[] >>
  first_x_assum (drule_then drule) >> strip_tac >>
  last_x_assum (drule_then drule) >> strip_tac >>
  qpat_x_assum `push_scope st1 = (INL x',sf)`
    (strip_assume_tac o
     SIMP_RULE (srw_ss()) [push_scope_def, return_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  pure_rewrite_tac[pairTheory.pair_case_def, sumTheory.sum_case_def] >>
  BETA_TAC >> ASM_REWRITE_TAC[] >>
  qmatch_goalsub_abbrev_tac`body_fun st2` >>
  Cases_on`body_fun st2` >>
  simp_tac std_ss [pairTheory.PAIR_EQ, sumTheory.sum_case_def] >>
  qmatch_assum_rename_tac`body_fun st2 = (rf,sf)` >>
  qho_match_abbrev_tac`P rf sf` >>
  `st1 with scopes := FEMPTY::st1.scopes = st2` by
    simp[Abbr`st2`, evaluation_state_component_equality] >>
  irule switch_BoolV_live_empty_scope_post >>
  qexistsl_tac [`cx`,`env`,`eval_stmts cx ss'`,`eval_stmts cx ss`,`tv`,`st1`] >>
  qunabbrev_tac`body_fun` >>
  simp[] >>
  qpat_x_assum `st1 with scopes := FEMPTY::st1.scopes = st2` kall_tac >>
  conj_tac >- (
    rpt strip_tac >> qunabbrev_tac`P` >> BETA_TAC >>
    simp[Abbr`st2`] >>
    conj_tac >- (
      irule push_scope_preserves_state_well_typed >>
      qexistsl_tac [`st1`,`()`] >>
      simp[push_scope_def, return_def, evaluation_state_component_equality]) >>
    conj_tac >- gvs[no_type_error_result_def] >>
    irule no_control_exc_return_exception_typed >> simp[]) >>
  `accounts_well_typed st2.accounts` by simp[Abbr`st2`] >>
  `env_consistent env cx st2` by (simp[Abbr`st2`] >> irule push_scope_env_consistent >> simp[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    rename1 `eval_stmts cx ss' st2 = (res1,st1')` >>
    qunabbrev_tac`P` >> BETA_TAC >>
    `state_well_typed st2` by (
      irule push_scope_preserves_state_well_typed >>
      qexists_tac `st1` >> qexists_tac `()` >>
      simp[push_scope_def, return_def, Abbr`st2`]) >>
    first_x_assum drule_all >> strip_tac >>
    qpat_x_assum `!env ret_ty env' st' res st''. _` kall_tac >>
    simp[] >>
    `st2 = st1 with scopes := FEMPTY::st1.scopes`
      by simp[evaluation_state_component_equality, Abbr`st2`] >>
    conj_tac >- (
      strip_tac >> gvs[] >>
      drule eval_stmts_preserves_scopes_len >> simp[]) >>
    Cases_on `res1` >> gvs[]
    >- (
      Cases_on `st1'.scopes` >> gvs[]
      >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
      irule type_stmts_env_consistent_after_pop >> simp[] >>
      conj_tac >- (
        drule eval_stmts_preserves_scopes_len >> simp[] >>
        strip_tac >>
        `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
        Cases_on `st1.scopes` >> gvs[] >>
        Cases_on `t` >> gvs[]) >>
      conj_tac >- (
        rpt strip_tac >> fs[] >>
        drule_at(Pat`eval_stmts`)lookup_scopes_not_in_new_head >>
        simp[] >> disch_then irule >>
        qpat_x_assum`env_consistent _ _ st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
      conj_tac >- (
        qexists_tac `x''` >>
        qexists_tac `ret_ty` >>
        qexists_tac `ss'` >> simp[] >>
        rpt strip_tac >> fs[] >>
        drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def] >>
        strip_tac >> gvs[FDOM_FEMPTY] >>
        drule lookup_scopes_is_some_same_fdoms >> simp[] >>
        disch_then (qspec_then `id` mp_tac) >> simp[optionTheory.IS_SOME_EXISTS] >>
        qpat_x_assum `env_consistent env cx st1` mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
        strip_tac >> strip_tac >>
        Cases_on `lookup_scopes id t` >> gvs[] >>
        qpat_x_assum `!id entry. lookup_scopes id st1.scopes = SOME entry ==> _`
          (qspec_then `id` mp_tac) >> simp[] >> metis_tac[]) >>
      qexists_tac `st1` >> simp[] >>
      qspecl_then [`cx`, `ss'`, `FEMPTY`, `st1`, `INL ()`, `st1'`]
        mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
      simp[] >>
      disch_then irule >>
      qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
      `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
      pop_assum SUBST1_TAC >>
      irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
      qexists_tac `INL ()` >> qexists_tac `ss'` >> simp[] >>
      gvs[Abbr`stp`]) >>
    Cases_on `st1'.scopes` >> gvs[]
    >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
    conj_tac >- (
      irule env_extends_env_consistent_after_pop >> simp[] >>
      conj_tac >- (
        drule eval_stmts_preserves_scopes_len >> simp[] >>
        strip_tac >>
        `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
        Cases_on `st1.scopes` >> gvs[] >>
        Cases_on `t` >> gvs[]) >>


      conj_tac >- (
        conj_tac >- (
          rpt strip_tac >> fs[] >>
          `?entry. lookup_scopes id st1.scopes = SOME entry` by (
            qpat_x_assum`env_consistent _ _ st1`mp_tac >>
            simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
          `FLOOKUP h id = NONE` suffices_by simp[] >>
          drule lookup_scopes_not_in_new_head >>
          disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
          simp[] >>
          disch_then irule >> simp[]) >>
        rpt strip_tac >> fs[] >>
        `?entry. lookup_scopes id st1.scopes = SOME entry` by (
          qpat_x_assum`env_consistent _ _ st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
        `FLOOKUP h id = NONE` suffices_by simp[] >>
        drule lookup_scopes_not_in_new_head >>
        disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
        simp[] >>
        disch_then irule >> simp[]) >>
      conj_tac >- (
        qexists_tac `env_exn` >> simp[] >>
        rpt strip_tac >> fs[] >>
        `lookup_scopes id st1.scopes = NONE` by (
          qpat_x_assum`env_consistent env cx st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def] >> strip_tac >>
          Cases_on `lookup_scopes id st1.scopes` >> gvs[] >>
          metis_tac[optionTheory.IS_SOME_DEF]) >>
        qspecl_then [`cx`, `ss'`, `st1`, `FEMPTY`, `st1.scopes`, `INR y`, `st1'`, `id`, `h`, `t`]
          mp_tac eval_stmts_preserves_tail_lookup_none >>
        simp[]) >>
      qexists_tac `st1` >> simp[] >>
      qspecl_then [`cx`, `ss'`, `FEMPTY`, `st1`, `INR y`, `st1'`]
        mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
      simp[] >> disch_then irule >>
      qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
      `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
      pop_assum SUBST1_TAC >>
      irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
      qexists_tac `INR y` >> qexists_tac `ss'` >> simp[] >>
      gvs[Abbr`stp`]) >>
    irule env_extends_return_exception_typed >>
    qexists_tac `env_exn` >> simp[]) >>
  conj_tac >- (
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmts cx ss st2 = (res1,st1')` >>
  qunabbrev_tac`P` >> BETA_TAC >>
  `state_well_typed st2` by (
    irule push_scope_preserves_state_well_typed >>
    qexists_tac `st1` >> qexists_tac `()` >>
    simp[push_scope_def, return_def, Abbr`st2`]) >>
  first_x_assum drule_all >> strip_tac >>
  simp[] >>
  `st2 = st1 with scopes := FEMPTY::st1.scopes`
    by simp[evaluation_state_component_equality, Abbr`st2`] >>
  conj_tac >- (
    strip_tac >> gvs[] >>
    drule eval_stmts_preserves_scopes_len >> simp[]) >>
  Cases_on `res1` >> gvs[]
  >- (
    Cases_on `st1'.scopes` >> gvs[]
    >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
    irule type_stmts_env_consistent_after_pop >> simp[] >>
    conj_tac >- (
      drule eval_stmts_preserves_scopes_len >> simp[] >>
      strip_tac >>
      `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
      Cases_on `st1.scopes` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    conj_tac >- (
      rpt strip_tac >> fs[] >>
      drule_at(Pat`eval_stmts`)lookup_scopes_not_in_new_head >>
      simp[] >> disch_then irule >>
      qpat_x_assum`env_consistent _ _ st1`mp_tac >>
      simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
    conj_tac >- (
      qexists_tac `x` >>
      qexists_tac `ret_ty` >>
      qexists_tac `ss` >> simp[] >>
      rpt strip_tac >> fs[] >>
      drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def] >>
      strip_tac >> gvs[FDOM_FEMPTY] >>
      drule lookup_scopes_is_some_same_fdoms >> simp[] >>
      disch_then (qspec_then `id` mp_tac) >> simp[optionTheory.IS_SOME_EXISTS] >>
      qpat_x_assum `env_consistent env cx st1` mp_tac >>
      simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
      strip_tac >> strip_tac >>
      Cases_on `lookup_scopes id t` >> gvs[] >>
      qpat_x_assum `!id entry. lookup_scopes id st1.scopes = SOME entry ==> _`
        (qspec_then `id` mp_tac) >> simp[] >> metis_tac[]) >>
    qexists_tac `st1` >> simp[] >>
    qspecl_then [`cx`, `ss`, `FEMPTY`, `st1`, `INL ()`, `st1'`]
      mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
    simp[] >>
    disch_then irule >>
    qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
    `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
    pop_assum SUBST1_TAC >>
    irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
    qexists_tac `INL ()` >> qexists_tac `ss` >> simp[] >>
    gvs[Abbr`stp`]) >>
  Cases_on `st1'.scopes` >> gvs[]
  >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
  conj_tac >- (
    irule env_extends_env_consistent_after_pop >> simp[] >>
    conj_tac >- (
      drule eval_stmts_preserves_scopes_len >> simp[] >>
      strip_tac >>
      `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
      Cases_on `st1.scopes` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    conj_tac >- (
      conj_tac >- (
        rpt strip_tac >> fs[] >>
        `?entry. lookup_scopes id st1.scopes = SOME entry` by (
          qpat_x_assum`env_consistent _ _ st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
        `FLOOKUP h id = NONE` suffices_by simp[] >>
        drule lookup_scopes_not_in_new_head >>
        disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
        simp[] >> disch_then irule >> simp[]) >>
      rpt strip_tac >> fs[] >>
      `?entry. lookup_scopes id st1.scopes = SOME entry` by (
        qpat_x_assum`env_consistent _ _ st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
      `FLOOKUP h id = NONE` suffices_by simp[] >>
      drule lookup_scopes_not_in_new_head >>
      disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
      simp[] >> disch_then irule >> simp[]) >>
    conj_tac >- (
      qexists_tac `env_exn` >> simp[] >>
      rpt strip_tac >> fs[] >>
      `lookup_scopes id st1.scopes = NONE` by (
        qpat_x_assum`env_consistent env cx st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def] >> strip_tac >>
        Cases_on `lookup_scopes id st1.scopes` >> gvs[] >>
        metis_tac[optionTheory.IS_SOME_DEF]) >>
      qspecl_then [`cx`, `ss`, `st1`, `FEMPTY`, `st1.scopes`, `INR y`, `st1'`, `id`, `h`, `t`]
        mp_tac eval_stmts_preserves_tail_lookup_none >>
      simp[]) >>
    qexists_tac `st1` >> simp[] >>
    qspecl_then [`cx`, `ss`, `FEMPTY`, `st1`, `INR y`, `st1'`]
      mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
    simp[] >> disch_then irule >>
    qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
    `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
    pop_assum SUBST1_TAC >>
    irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
    qexists_tac `INR y` >> qexists_tac `ss` >> simp[] >>
    gvs[Abbr`stp`]) >>
  irule env_extends_return_exception_typed >>
  qexists_tac `env_exn` >> simp[]) >>
  metis_tac[]
QED

Resume eval_scc_type_sound_results_mutual[Expr]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Expr e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, type_check_def,
    assert_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `eval_expr cx e st` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `q` >> gvs[no_type_error_result_def]
  >- (
    strip_tac >> Cases_on `x` >>
    gvs[eval_result_typed_def]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[Stmts_nil]:
  rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, Once evaluate_def,
      return_def, no_type_error_result_def]
QED

Resume eval_scc_type_sound_results_mutual[Stmts_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmts (s::ss))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmt s)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_stmts ss` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_stmt s` >> simp[]) >>
  qpat_x_assum `type_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, ignore_bind_apply] >>
  Cases_on `eval_stmt cx s st` >>
  rename1 `eval_stmt cx s st = (r1,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `r1` >> gvs[]
  >- (
    Cases_on `eval_stmts cx ss st1` >>
    rename1 `eval_stmts cx ss st1 = (r2,st2)` >>
    first_x_assum drule_all >> strip_tac >>
    strip_tac >> fs[bind_def] >> gvs[] >>
    Cases_on `r2` >> gvs[no_type_error_result_def]
    >- (
      qexists_tac `env_exn` >> simp[] >>
      irule env_extends_trans >>
      qexists_tac `env''` >> simp[] >>
      irule type_stmt_env_extends >> simp[] >>
      conj_tac >- (irule env_consistent_env_maps_wf >> goal_assum drule >> simp[]) >>
      qexists_tac `ret_ty` >> qexists_tac `s` >> simp[]) >>
    simp[]) >>
  strip_tac >> gvs[] >>
  qexists_tac `env` >> simp[env_extends_refl]
QED

Resume eval_scc_type_sound_results_mutual[For]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (For id typ it n body'))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_iterator it)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_stmts body'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts body')` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_iterator it` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  `env.type_defs = get_tenv cx` by (
    qpat_x_assum `env_consistent env cx st` mp_tac >>
    rewrite_tac[env_consistent_def, env_context_consistent_def] >>
    strip_tac >> simp[]) >>
  `?env_after. type_stmts (extend_local env id typ F) ret_ty body' = SOME env_after` by (
    qpat_x_assum `IS_SOME (type_stmts (extend_local env id typ F) ret_ty body')` mp_tac >>
    rewrite_tac[optionTheory.IS_SOME_EXISTS]) >>
  `well_formed_type env.type_defs typ` by metis_tac[assignable_type_well_formed] >>
  qpat_x_assum `well_formed_type env.type_defs typ` mp_tac >>
  qpat_assum `env.type_defs = get_tenv cx` (fn th => rewrite_tac[th]) >>
  rewrite_tac[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  strip_tac >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME iter_tyv` >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, lift_option_type_def,
       check_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `eval_iterator cx it st` >>
  rename1 `eval_iterator cx it st = (iter_res, st1)` >>
  qpat_x_assum `!tenv s'' tyv t. _`
    (qspecl_then [`get_tenv cx`, `st`, `iter_tyv`, `st`] mp_tac) >>
  impl_tac >- simp[lift_option_type_def, return_def] >>
  disch_then (qspecl_then [`env`, `typ`, `st`, `iter_res`, `st1`] mp_tac) >>
  impl_tac >- metis_tac[] >>
  strip_tac >>
  Cases_on `iter_res`
  >- (
    rename1 `eval_iterator cx it st = (INL vs, st1)` >>
    qpat_x_assum `case INL vs of INL vs => _ | INR v1 => _`
      (mp_tac o SIMP_RULE (srw_ss()) []) >>
    strip_tac >>
    `tyv = iter_tyv` by (
      qpat_x_assum `evaluate_type env.type_defs typ = SOME tyv` mp_tac >>
      qpat_assum `env.type_defs = get_tenv cx` (fn th => rewrite_tac[th]) >>
      qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
      simp[]) >>
    qpat_x_assum `EVERY (value_has_type tyv) vs` mp_tac >>
    qpat_x_assum `tyv = iter_tyv` (fn th => rewrite_tac[th]) >>
    strip_tac >>
    Cases_on `compatible_bound (Dynamic n) (LENGTH vs)`
    >- (
      qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
      qpat_assum `eval_iterator cx it st = (INL vs, st1)` (fn th => rewrite_tac[th]) >>
      rewrite_tac[bind_def, return_def, raise_def, assert_def, check_def, lift_option_type_def] >>
      Cases_on `eval_for cx iter_tyv id body' vs st1` >>
      rename1 `eval_for cx iter_tyv id body' vs st1 = (for_res, st2)` >>
      qpat_x_assum `!tenv s'' tyv t s1 vs' t' s2 x t''. _`
        (qspecl_then [`get_tenv cx`, `st`, `iter_tyv`, `st`, `st`, `vs`, `st1`, `st1`, `()`, `st1`] mp_tac) >>
      impl_tac >- simp[lift_option_type_def, return_def, check_def, assert_def] >>
      disch_then (qspecl_then [`env`, `ret_ty`, `typ`, `env_after`, `st1`, `for_res`, `st2`] mp_tac) >>
      simp[bind_def, ignore_bind_def, return_def, assert_def] >> strip_tac >>
      strip_tac >> gvs[no_type_error_result_def]) >>
    strip_tac >>
    qpat_x_assum `!tenv s'' tyv t s1 vs' t' s2 x t''. _` kall_tac >>
    qpat_x_assum `(let tenv = get_tenv cx in _) st = (res,st')` mp_tac >>
    qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
    qpat_assum `eval_iterator cx it st = (INL vs, st1)` (fn th => rewrite_tac[th]) >>
    simp[LET_THM, bind_def, ignore_bind_def, return_def, assert_def, raise_def,
        check_def, lift_option_type_def, no_type_error_result_def,
        return_exception_typed_def] >> strip_tac >> gvs[]) >>
  strip_tac >>
  qpat_x_assum `!tenv s'' tyv t s1 vs' t' s2 x t''. _` kall_tac >>
  qpat_x_assum `(let tenv = get_tenv cx in _) st = (res,st')` mp_tac >>
  qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
  qpat_assum `eval_iterator cx it st = (INR y, st1)` (fn th => rewrite_tac[th]) >>
  simp[LET_THM, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_type_def] >>
  strip_tac >> gvs[] >>
  conj_tac >- (
    qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
    simp[no_type_error_result_def]) >>
  irule no_control_exc_return_exception_typed >>
  drule eval_iterator_no_control >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[For_nil]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ [] _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >> gvs[no_type_error_result_def]
QED


Resume eval_scc_type_sound_results_mutual[For_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                       push_scope_with_var_def, return_def] >>
  qmatch_goalsub_abbrev_tac `finally loop_body pop_scope stp` >>
  Cases_on `finally loop_body pop_scope stp` >>
  rename1 `finally loop_body pop_scope stp = (loop_res, st_after)` >>
  strip_tac >>
  `stp =
    st with scopes updated_by
      CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))` by
    simp[Abbr`stp`] >>
  qunabbrev_tac `loop_body` >>
  drule for_body_decompose_for_cons_pushed >>
  rewrite_tac[ignore_bind_def] >>
  disch_then drule >>
  strip_tac >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
  `state_well_typed stp` by (
    `value_has_type tyv v` by fs[] >>
    `well_formed_type_value tyv` by (
      qpat_assum `evaluate_type env.type_defs ty = SOME tyv`
        (ACCEPT_TAC o MATCH_MP evaluate_type_well_formed_type_value)) >>
    qpat_x_assum `stp = _` SUBST1_TAC >>
    irule for_cons_pushed_state_well_typed >>
    simp[]) >>
  `accounts_well_typed stp.accounts` by (
    qpat_x_assum `stp = _` SUBST1_TAC >>
    simp[NoAsms, evaluation_state_component_equality] >>
    qpat_assum `accounts_well_typed st.accounts` ACCEPT_TAC) >>
  `env_consistent (extend_local env id ty F) cx stp` by (
    qunabbrev_tac `stp` >>
    metis_tac[push_scope_with_var_env_consistent]) >>
  qpat_x_assum `!s'' x t. push_scope_with_var id tyv v s'' = (INL x,t) ==> _`
    (qspecl_then [`st`, `()`, `stp`] mp_tac) >>
  impl_tac >- simp[push_scope_with_var_def, return_def, Abbr`stp`] >>
  disch_then (qspecl_then [`extend_local env id ty F`, `ret_ty`, `env_after`,
                           `stp`, `res_body`, `st_body`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  Cases_on `res_body` >> simp[NoAsms]
  >- (
    `state_well_typed (st_body with scopes := TL st_body.scopes)` by (
      irule scope_bracket_preserves_swt >> simp[] >>
      qexists_tac `cx` >> qexists_tac `INL x` >>
      qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)` >>
      qexists_tac `body'` >> qexists_tac `st` >> simp[Abbr`stp`]) >>
    `accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts` by
      simp[evaluation_state_component_equality] >>
    `env_consistent env cx (st_body with scopes := TL st_body.scopes)` by (
      `env_consistent env_after cx st_body` by (
        qpat_x_assum `case (INL x : unit + vyperState$exception) of INL u => _ | INR exn => _` mp_tac >>
        simp[NoAsms]) >>
      qpat_x_assum `stp = _` SUBST_ALL_TAC >>
      metis_tac[for_body_env_consistent_after_pop, env_consistent_env_maps_wf]) >>
    qpat_x_assum `!s'' x' t s''' broke t'. _`
      (qspecl_then [`st`, `()`, `stp`, `stp`, `F`,
                    `st_body with scopes := TL st_body.scopes`] mp_tac) >>
    impl_tac >- (
      conj_tac >- simp[push_scope_with_var_def, return_def, Abbr`stp`] >>
      conj_tac >- (
        `loop_res = INL F` by (
          qpat_x_assum `(∃x'. INL x = INL x') ==> _` irule >>
          simp[]) >>
        qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
        qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
        qpat_x_assum `stp = _` SUBST_ALL_TAC >>
        qpat_x_assum `finally _ _ _ = (INL F, _)` mp_tac >>
        strip_tac >>
        pop_assum mp_tac >>
        simp[NoAsms, bind_def, ignore_bind_def]) >>
      simp[]) >>
    `loop_res = INL F` by (
      qpat_x_assum `(∃x'. INL x = INL x') ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    `eval_for cx tyv id body' vs (st_body with scopes := TL st_body.scopes) = (res,st')` by (
      qpat_x_assum `(case (INL F,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
      simp[return_def]) >>
    disch_then (qspecl_then [`env`, `ret_ty`, `ty`, `env_after`,
                             `st_body with scopes := TL st_body.scopes`, `res`, `st'`] mp_tac) >>
    (impl_tac >- fs[]) >>
    simp[]) >>
  `state_well_typed (st_body with scopes := TL st_body.scopes)` by (
    irule scope_bracket_preserves_swt >> simp[] >>
    qexists_tac `cx` >> qexists_tac `INR y` >>
    qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)` >>
    qexists_tac `body'` >> qexists_tac `st` >> simp[Abbr`stp`]) >>
  `accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts` by
    simp[evaluation_state_component_equality] >>
  SUBGOAL_THEN ``env_consistent env cx (st_body with scopes := TL st_body.scopes)`` assume_tac >- (
    irule for_cons_popped_env_consistent_from_stmt_case >>
    qexists_tac `body'` >> qexists_tac `y` >> qexists_tac `id` >>
    qexists_tac `\u. env_consistent env_after cx st_body` >>
    qexists_tac `ret_ty` >> qexists_tac `st` >> qexists_tac `ty` >>
    qexists_tac `tyv` >> qexists_tac `v` >>
    conj_tac >- simp[] >>
    conj_tac >- simp[Abbr`stp`] >>
    conj_tac >- simp[] >>
    asm_rewrite_tac[]) >>
  Cases_on `y = ContinueException`
  >- (
    qpat_x_assum `y = ContinueException` SUBST_ALL_TAC >>
    qpat_x_assum `!s'' x t s'³' broke t'. _`
      (qspecl_then [`st`, `()`, `stp`, `stp`, `F`,
                    `st_body with scopes := TL st_body.scopes`] mp_tac) >>
    impl_tac >- (
      conj_tac >- simp[push_scope_with_var_def, return_def, Abbr`stp`] >>
      conj_tac >- (
        `loop_res = INL F` by (
          qpat_x_assum `INR ContinueException = INR ContinueException ==> _` irule >>
          simp[]) >>
        qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
        qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
        qpat_x_assum `stp = _` SUBST_ALL_TAC >>
        qpat_x_assum `finally _ pop_scope _ = (INL F, _)` mp_tac >>
        strip_tac >>
        pop_assum mp_tac >>
        simp[NoAsms, bind_def, ignore_bind_def]) >>
      simp[]) >>
    `loop_res = INL F` by (
      qpat_x_assum `INR ContinueException = INR ContinueException ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    `eval_for cx tyv id body' vs (st_body with scopes := TL st_body.scopes) = (res,st')` by (
      qpat_x_assum `(case (INL F,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
      simp[return_def]) >>
    disch_then (qspecl_then [`env`, `ret_ty`, `ty`, `env_after`,
                             `st_body with scopes := TL st_body.scopes`, `res`, `st'`] mp_tac) >>
    (impl_tac >- fs[]) >>
    simp[]) >>
  Cases_on `y = BreakException`
  >- (
    qpat_x_assum `y = BreakException` SUBST_ALL_TAC >>
    `loop_res = INL T` by (
      qpat_x_assum `INR BreakException = INR BreakException ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL T` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    qpat_x_assum `(case (INL T,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
    simp[NoAsms, return_def] >>
    strip_tac >>
    qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >>
    simp[no_type_error_result_def]) >>
  `loop_res = INR y` by (
    qpat_x_assum `!e. INR y = INR e /\ e <> ContinueException /\ e <> BreakException ==> _`
      (qspec_then `y` irule) >>
    simp[]) >>
  qpat_x_assum `loop_res = INR y` SUBST_ALL_TAC >>
  qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
  qpat_x_assum `(case (INR y,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
  simp[NoAsms] >>
  strip_tac >>
  qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `INR y = res` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `!s'' x t s'³' broke t'. _` kall_tac >>
  qmatch_goalsub_abbrev_tac `state_well_typed stfinal` >>
  qunabbrev_tac `stfinal` >>
  irule for_cons_non_loop_exception_suffix_projected >>
  simp[] >>
  conj_tac >- (
    simp[no_type_error_result_def] >> strip_tac >>
    qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
    simp[no_type_error_result_def] >>
    disch_then (qspec_then `msg` mp_tac) >> simp[]) >>
  fs[] >>
  qexists_tac `id` >> qexists_tac `ty` >>
  qexists_tac `env_exn` >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[Iterator_Array]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_iterator (Array e))` mp_tac >>
  pure_rewrite_tac[int_calls_iterator_def] >> strip_tac >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    rename1 `eval_expr cx e st = (INL tvl, st1)` >>
    qpat_x_assum `!env' st' res st''. _ ==> case res of INL pv => live_memory_result st'' pv | INR _ => T`
      (qspecl_then [`env`,`st`,`INL tvl`,`st1`] mp_tac) >>
    simp[] >> strip_tac >>
    qpat_x_assum `!env' st' res st''. _ ==> typed_scope_transition st' st''` kall_tac >>
    Cases_on `read_result cx tvl st1` >>
    rename1 `read_result cx tvl st1 = (mat_res, st2)` >>
    drule_all live_result_read_typed >> strip_tac >>
    Cases_on `mat_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `read_result cx tvl st1 = (INL v, st2)` >>
      drule read_result_state >> strip_tac >> gvs[] >>
      gvs[value_runtime_typed_def] >>
      `env.type_defs = get_tenv cx` by gvs[env_consistent_def, env_context_consistent_def] >>
      gvs[] >>
      drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
      Cases_on `lift_option_type (extract_elements (ArrayTV elem_tv bd) v) "For not ArrayV" st2` >>
      rename1 `lift_option_type _ _ st2 = (lift_res, st3)` >>
      drule lift_option_type_state >> strip_tac >> gvs[] >>
      Cases_on `lift_res` >> gvs[return_def, no_type_error_result_def]
      >- (
        rename1 `lift_option_type (extract_elements (ArrayTV elem_tv bd) v) _ st2 = (INL vs, st2)` >>
        strip_tac >> gvs[lift_option_type_def] >>
        Cases_on `extract_elements (ArrayTV elem_tv bd) v` >>
        gvs[raise_def, return_def] >>
        Cases_on `v` >> gvs[extract_elements_def] >>
        rename1 `ArrayV av` >>
        irule extract_elements_well_typed >>
        qexists_tac `av` >> qexists_tac `bd` >> simp[] >>
        conj_tac >- metis_tac[evaluate_type_well_formed_type_value] >>
        simp[extract_elements_def]) >>
      Cases_on `extract_elements (ArrayTV elem_tv bd) v` >>
      gvs[lift_option_type_def, raise_def, return_def] >>
      Cases_on `v` >> gvs[extract_elements_def, value_has_type_def]) >>
    strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Iterator_Range]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_iterator (Range e e'))` mp_tac >>
  pure_rewrite_tac[int_calls_iterator_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr1_res, st1)` >>
  last_x_assum drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  Cases_on `expr1_res`
  >- (
    qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
    rename1 `eval_expr cx e st = (INL tv1, st1)` >>
    qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result st' pv | INR _ => T`
      (qspecl_then [`env`,`st`,`INL tv1`,`st1`] mp_tac) >>
    (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
    qpat_x_assum `!env st res st'. _ ==> typed_scope_transition st st'` kall_tac >>
    qpat_x_assum `case INL tv1 of INL pv => eval_result_typed _ pv _ | INR _ => T` mp_tac >>
    pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
    Cases_on `read_result cx tv1 st1` >>
    rename1 `read_result cx tv1 st1 = (val1_res, st2)` >>
    drule_all live_result_read_typed >> strip_tac >>
    Cases_on `val1_res`
    >- (
      rename1 `read_result cx tv1 st1 = (INL v1, st2)` >>
      drule read_result_state >> strip_tac >>
      qpat_x_assum `st2 = st1` SUBST_ALL_TAC >>
      qpat_x_assum `!s'' tv1 t s''' s t'. _`
        (qspecl_then [`st`, `tv1`, `st1`, `st1`, `v1`, `st1`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `eval_expr cx e' st1` >>
      rename1 `eval_expr cx e' st1 = (expr2_res, st3)` >>
      qpat_x_assum `!env' st' res st''. _ ==> case res of INL pv => live_memory_result st'' pv | INR _ => T`
        (qspecl_then [`env`, `st1`, `expr2_res`, `st3`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `!env' st' res st''. _ ==> typed_scope_transition st' st''` kall_tac >>
      qpat_x_assum `!env' st' res st''. _ ==> (_ /\ _)`
        (qspecl_then [`env`, `st1`, `expr2_res`, `st3`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `well_typed_expr env e' ==> _` mp_tac >>
      impl_tac >- simp[] >> strip_tac >>
      Cases_on `expr2_res`
      >- (
        qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
        rename1 `eval_expr cx e' st1 = (INL tv2, st3)` >>
        Cases_on `read_result cx tv2 st3` >>
        rename1 `read_result cx tv2 st3 = (val2_res, st4)` >>
        drule_at (Pat `read_result`) live_result_read_typed >>
        disch_then (qspecl_then [`ty`,`env`] mp_tac) >>
        (impl_tac >- gvs[]) >> strip_tac >>
        Cases_on `val2_res`
        >- (
          qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
          rename1 `read_result cx tv2 st3 = (INL v2, st4)` >>
          drule read_result_state >> strip_tac >>
          qpat_x_assum `st4 = st3` SUBST_ALL_TAC >>
          gvs[value_runtime_typed_def] >>
          `?i1. v1 = IntV i1` by metis_tac[int_typed_value_is_IntV] >>
          `?i2. v2 = IntV i2` by metis_tac[int_typed_value_is_IntV] >>
          gvs[] >>
          Cases_on `lift_sum (get_range_limits (IntV i1) (IntV i2)) st3` >>
          rename1 `lift_sum (get_range_limits (IntV i1) (IntV i2)) st3 = (range_res, st5)` >>
          strip_tac >>
          qspecl_then [`env.type_defs`, `expr_type e`, `tv`, `i1`, `i2`,
                       `range_res`, `st3`, `st5`, `res`, `st'`]
            mp_tac iterator_range_tail_eval_sound >>
          impl_tac >- (
            simp[] >>
            qpat_x_assum `case (range_res,st5) of _ => _ | _ => _` mp_tac >>
            Cases_on `range_res` >> simp[return_def, raise_def]) >>
          strip_tac >> gvs[]) >>
        strip_tac >> gvs[no_type_error_result_def]) >>
      strip_tac >> gvs[return_def, no_type_error_result_def] >> metis_tac[]) >>
    qpat_x_assum `!s'' tv1 t s''' s t'. _` kall_tac >>
    strip_tac >> gvs[no_type_error_result_def]) >>
  strip_tac >>
  drule_all iterator_range_expr_error_eq >> strip_tac >>
  qpat_x_assum `res = INR y` SUBST_ALL_TAC >>
  qpat_x_assum `st' = st1` SUBST_ALL_TAC >>
  qpat_x_assum `!s'' tv1 t s''' s t'. _` kall_tac >>
  qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
  simp[no_type_error_result_def]
QED

(* Legacy wrappers have their own, disconnected structural induction. *)


Resume eval_scc_type_sound_results_mutual[BasePlaceRoot_NameTarget]:
  rpt gen_tac >> strip_tac >>
  `?ty. vt = Type ty` by
    gvs[type_place_target_NameTarget, AllCaseEqs()] >>
  gvs[] >>
  drule_all NameTarget_sound >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, assert_def, ignore_bind_def,
    get_scopes_def, type_check_def, lift_option_type_def, lift_option_def] >>
  strip_tac >> gvs[] >>
  simp[no_type_error_result_def, runtime_place_typed_memory, subscripts_type_def] >>
  gvs[type_place_target_NameTarget, AllCaseEqs(),
      env_consistent_def, env_scopes_consistent_def, env_context_consistent_def] >>
  `EVERY scope_well_typed st.scopes` by gvs[state_well_typed_def] >>
  drule_all lookup_scopes_well_typed_type >> strip_tac >>
  metis_tac[]
QED

Theorem is_immutable_decl_MEM_Immutable_exists[local]:
  !n ts. is_immutable_decl n ts ==>
  ?vis id ty init. MEM (VariableDecl vis Immutable id ty init) ts /\ id = n
Proof
  Induct_on `ts` >> rw[is_immutable_decl_def] >>
  Cases_on `h` >> gvs[is_immutable_decl_def] >>
  Cases_on `v0` >> gvs[is_immutable_decl_def] >>
  metis_tac[]
QED

Resume eval_scc_type_sound_results_mutual[BasePlaceRoot_TopLevelNameTarget]:
  rpt gen_tac >> strip_tac >>
  drule eval_base_place_TopLevelNameTarget_preserves_state >> strip_tac >> gvs[] >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  pure_rewrite_tac[Once evaluate_def] >> strip_tac >>
  drule_all lookup_global_target_no_type_error >> strip_tac >>
  simp[] >> Cases_on `res` >> simp[] >>
  drule_all lookup_global_target_success_typed >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[BasePlaceRoot_SubscriptTarget]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_base_place cx (SubscriptTarget t e) st = (res,st')` >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_target (SubscriptTarget t e))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_target t)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_target t` >> simp[]) >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
  rewrite_tac[type_place_target_SubscriptTarget] >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx t st` >>
  rename1 `eval_base_place cx t st = (bt_res, st1)` >>
  qpat_assum `!env vt st res st'. _ ==> state_well_typed st' /\ _`
    drule_all >> strip_tac >>
  Cases_on `bt_res`
  >- (rename1 `eval_base_place cx t st = (INL pv,st1)` >>
      qpat_x_assum `!s'' pv t'. eval_base_place _ _ _ = _ ==> _` drule >> strip_tac >>
      qpat_x_assum `!env vt st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
        drule_all >> pure_rewrite_tac[sumTheory.sum_case_def] >> strip_tac >>
      qpat_x_assum `!env vt st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
      qpat_x_assum `!env vt st res st'. _ ==> case res of INL pv => writable_place_result _ _ _ | INR _ => T` kall_tac >>
      qpat_x_assum `!env vt st res st'. _ ==> state_well_typed _ /\ _` kall_tac >>
      simp_tac (srw_ss()) [] >>
      Cases_on `eval_expr cx e st1` >>
      rename1 `eval_expr cx e st1 = (er,st2)` >>
      qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
        (qspecl_then [`env`,`st1`,`er`,`st2`] mp_tac) >>
      (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
      qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
        (qspecl_then [`env`,`st1`,`er`,`st2`] mp_tac) >>
      (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
      qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
      qpat_x_assum `well_typed_expr env e ==> _` drule >>
      simp[] >> strip_tac >>
      Cases_on `er` >> gvs[no_type_error_result_def]
      >- (rename1 `read_result cx idx st2` >>
          Cases_on `read_result cx idx st2` >>
          rename1 `read_result cx idx st2 = (rr,st3)` >>
          drule_all live_result_read_typed >> strip_tac >> gvs[] >>
          Cases_on `rr` >> gvs[no_type_error_result_def]
          >- (rename1 `read_result cx idx st2 = (INL v,st2)` >>
              `vyperImmutableMetadataFrame$immutable_metadata_frame st1 st2` by
                (drule eval_expr_immutable_metadata_frame >> simp[]) >>
              `eval_result_typed (env,cx,st2) pv vt'` by
                (irule eval_result_typed_transport >> goal_assum drule_all) >>
              `live_memory_result st2 pv` by
                (Cases_on `pv`
                 >- simp[live_memory_result_def]
                 >- (rename1 `PlaceR p` >> Cases_on `p`
                     >- simp[live_memory_result_def]
                     >- (irule live_memory_result_transport >> goal_assum drule_all)
                     >> simp[live_memory_result_def])
                 >> simp[live_memory_result_def]) >>
              `well_formed_vtype env.type_defs vt'` by
                metis_tac[type_place_target_well_formed_vtype_stmt] >>
              `case pv of Value _ => F | _ => T` by
                (drule eval_base_place_result_shape >> strip_tac >> gvs[]) >>
              `expr_result_typed env e (Value v)` by
                gvs[expr_result_typed_def, expr_runtime_typed_def, value_runtime_typed_def,
                    value_result_typed_def] >>
              strip_tac >>
              drule vyperPlaceFramesTheory.extend_place_state >> strip_tac >> gvs[] >>
              drule_all extend_target_subscript_place_sound >>
              simp[no_type_error_result_def]) >>
          strip_tac >> gvs[]) >>
      strip_tac >> gvs[]) >>
  qpat_x_assum `!s'' pv t'. eval_base_place _ _ _ = _ ==> _` kall_tac >>
  gvs[no_type_error_result_def] >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[BasePlaceRoot_AttributeTarget]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_base_place cx (AttributeTarget bt id) st = (res,st')` >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_target (AttributeTarget bt id))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `type_place_target _ (AttributeTarget _ _) = _` mp_tac >>
  rewrite_tac[type_place_target_AttributeTarget] >> strip_tac >> gvs[] >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt st` >>
  rename1 `eval_base_place cx bt st = (br,st1)` >>
  qpat_x_assum `!env vt st res st'. _ ==> state_well_typed _ /\ _`
    drule_all >> strip_tac >>
  Cases_on `br`
  >- (rename1 `eval_base_place cx bt st = (INL pv,st1)` >>
      qpat_x_assum `!env vt st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
        drule_all >> pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
      qpat_x_assum `!env vt st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
      qpat_x_assum `!env vt st res st'. _ ==> case res of INL pv => writable_place_result _ _ _ | INR _ => T` kall_tac >>
      simp[] >> strip_tac >>
      drule vyperPlaceFramesTheory.extend_place_state >> strip_tac >> gvs[] >>
      drule eval_base_place_result_shape >> strip_tac >> gvs[eval_result_typed_def] >>
      drule_all attribute_type_runtime_step >> strip_tac >>
      drule_all extend_live_place_attribute_no_type_error >> strip_tac >>
      simp[] >> Cases_on `res` >> simp[] >>
      drule extend_place_place_success_shape >> strip_tac >> gvs[] >>
      drule_all extend_place_typed >> simp[]) >>
  strip_tac >> gvs[no_type_error_result_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Name]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >>
      drule_all well_typed_Name_lookup >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, type_check_def, assert_def, ignore_bind_def,
           bind_def, get_scopes_def, return_def] >>
      strip_tac >> gvs[] >>
      simp[no_type_error_result_def, eval_result_typed_def, expr_type_def,
           runtime_place_typed_memory, subscripts_type_def] >>
      `EVERY scope_well_typed st.scopes` by gvs[state_well_typed_def] >>
      drule_all lookup_scopes_well_typed_type >> strip_tac >>
      metis_tac[]) >>
  rpt strip_tac >> gvs[well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_TopLevelName]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  imp_res_tac lookup_global_state >> gvs[] >>
  conj_tac
  >- (strip_tac >> simp[expr_type_def] >>
      metis_tac[lookup_global_TopLevelName_sound]) >>
  rpt strip_tac >> metis_tac[lookup_global_TopLevelName_place_sound]
QED

Resume eval_scc_type_sound_results_mutual[Expr_FlagMember]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >> gvs[] >> conj_tac
  >- (disch_tac >>
      drule_all flag_member_sound >> strip_tac >>
      imp_res_tac lookup_flag_mem_state >> gvs[] >>
      PairCases_on `nsid` >>
      gvs[env_consistent_def, env_context_consistent_def] >>
      qpat_x_assum `!src fid ls. FLOOKUP env.flag_members (src,fid) = SOME ls ==> _`
        (drule_then strip_assume_tac) >>
      `LENGTH members <= 256` by (
        qpat_x_assum `well_typed_expr env (FlagMember _ _ _)` mp_tac >>
        gvs[well_typed_expr_def, well_formed_type_def, evaluate_type_def] >>
        decide_tac) >>
      qpat_x_assum `lookup_flag_mem _ _ _ _ = _` mp_tac >>
      simp[lookup_flag_mem_def, return_def, raise_def] >>
      Cases_on `INDEX_OF mid members` >> strip_tac >>
      gvs[return_def, no_type_error_result_def, expr_result_typed_def,
          expr_runtime_typed_def, expr_type_def, value_result_typed_Value,
          evaluate_type_def, value_has_type_def, INDEX_OF_eq_NONE,
          INDEX_OF_eq_SOME] >>
      irule bitTheory.TWOEXP_MONO >> simp[]) >>
  rpt strip_tac >> gvs[well_typed_expr_def]
QED


(* ===== If-expression helpers and Resume block ===== *)


Theorem type_place_expr_IfExp_NONE[local]:
  !env ty cond e_true e_false.
    type_place_expr env (IfExp ty cond e_true e_false) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_IfExp]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (IfExp ty e e' e''))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e'')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  reverse conj_tac >- (
    rpt strip_tac >>
    qpat_x_assum `type_place_expr _ (IfExp _ _ _ _) = SOME _` mp_tac >>
    simp[type_place_expr_IfExp_NONE]) >>
  disch_then mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  rename1 `expr_type e' = ty` >>
  qpat_x_assum `!s0 pv t. eval_expr cx e s0 = (INL pv,t) ==> _`
    (mk_asm "true_branch") >>
  qpat_x_assum `!s0 pv t. eval_expr cx e s0 = (INL pv,t) ==> _`
    (mk_asm "false_branch") >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (cr,st1)` >>
  qpat_x_assum `!env st res st'. env_consistent _ _ _ /\ _ ==> _`
    (qspecl_then [`env`,`st`,`cr`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  (impl_tac >- simp[]) >> strip_tac >>
  reverse (Cases_on `cr`)
  >- (asm_x "true_branch" kall_tac >> asm_x "false_branch" kall_tac >>
      qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def] >> strip_tac >> gvs[]) >>
  rename1 `eval_expr cx e st = (INL cp,st1)` >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
    (qspecl_then [`env`,`st`,`INL cp`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> simp_tac bool_ss [] >> disch_tac >>
  asm_x "true_branch" mp_tac >>
  disch_then (qspecl_then [`st`,`cp`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  asm_x "false_branch" mp_tac >>
  disch_then (qspecl_then [`st`,`cp`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `switch_BoolV cx cp (eval_expr cx e') (eval_expr cx e'') st1` >>
  rename1 `switch_BoolV _ _ _ _ _ = (br,st2)` >>
  `state_well_typed st2 /\ env_consistent env cx st2 /\
   accounts_well_typed st2.accounts /\ no_type_error_result br /\
   (case br of INL pv => eval_result_typed (env,cx,st2) pv (Type ty) /\
                        live_memory_result st2 pv | INR _ => T)` by
    (qho_match_abbrev_tac `P br st2` >>
     irule switch_BoolV_live_post >>
     goal_assum $ drule_at (Pat `switch_BoolV`) >>
     qexists `env` >> simp[expr_type_def] >> conj_tac
     >- (rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
         simp[Abbr `P`, no_type_error_result_def]) >>
     conj_tac
     >- (rpt gen_tac >> disch_tac >>
         qpat_x_assum `!env st res st'. env_consistent _ _ _ /\ _ ==> (well_typed_expr env e'' ==> _) /\ _`
           (qspecl_then [`env`,`st1`,`r`,`s`] mp_tac) >>
         (impl_tac >- simp[]) >> strip_tac >>
         qpat_x_assum `well_typed_expr env e'' ==> _` mp_tac >>
         (impl_tac >- simp[]) >> strip_tac >>
         qpat_x_assum `!env st res st'. (well_typed_expr env e'' \/ _) /\ _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
           (qspecl_then [`env`,`st1`,`r`,`s`] mp_tac) >>
         (impl_tac >- simp[]) >>
         rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
         Cases_on `r` >> gvs[Abbr `P`]) >>
     conj_tac
     >- (rpt gen_tac >> disch_tac >>
         qpat_x_assum `!env st res st'. env_consistent _ _ _ /\ _ ==> (well_typed_expr env e' ==> _) /\ _`
           (qspecl_then [`env`,`st1`,`r`,`s`] mp_tac) >>
         (impl_tac >- simp[]) >> strip_tac >>
         qpat_x_assum `well_typed_expr env e' ==> _` mp_tac >>
         (impl_tac >- simp[]) >> strip_tac >>
         qpat_x_assum `!env st res st'. (well_typed_expr env e' \/ _) /\ _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
           (qspecl_then [`env`,`st1`,`r`,`s`] mp_tac) >>
         (impl_tac >- simp[]) >>
         rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
         Cases_on `r` >> gvs[Abbr `P`]) >>
     rpt (qpat_x_assum `!env st res st'. _` kall_tac) >> gvs[]) >>
  rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
  qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `br` >> simp[] >> strip_tac >>
  gvs[] >>
  drule_all conditional_result_live_typed >> strip_tac >>
  Cases_on `res` >> gvs[expr_type_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Literal]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >>
  gvs[no_type_error_result_def, well_typed_expr_def, well_formed_type_def,
      expr_type_def, optionTheory.IS_SOME_EXISTS] >>
  rw[expr_result_typed_def, expr_runtime_typed_def, expr_type_def] >>
  drule_all literal_value_result_typed >> simp[value_result_typed_def] >>
  metis_tac[]
QED


(* ===== Struct literal helpers and Resume block ===== *)

Theorem well_typed_named_exprs_MAP_SND_stmt:
  !env kes. well_typed_named_exprs env kes ==> well_typed_exprs env (MAP SND kes)
Proof
  gen_tac >> Induct >> simp[well_typed_expr_def] >>
  Cases >> simp[well_typed_expr_def]
QED

Theorem struct_has_type_zip_same_names_stmt[local]:
  !names tvs vs.
    LENGTH names = LENGTH tvs /\ LENGTH tvs = LENGTH vs /\
    LIST_REL value_has_type tvs vs ==>
    struct_has_type (ZIP (names,tvs)) (ZIP (names,vs))
Proof
  Induct >> simp[Once value_has_type_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `tvs` >> Cases_on `vs` >> gvs[Once value_has_type_def]
QED


Theorem OPT_MMAP_from_LIST_REL_evaluate_type_stmt[local]:
  !tys tvs tenv.
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
    OPT_MMAP (evaluate_type tenv) tys = SOME tvs
Proof
  Induct >> Cases_on `tvs` >> simp[OPT_MMAP_def]
QED

Theorem OPT_MMAP_evaluate_type_mono_stmt[local]:
  !types tenv nid tvs.
    OPT_MMAP (evaluate_type (tenv \\ nid)) types = SOME tvs ==>
    OPT_MMAP (evaluate_type tenv) types = SOME tvs
Proof
  Induct >> simp[OPT_MMAP_def] >>
  rpt gen_tac >>
  Cases_on `evaluate_type (tenv \\ nid) h` >> simp[] >>
  Cases_on `OPT_MMAP (evaluate_type (tenv \\ nid)) types` >> simp[] >>
  strip_tac >> gvs[] >>
  imp_res_tac evaluate_type_mono >> simp[] >>
  first_x_assum (qspecl_then [`tenv`, `nid`] mp_tac) >> simp[]
QED
Theorem struct_lit_expr_result_typed[local]:
  well_formed_type env.type_defs (StructT nsid) /\
  FLOOKUP env.type_defs (nsid) = SOME (StructArgs args) /\
  MAP FST kes = MAP FST args /\
  MAP (expr_type o SND) kes = MAP SND args /\
  exprs_runtime_typed env (MAP SND kes) vs ==>
  eval_result_typed (env,cx,st)
    (Value (StructV (ZIP (MAP FST args,vs)))) (Type (StructT nsid))
Proof
  rw[exprs_runtime_typed_def, eval_result_typed_def] >>
  qexists_tac `StructTV (ZIP (MAP FST args,tvs))` >>
  gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  qpat_x_assum `evaluate_type _ (StructT _) = SOME _` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  strip_tac >> gvs[value_has_type_def] >>
  qpat_x_assum `MAP (expr_type o SND) kes = MAP SND args` (assume_tac o GSYM) >>
  gvs[] >>
  `OPT_MMAP (evaluate_type env.type_defs) (MAP (expr_type o SND) kes) = SOME tvs` by
    (irule OPT_MMAP_from_LIST_REL_evaluate_type_stmt >>
     gvs[LIST_REL_EL_EQN, EL_MAP]) >>
  `OPT_MMAP (evaluate_type env.type_defs) (MAP (expr_type o SND) kes) = SOME tvs'` by
    metis_tac[OPT_MMAP_evaluate_type_mono_stmt] >>
  gvs[] >>
  irule struct_has_type_zip_same_names_stmt >>
  imp_res_tac LIST_REL_LENGTH >> gvs[LENGTH_MAP] >>
  metis_tac[LENGTH_MAP]
QED

Theorem type_place_expr_StructLit_NONE_stmt[local]:
  !env ty sid kes.
    type_place_expr env (StructLit ty sid kes) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_StructLit]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (StructLit ty callee kes))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def, GSYM int_calls_exprs_MAP_SND] >> strip_tac >>
  reverse conj_tac >- (
    rpt strip_tac >>
    qpat_x_assum `type_place_expr _ (StructLit _ _ _) = SOME _` mp_tac >>
    simp[type_place_expr_StructLit_NONE_stmt]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr _ (StructLit _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx (MAP SND kes) st` >>
  rename1 `eval_exprs cx (MAP SND kes) st = (exprs_res,st1)` >>
  qpat_x_assum `!ks. ks = MAP FST kes ==> _` (qspec_then `MAP FST kes` mp_tac) >>
  simp_tac bool_ss [] >>
  `well_typed_exprs env (MAP SND kes)` by
    (irule well_typed_named_exprs_MAP_SND_stmt >> first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then drule_all >> strip_tac >>
  Cases_on `exprs_res` >> simp_tac(srw_ss())[]
  >- (
    strip_tac >>
    qpat_x_assum `(let ks = MAP FST kes in do vs <- eval_exprs cx (MAP SND kes); return (Value (StructV (ZIP (ks,vs)))) od) st = (res,st')` mp_tac >>
    asm_simp_tac(srw_ss())[bind_def, return_def, LET_THM] >>
    strip_tac >> gvs[no_type_error_result_def] >>
    simp[expr_type_def] >>
    irule (SRULE [eval_result_typed_def] struct_lit_expr_result_typed) >>
    asm_rewrite_tac[] >> qexists `kes` >> asm_rewrite_tac[])
  >- (
    strip_tac >>
    qpat_x_assum `eval_exprs cx (MAP SND kes) st = (INR y,st1)` (fn ev_th =>
      qpat_x_assum `(let ks = MAP FST kes in do vs <- eval_exprs cx (MAP SND kes); return (Value (StructV (ZIP (ks,vs)))) od) st = (res,st')` mp_tac >>
      asm_simp_tac(srw_ss())[Once bind_def, return_def, LET_THM, ev_th]) >>
    strip_tac >>
    gvs[] >>
    qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
    simp[no_type_error_result_def])
QED


(* ===== Subscript expression helpers and Resume block ===== *)

Theorem select_ordinary_subscript_sound[local]:
  !env cx st base ct ie rt idx res st'.
  env_consistent env cx st /\ state_well_typed st /\
  eval_result_typed (env,cx,st) base (Type ct) /\ live_memory_result st base /\
  subscript_type_ok ct ie rt /\ subscript_index_matches ct ie idx /\
  value_runtime_typed env (expr_type ie) idx /\
  select_result cx ct base (ValueSubscript idx) st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  (case res of INL pv => eval_result_typed (env,cx,st') pv (Type rt) | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  Cases_on `ct` >>
  gvs[subscript_type_ok_def, subscript_index_matches_def, AllCaseEqs()]
  >- (gvs[eval_result_typed_def] >>
      drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
      `LENGTH tvs = LENGTH l` by metis_tac[LIST_REL_LENGTH] >>
      `evaluate_type (get_tenv cx) (EL (Num n) l) = SOME (EL (Num n) tvs)` by
        gvs[LIST_REL_EL_EQN] >>
      `well_formed_type_value (TupleTV tvs)` by
        metis_tac[evaluate_type_well_formed_type_value] >>
      `subscript_type (TupleTV tvs) (ValueSubscript (IntV n)) = SOME (EL (Num n) tvs)` by
        simp[subscript_type_def, oEL_THM] >>
      `subscripts_type (TupleTV tvs) [ValueSubscript (IntV n)] = SOME (EL (Num n) tvs)` by
        simp[subscripts_type_def] >>
      Cases_on `base'` >> gvs[select_result_def]
       >- (rename1 `value_has_type (TupleTV tvs) vv` >>
           Cases_on `evaluate_subscripts (TupleTV tvs) vv [ValueSubscript (IntV n)]` >>
           gvs[bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def] >>
           simp[no_type_error_result_def]
           >- (drule_all vyperPlaceStatePreservationTheory.evaluate_subscripts_type >> simp[]) >>
           metis_tac[evaluate_subscripts_typed_error]) >>
       rename1 `runtime_place_typed cx st p (TupleTV tvs)` >>
       drule_all extend_live_tuple_place_sound >> strip_tac >>
       `st' = st` by metis_tac[vyperPlaceFramesTheory.extend_place_state, SND] >>
       Cases_on `res` >> gvs[]) >>
  qpat_x_assum `value_runtime_typed _ _ _` mp_tac >>
  simp[value_runtime_typed_def] >> strip_tac >>
  drule_all int_typed_value_is_IntV >> strip_tac >> gvs[] >>
  gvs[eval_result_typed_def] >>
  drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
  `well_formed_type_value (ArrayTV elem_tv b)` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  Cases_on `base'` >> gvs[select_result_def]
  >- (rename1 `value_has_type (ArrayTV elem_tv b) vv` >>
      Cases_on `evaluate_subscripts (ArrayTV elem_tv b) vv [ValueSubscript (IntV i)]` >>
      gvs[bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def] >>
      drule_all array_subscript_place_check >> simp[no_type_error_result_def] >>
      strip_tac >>
      `subscripts_type (ArrayTV elem_tv b) [ValueSubscript (IntV i)] = SOME elem_tv` by
        simp[subscripts_type_def] >>
      drule_all vyperPlaceStatePreservationTheory.evaluate_subscripts_type >> simp[]) >>
  drule_all extend_live_array_place_sound >> strip_tac >>
  `st' = st` by metis_tac[vyperPlaceFramesTheory.extend_place_state, SND] >>
  Cases_on `res` >> gvs[]
QED

Theorem select_projection_subscript_sound[local]:
  !env cx st bp bvt ct ie out idx res st'.
  env_consistent env cx st /\ state_well_typed st /\
  eval_result_typed (env,cx,st) bp bvt /\ live_memory_result st bp /\
  well_formed_vtype env.type_defs bvt /\ vtype_annotation_ok bvt ct /\
  subscript_vtype bvt (expr_type ie) = SOME out /\
  value_runtime_typed env (expr_type ie) idx /\
  select_result cx ct bp (ValueSubscript idx) st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  (case res of INL pv => eval_result_typed (env,cx,st') pv out | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `bvt`
  >- (rename1 `Type input_ty` >> Cases_on `input_ty` >>
      gvs[subscript_vtype_def, vtype_annotation_ok_def] >>
      irule select_ordinary_subscript_sound >> simp[] >>
      goal_assum (drule_at (Pat `select_result`)) >>
      qexists `ie` >> simp[subscript_type_ok_def, subscript_index_matches_def]) >>
  gvs[eval_result_typed_def] >>
  gvs[select_result_def, vtype_annotation_ok_def] >>
  `st' = st` by metis_tac[vyperPlaceFramesTheory.extend_place_state, SND] >>
  drule_all extend_target_hashmap_place_sound >>
  simp[eval_result_typed_def]
QED

Theorem values_have_types_LIST_REL_stmt[local]:
  !tys tvs. values_have_types tys tvs = LIST_REL value_has_type tys tvs
Proof
  Induct >> rw[value_has_type_def] >>
  Cases_on `tvs` >> gvs[value_has_type_def]
QED

Theorem value_has_type_TupleTV_dest_stmt[local]:
  !tvs v. value_has_type (TupleTV tvs) v ==>
          ?vs. v = ArrayV (TupleV vs) /\ values_have_types tvs vs
Proof
  Cases_on `v` >> gvs[value_has_type_inv] >>
  Cases_on `a` >> gvs[value_has_type_inv]
QED


Theorem type_place_expr_well_formed_vtype_stmt[local]:
  !env cx st e vt.
    env_consistent env cx st /\ type_place_expr env e = SOME vt ==>
    well_formed_vtype env.type_defs vt
Proof
  measureInduct_on `expr_size e` >>
  rpt strip_tac >>
  Cases_on `e` >>
  gvs[Once well_typed_expr_def, AllCaseEqs()]
  >- (PairCases_on `p` >>
      qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
      simp[well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
      gvs[env_consistent_def, env_context_consistent_def] >>
      first_x_assum drule >> simp[]) >>
  qpat_x_assum `!y. expr_size y < _ ==> _` (qspec_then `e'` mp_tac) >>
  (impl_tac >- simp[expr_size_def]) >>
  disch_then (qspecl_then [`env`,`cx`,`st`,`vt'`] mp_tac) >>
  simp[] >> strip_tac >>
  metis_tac[subscript_vtype_well_formed_stmt]
QED

Theorem type_place_expr_annotation_ok_stmt[local]:
  !env e vt. type_place_expr env e = SOME vt ==> vtype_annotation_ok vt (expr_type e)
Proof
  Cases_on `e` >> simp[expr_type_def] >> rpt strip_tac >>
  TRY (PairCases_on `p`) >>
  qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
  simp[Once well_typed_expr_def, vtype_annotation_ok_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem eval_expr_subscript_index_matches_stmt[local]:
  !ct ie rt cx st tv st1 idx st2.
    subscript_type_ok ct ie rt /\
    eval_expr cx ie st = (INL tv,st1) /\
    read_result cx tv st1 = (INL idx,st2) ==>
    subscript_index_matches ct ie idx
Proof
  rpt gen_tac >> Cases_on `ct` >> simp[subscript_index_matches_def] >>
  rpt strip_tac >>
  gvs[subscript_type_ok_tuple] >>
  gvs[Once evaluate_def, evaluate_literal_def, return_def, read_result_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Subscript]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v9 e e'))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    metis_tac[call_evaluation_safe_append_left]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v9 e e'))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    metis_tac[call_evaluation_safe_append_right]) >>
  conj_tac
  >- (strip_tac >>
      qpat_x_assum `well_typed_expr env (Subscript v9 e e')` mp_tac >>
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [well_typed_expr_def])) >>
      strip_tac
      >- (qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
          qpat_x_assum `eval_expr cx (Subscript _ e e') st = _` mp_tac >>
          simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
          Cases_on `eval_expr cx e st` >>
          rename1 `eval_expr cx e st = (br,st1)` >>
          qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
            (qspecl_then [`env`,`st`,`br`,`st1`] mp_tac) >>
          (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
          qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
          qpat_x_assum `well_typed_expr env e ==> _` drule >>
          simp_tac(srw_ss())[] >> strip_tac >>
          Cases_on `br`
          >- (rename1 `eval_expr cx e st = (INL base_pv,st1)` >>
              qpat_x_assum `!s'' pv t. eval_expr cx e s'' = (INL pv,t) ==> _` drule >> strip_tac >>
              simp_tac(srw_ss())[] >>
              Cases_on `eval_expr cx e' st1` >>
              rename1 `eval_expr cx e' st1 = (ir,st2)` >>
              qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
                (qspecl_then [`env`,`st1`,`ir`,`st2`] mp_tac) >>
              (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
              qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
                (qspecl_then [`env`,`st1`,`ir`,`st2`] mp_tac) >>
              (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
              qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
              qpat_x_assum `well_typed_expr env e' ==> _` drule >>
              simp_tac(srw_ss())[] >> strip_tac >>
              Cases_on `ir`
              >- (rename1 `eval_expr cx e' st1 = (INL idx,st2)` >>
                  simp_tac(srw_ss())[] >>
                  Cases_on `read_result cx idx st2` >>
                  rename1 `read_result cx idx st2 = (rr,st3)` >>
                  rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
                  rule_assum_tac BETA_RULE >>
                  qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> _` kall_tac >>
                  qpat_x_assum `!vt. type_place_expr env e' = SOME vt ==> _` kall_tac >>
                  drule_all live_result_read_typed >> strip_tac >> gvs[] >>
                  Cases_on `rr`
                  >- (rename1 `read_result cx idx st2 = (INL v,st2)` >>
                      `vyperImmutableMetadataFrame$immutable_metadata_frame st1 st2` by
                        (drule eval_expr_immutable_metadata_frame >> simp[]) >>
                      `eval_result_typed (env,cx,st2) base_pv (Type (expr_type e))` by
                        (irule eval_result_typed_transport >> goal_assum drule_all) >>
                      `live_memory_result st2 base_pv` by
                        (Cases_on `base_pv`
                         >- simp[live_memory_result_def]
                         >- (rename1 `PlaceR p` >> Cases_on `p`
                             >- simp[live_memory_result_def]
                             >- (irule live_memory_result_transport >> goal_assum drule_all)
                             >> simp[live_memory_result_def])
                         >> simp[live_memory_result_def]) >>
                      `subscript_index_matches (expr_type e) e' v` by
                        (drule_all eval_expr_subscript_index_matches_stmt >> simp[]) >>
                      simp_tac(srw_ss())[] >> strip_tac >>
                      rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
                      rule_assum_tac BETA_RULE >>
                      drule_all select_ordinary_subscript_sound >> strip_tac >> gvs[expr_type_def]) >>
                  simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]) >>
              simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]) >>
          qpat_x_assum `!s'' pv t. _` kall_tac >>
          simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]) >>
      simp_tac(srw_ss())[expr_type_def] >>
      suspend "Expr_Subscript_projection") >>
  gen_tac >> strip_tac >>
  qpat_x_assum `type_place_expr env (Subscript v9 e e') = SOME vt` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def, AllCaseEqs()] >>
  strip_tac >> suspend "Expr_Subscript_projection"
QED

Resume eval_scc_type_sound_results_mutual[Expr_Subscript_projection]:
  RESUME_TAC >> (
  qmatch_asmsub_rename_tac `type_place_expr env e = SOME bvt` >>
  `well_formed_vtype env.type_defs bvt` by
    metis_tac[type_place_expr_well_formed_vtype_stmt] >>
  `vtype_annotation_ok bvt (expr_type e)` by
    metis_tac[type_place_expr_annotation_ok_stmt] >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
  qpat_x_assum `eval_expr cx (Subscript _ e e') st = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (br,st1)` >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (qspecl_then [`env`,`st`,`br`,`st1`] mp_tac) >>
  (impl_tac >- (conj_tac >- (disj2_tac >> goal_assum drule) >> simp[])) >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` kall_tac >>
  qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> _`
    (qspec_then `bvt` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `br`
  >- (rename1 `eval_expr cx e st = (INL base_pv,st1)` >>
      qpat_x_assum `!s'' pv t. eval_expr cx e s'' = (INL pv,t) ==> _` drule >> strip_tac >>
      simp_tac(srw_ss())[] >>
      Cases_on `eval_expr cx e' st1` >>
      rename1 `eval_expr cx e' st1 = (ir,st2)` >>
      qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
        (qspecl_then [`env`,`st1`,`ir`,`st2`] mp_tac) >>
      (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
      qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
        (qspecl_then [`env`,`st1`,`ir`,`st2`] mp_tac) >>
      (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
      qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
      qpat_x_assum `well_typed_expr env e' ==> _` drule >>
      simp_tac(srw_ss())[] >> strip_tac >>
      qpat_x_assum `!vt. type_place_expr env e' = SOME vt ==> _` kall_tac >>
      Cases_on `ir`
      >- (rename1 `eval_expr cx e' st1 = (INL idx,st2)` >>
          simp_tac(srw_ss())[] >>
          Cases_on `read_result cx idx st2` >>
          rename1 `read_result cx idx st2 = (rr,st3)` >>
          rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
          rule_assum_tac BETA_RULE >>
          drule_all live_result_read_typed >> strip_tac >> gvs[] >>
          Cases_on `rr`
          >- (rename1 `read_result cx idx st2 = (INL v,st2)` >>
              `vyperImmutableMetadataFrame$immutable_metadata_frame st1 st2` by
                (drule eval_expr_immutable_metadata_frame >> simp[]) >>
              `eval_result_typed (env,cx,st2) base_pv bvt` by
                (irule eval_result_typed_transport >> goal_assum drule_all) >>
              `live_memory_result st2 base_pv` by
                (Cases_on `base_pv`
                 >- simp[live_memory_result_def]
                 >- (rename1 `PlaceR p` >> Cases_on `p`
                     >- simp[live_memory_result_def]
                     >- (irule live_memory_result_transport >> goal_assum drule_all)
                     >> simp[live_memory_result_def])
                 >> simp[live_memory_result_def]) >>
              simp_tac(srw_ss())[] >> strip_tac >>
              rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
              rule_assum_tac BETA_RULE >>
              drule_all select_projection_subscript_sound >> strip_tac >> gvs[expr_type_def]) >>
          simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]) >>
      simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]) >>
  qpat_x_assum `!s'' pv t. _` kall_tac >>
  simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def])
QED


(* ===== Attribute expression helpers and Resume block ===== *)

Theorem select_attribute_sound[local]:
  !env cx st bp ct id rt res st'.
  env_consistent env cx st /\ state_well_typed st /\
  eval_result_typed (env,cx,st) bp (Type ct) /\ live_memory_result st bp /\
  attribute_type env.type_defs ct id = SOME rt /\
  select_result cx ct bp (AttrSubscript id) st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  (case res of INL pv => eval_result_typed (env,cx,st') pv (Type rt) | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  Cases_on `bp`
  >- (gvs[eval_result_typed_def] >>
      drule_all attribute_type_runtime_step >> strip_tac >>
      `well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
      `subscripts_type tv [AttrSubscript id] = SOME field_tv` by
        simp[subscripts_type_def] >>
      Cases_on `evaluate_subscripts tv v [AttrSubscript id]` >>
      gvs[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
          return_def, raise_def] >> simp[no_type_error_result_def]
      >- (drule_all vyperPlaceStatePreservationTheory.evaluate_subscripts_type >> simp[]) >>
      metis_tac[evaluate_subscripts_typed_error])
  >- (rename1 `PlaceR p` >>
      `?tv. evaluate_type env.type_defs ct = SOME tv /\ runtime_place_typed cx st p tv` by
        gvs[eval_result_typed_def] >>
      drule_all attribute_type_runtime_step >> strip_tac >>
      gvs[select_result_def] >>
      `st' = st` by metis_tac[vyperPlaceFramesTheory.extend_place_state, SND] >>
      `no_type_error_result res` by metis_tac[extend_live_place_attribute_no_type_error] >>
      Cases_on `res` >> simp[] >>
      `eval_result_typed (env,cx,st) (PlaceR p) (Type ct)` by
        (simp[eval_result_typed_def] >> metis_tac[]) >>
      `attribute_type env.type_defs ct id = SOME rt` by simp[] >>
      drule_all extend_place_attribute_success_typed >> simp[]) >>
  gvs[eval_result_typed_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Attribute]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Attribute ty e id))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >> simp[]) >>
  reverse conj_tac >- (rpt strip_tac >>
    qpat_x_assum `type_place_expr _ (Attribute _ _ _) = SOME _` mp_tac >>
    simp_tac(srw_ss())[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Attribute ty e id)` mp_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [well_typed_expr_def])) >>
  strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
  qpat_x_assum `eval_expr cx (Attribute ty e id) st = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (br,st1)` >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (qspecl_then [`env`,`st`,`br`,`st1`] mp_tac) >>
  (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` drule >>
  simp_tac(srw_ss())[] >> strip_tac >>
  Cases_on `br`
  >- (simp_tac(srw_ss())[] >> strip_tac >>
      rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
      rule_assum_tac BETA_RULE >>
      qpat_x_assum `attribute_type_ok _ _ _ _` mp_tac >>
      simp_tac(srw_ss())[attribute_type_ok_def] >> strip_tac >>
      drule_all select_attribute_sound >> strip_tac >> gvs[expr_type_def]) >>
  simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]
QED

(* ===== Builtin, type-builtin, and pop expression cases ===== *)

Theorem nested_return_value_case[local]:
  ((case (case INL x of INL v => return v | INR e => raise (Error e)) st of
      (INL v,s'') => (INL (Value v),s'')
    | (INR e,s'') => (INR e,s'')) = (res,st')) <=>
  res = INL (Value x) /\ st' = st
Proof
  simp[return_def] >> metis_tac[]
QED

Theorem nested_raise_error_case[local]:
  ((case (case INR x of INL v => return v | INR e => raise (Error e)) st of
      (INL v,s'') => (INL (Value v),s'')
    | (INR e,s'') => (INR e,s'')) = (res,st')) <=>
  res = INR (Error x) /\ st' = st
Proof
  simp[raise_def] >> metis_tac[]
QED

Theorem eval_exprs_failure_builtin_case[local]:
  ((case
      case (INR x,st) of
        (INL vs,s'') =>
          (case evaluate_builtin cx s''.accounts ty bt (MAP expr_type es) vs of
             INL v => return v
           | INR e => raise (Error e)) s''
      | (INR e,s'') => (INR e,s'')
    of
      (INL v,s'') => (INL (Value v),s'')
    | (INR e,s'') => (INR e,s'')) = (res,st')) <=>
  res = INR x /\ st' = st
Proof
  simp[] >> metis_tac[]
QED

Theorem eval_exprs_failure_type_builtin_case[local]:
  ((case (INR x,st) of
      (INL vs,s'') =>
        (case
           (case evaluate_type_builtin cx tb target_ty (MAP expr_type es) vs of
              INL v => return v
            | INR e => raise (Error e)) s''
         of
           (INL v,s'') => (INL (Value v),s'')
         | (INR e,s'') => (INR e,s''))
    | (INR e,s'') => (INR e,s'')) = (res,st')) <=>
  res = INR x /\ st' = st
Proof
  simp[] >> metis_tac[]
QED


Theorem type_builtin_exprs_runtime_no_type_error_stmt_adapter[local]:
  env.type_defs = get_tenv cx /\
  type_builtin_result_ok env.type_defs tb result_ty target_ty (MAP expr_type es) /\
  well_typed_type_builtin_args tb target_ty (MAP expr_type es) /\
  well_formed_type env.type_defs result_ty /\
  exprs_runtime_typed env es vs /\
  context_well_typed cx ==>
  !msg. evaluate_type_builtin cx tb target_ty (MAP expr_type es) vs <> INR (TypeError msg)
Proof
  rw[exprs_runtime_typed_def] >>
  `MAP (evaluate_type (get_tenv cx)) (MAP expr_type es) = MAP SOME tvs` by
    gvs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP] >>
  `?result_tv. evaluate_type (get_tenv cx) result_ty = SOME result_tv` by
    gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  mp_tac (Q.INST [`ts` |-> `MAP expr_type es`]
            well_typed_type_builtin_no_type_error) >>
  gvs[]
QED

Theorem type_builtin_exprs_runtime_success_type_stmt_adapter[local]:
  env.type_defs = get_tenv cx /\
  type_builtin_result_ok env.type_defs tb result_ty target_ty (MAP expr_type es) /\
  well_typed_type_builtin_args tb target_ty (MAP expr_type es) /\
  well_formed_type env.type_defs result_ty /\
  exprs_runtime_typed env es vs /\
  context_well_typed cx /\
  evaluate_type_builtin cx tb target_ty (MAP expr_type es) vs = INL v ==>
  value_runtime_typed env result_ty v
Proof
  rw[exprs_runtime_typed_def, value_runtime_typed_def] >>
  `MAP (evaluate_type (get_tenv cx)) (MAP expr_type es) = MAP SOME tvs` by
    gvs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP] >>
  `?result_tv. evaluate_type (get_tenv cx) result_ty = SOME result_tv` by
    gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  qexists_tac `result_tv` >> simp[] >>
  irule well_typed_type_builtin_success_type >>
  qexistsl_tac [`cx`, `result_ty`, `target_ty`, `tb`, `MAP expr_type es`, `tvs`, `vs`] >>
  gvs[]
QED

Theorem Len_live_result_sound[local]:
  state_well_typed st /\ well_typed_builtin_app ty Len [arg_ty] /\
  eval_result_typed (env,cx,st) pv (Type arg_ty) /\ live_memory_result st pv /\
  result_array_length cx pv st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  (case res of INL n => eval_result_typed (env,cx,st) (Value (IntV (&n))) (Type ty) | INR _ => T)
Proof
  strip_tac >>
  Cases_on `?tr slot tv bd. pv = PlaceR (StoragePlace tr slot (ArrayTV tv bd))`
  >- (gvs[] >>
      gvs[eval_result_typed_def, runtime_place_typed_storage] >>
      Cases_on `bd` >>
      gvs[result_array_length_def, return_def, bind_def, get_storage_backend_def,
          get_accounts_def, get_transient_storage_def, AllCaseEqs(),
          no_type_error_result_def]
      >- (Cases_on `arg_ty` >>
          gvs[evaluate_type_def, AllCaseEqs(), well_typed_builtin_app_def,
              value_has_type_def, type_slot_size_def] >>
          `n <= n * type_slot_size tv` by simp[] >> decide_tac)
      >- (drule vyperStorageBackendTheory.get_storage_backend_state >> strip_tac >> gvs[] >>
          `w2n (lookup_storage slot storage) < dimword(:256)` by
            simp_tac(srw_ss())[wordsTheory.w2n_lt] >>
          gvs[well_typed_builtin_app_def, evaluate_type_def, value_has_type_def]) >>
      metis_tac[get_storage_backend_no_error]) >>
  `result_array_length cx pv = do v <- read_result cx pv; result_array_length cx (Value v) od` by
    (Cases_on `pv`
     >- simp[FUN_EQ_THM, result_array_length_def, read_result_def, return_def, bind_def]
     >- (rename1 `PlaceR p` >> namedCases_on `p` ["tr slot ptv", "mid path", "src iid path"]
         >- (Cases_on `ptv` >>
             gvs[result_array_length_def, FUN_EQ_THM, bind_def, read_result_def, return_def]) >>
         simp[result_array_length_def, FUN_EQ_THM, bind_def, read_result_def, return_def]) >>
     simp[FUN_EQ_THM, result_array_length_def, read_result_def, raise_def, bind_def]) >>
  qpat_x_assum `result_array_length cx pv st = _` mp_tac >>
  asm_rewrite_tac[] >> simp_tac(srw_ss())[bind_def] >>
  Cases_on `read_result cx pv st` >>
  rename1 `read_result cx pv st = (rr,rs)` >>
  drule_all live_result_read_typed >> strip_tac >> gvs[] >>
  Cases_on `rr`
  >- (rename1 `read_result cx pv st = (INL v,st)` >>
      simp_tac(srw_ss())[] >> strip_tac >>
      `st' = st` by metis_tac[result_array_length_state] >> gvs[] >>
      gvs[value_runtime_typed_def] >>
      `value_result_typed (Value v) tv` by simp[value_result_typed_def] >>
      Cases_on `res` >> simp[no_type_error_result_def]
      >- (`well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
          `x < dimword(:256)` by (drule_all Len_result_fits_uint256 >> simp[]) >>
          gvs[well_typed_builtin_app_def, eval_result_typed_def,
              evaluate_type_def, value_has_type_def]) >>
      `well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
      Cases_on `y` >> simp[no_type_error_result_def] >>
      Cases_on `e` >> simp[no_type_error_result_def] >>
      metis_tac[Len_result_array_length_no_type_error]) >>
  simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Builtin]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Builtin ty bt es))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Builtin _ _ _) = SOME _` mp_tac >>
      simp_tac(srw_ss())[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Builtin ty bt es)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by metis_tac[env_consistent_def, env_context_consistent_def] >>
  `builtin_args_length_ok bt (LENGTH es)` by
    (drule well_typed_builtin_app_length >> simp[]) >>
  qpat_x_assum `eval_expr cx (Builtin ty bt es) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def,
                       type_check_def, assert_def] >>
  Cases_on `bt = Len`
  >- (`es <> []` by (
        Cases_on `es` >> simp[] >>
        qpat_x_assum `well_typed_builtin_app ty bt (MAP expr_type [])` mp_tac >>
        qpat_x_assum `bt = Len` (fn th => rewrite_tac[th]) >>
        simp[well_typed_builtin_app_def]) >>
      `call_evaluation_safe cx (int_calls_expr (HD es))` by
        metis_tac[call_evaluation_safe_int_calls_exprs_HD] >>
      qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
      qpat_assum `bt = Len` (fn th => rewrite_tac[th]) >>
      simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
                         type_check_def, assert_def] >>
      Cases_on `eval_expr cx (HD es) st` >>
      rename1 `eval_expr cx (HD es) st = (arg_res,arg_st)` >>
      qpat_x_assum `!s'' x t. _ /\ bt = Len ==> _`
        (qspecl_then [`st`,`()`,`st`] mp_tac) >>
      (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
      `well_typed_expr env (HD es)` by
        (qpat_assum `well_typed_exprs env es` mp_tac >>
         rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
         qpat_x_assum `!s'' x t. _` kall_tac >>
         Cases_on `es` >> gvs[Once well_typed_expr_def]) >>
      `well_typed_builtin_app ty Len [expr_type (HD es)]` by
        (rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
         qpat_x_assum `!s'' x t. _` kall_tac >>
         Cases_on `es` >> gvs[well_typed_builtin_app_def] >>
         Cases_on `t` >> gvs[]) >>
      qpat_x_assum `!env st res st'. _ ==> (well_typed_expr _ _ ==> _) /\ _`
        (qspecl_then [`env`,`st`,`arg_res`,`arg_st`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `well_typed_expr env (HD es) ==> _` mp_tac >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result st' pv | INR _ => T`
        (qspecl_then [`env`,`st`,`arg_res`,`arg_st`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
      qpat_x_assum `!s'' x t. _` kall_tac >>
      Cases_on `arg_res`
      >- (rename1 `eval_expr cx (HD es) st = (INL arg_tv,arg_st)` >>
          gvs[] >>
          Cases_on `result_array_length cx arg_tv arg_st` >>
          rename1 `result_array_length cx arg_tv arg_st = (len_res,len_st)` >>
          drule_all Len_live_result_sound >> strip_tac >> gvs[] >>
          Cases_on `len_res` >>
          simp_tac(srw_ss())[return_def, raise_def] >> strip_tac >>
          gvs[no_type_error_result_def, expr_type_def]) >>
      simp_tac(srw_ss())[] >> strip_tac >> gvs[]) >>
  qpat_assum `bt <> Len` (fn th => rewrite_tac[th]) >>
  qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
                     type_check_def, assert_def, get_accounts_def, lift_sum_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  qpat_x_assum `!s'' x t. _ /\ bt <> Len ==> _`
    (qspecl_then [`st`,`()`,`st`] mp_tac) >>
  (impl_tac >- (simp[type_check_def, assert_def] >> metis_tac[])) >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> _ /\ _ /\ _ /\ _ /\ case res of INL vs => exprs_runtime_typed env es vs | INR _ => T`
    (qspecl_then [`env`,`st`,`args_res`,`args_st`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
  qpat_x_assum `!s'' x t. _` kall_tac >>
  Cases_on `args_res`
  >- (
    rename1 `eval_exprs cx es st = (INL vs,args_st)` >>
    qpat_x_assum `case INL vs of INL vs => exprs_runtime_typed env es vs | INR v1 => T`
      mp_tac >> simp_tac(srw_ss())[] >> strip_tac >>
    qpat_x_assum `exprs_runtime_typed env es vs` mp_tac >>
    rewrite_tac[exprs_runtime_typed_def] >> strip_tac >>
    `MAP (evaluate_type (get_tenv cx)) (MAP expr_type es) = MAP SOME tvs` by
      (gvs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP]) >>
    `?ret_tv. evaluate_type (get_tenv cx) ty = SOME ret_tv` by
      (gvs[well_formed_type_def, IS_SOME_EXISTS]) >>
    Cases_on `evaluate_builtin cx args_st.accounts ty bt (MAP expr_type es) vs` >>
    rename1 `evaluate_builtin cx args_st.accounts ty bt (MAP expr_type es) vs = builtin_res` >>
    Cases_on `builtin_res` >>
    FIRST [
      rename1 `evaluate_builtin cx args_st.accounts ty bt (MAP expr_type es) vs = INL builtin_v` >>
      strip_tac >>
      gvs[nested_return_value_case, no_type_error_result_def] >>
      gvs[expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
          value_result_typed_Value] >>
      mp_tac (Q.INST [`blt` |-> `bt`, `ts` |-> `MAP expr_type es`,
                       `acc` |-> `(args_st:evaluation_state).accounts`,
                       `tv` |-> `ret_tv`, `v` |-> `builtin_v`,
                       `cx` |-> `cx`, `tvs` |-> `tvs`, `vs` |-> `vs`,
                       `ty` |-> `ty`]
                well_typed_builtin_app_success_type) >>
      simp[],
      strip_tac >>
      gvs[nested_raise_error_case, no_type_error_result_def] >>
      strip_tac >> spose_not_then assume_tac >> gvs[] >>
      `!item. bt = Env item ==> item <> MsgGas` by
        (rpt strip_tac >> gvs[well_typed_builtin_app_def]) >>
      drule_all well_typed_builtin_app_no_type_error >>
      disch_then (qspec_then `msg` mp_tac) >> gvs[]]) >>
  strip_tac >> gvs[eval_exprs_failure_builtin_case, no_type_error_result_def]
QED

(* The ABI and ordinary argument paths share the typed-values boundary. *)
Definition type_builtin_args_def:
  type_builtin_args cx tb es =
    case tb of
    | AbiEncode _ _ => do
        mark <- mark_abi_captures;
        finally (do args <- eval_abi_exprs cx es; stage_abi_operands cx args od)
          (release_abi_captures mark)
      od
    | _ => eval_exprs cx es
End

Theorem abi_encode_args_sound[local]:
  (!res rt. eval_abi_exprs cx es st = (res,rt) ==>
    state_well_typed rt /\ env_consistent env cx rt /\
    accounts_well_typed rt.accounts /\ no_type_error_result res /\
    case res of INL args => abi_exprs_result_valid env rt es args | INR _ => T) /\
  finally (do args <- eval_abi_exprs cx es; stage_abi_operands cx args od)
    (release_abi_captures mark) st = (res,rt) ==>
  state_well_typed rt /\ env_consistent env cx rt /\
  accounts_well_typed rt.accounts /\ no_type_error_result res /\
  case res of INL vs => exprs_runtime_typed env es vs | INR _ => T
Proof
  strip_tac >> Cases_on `eval_abi_exprs cx es st` >>
  rename1 `eval_abi_exprs cx es st = (args_res,args_st)` >>
  qpat_x_assum `!res rt. _`
    (qspecl_then [`args_res`,`args_st`] mp_tac) >>
  simp_tac(srw_ss())[] >> strip_tac >> Cases_on `args_res`
  >- (gvs[] >> Cases_on `stage_abi_operands cx x args_st` >>
      rename1 `stage_abi_operands cx x args_st = (stage_res,stage_st)` >>
      drule_all abi_exprs_result_valid_stage_no_type_error >> strip_tac >>
      Cases_on `stage_res`
      >- (drule_all abi_exprs_result_valid_stage >> strip_tac >>
          gvs[finally_def, bind_def, ignore_bind_def, release_abi_captures_def,
              return_def, raise_def]) >>
      gvs[finally_def, bind_def, ignore_bind_def, release_abi_captures_def,
          return_def, raise_def, no_type_error_result_def]) >>
  gvs[finally_def, bind_def, ignore_bind_def, release_abi_captures_def,
      return_def, raise_def, no_type_error_result_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_TypeBuiltin]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_expr cx (TypeBuiltin result_ty tb target_ty es) st = (res,st')` >>
  `call_evaluation_safe cx (int_calls_exprs es)` by (
    qpat_assum `call_evaluation_safe cx
      (int_calls_expr (TypeBuiltin result_ty tb target_ty es))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (TypeBuiltin _ _ _ _) = SOME _` mp_tac >>
      simp_tac(srw_ss())[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (TypeBuiltin result_ty tb target_ty es)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by metis_tac[env_consistent_def, env_context_consistent_def] >>
  `type_builtin_args_length_ok tb (LENGTH es)` by
    (drule well_typed_type_builtin_args_length >> simp[]) >>
  `!r rt. type_builtin_args cx tb es st = (r,rt) ==>
    state_well_typed rt /\ env_consistent env cx rt /\
    accounts_well_typed rt.accounts /\ no_type_error_result r /\
    case r of INL vs => exprs_runtime_typed env es vs | INR _ => T` by
    (Cases_on `tb` >>
     fs[type_builtin_args_def, type_check_def, assert_def,
        mark_abi_captures_def, bind_def, return_def] >>
     rpt gen_tac >> strip_tac >>
     FIRST [
       (`!r0 rt0. eval_abi_exprs cx es st = (r0,rt0) ==>
          state_well_typed rt0 /\ env_consistent env cx rt0 /\
          accounts_well_typed rt0.accounts /\ no_type_error_result r0 /\
          case r0 of INL args => abi_exprs_result_valid env rt0 es args
                   | INR _ => T` by
          (rpt gen_tac >> strip_tac >>
           qpat_assum `!env st res st'. _ ==> state_well_typed _ /\ _`
             (drule_all_then strip_assume_tac) >> simp[]) >>
        drule_all abi_encode_args_sound >> simp[]),
       qpat_assum `!env st res st'. _ ==> state_well_typed _ /\ _`
         (drule_all_then strip_assume_tac) >> simp[]]) >>
  rpt (qpat_x_assum `!s'' x t. _` kall_tac) >>
  qpat_x_assum `eval_expr cx (TypeBuiltin result_ty tb target_ty es) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, GSYM type_builtin_args_def,
                       bind_def, return_def, raise_def, type_check_def, assert_def] >>
  qpat_assum `type_builtin_args_length_ok tb (LENGTH es)` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
                     type_check_def, assert_def] >>
  Cases_on `type_builtin_args cx tb es st` >>
  rename1 `type_builtin_args cx tb es st = (args_res,args_st)` >>
  qpat_x_assum `!r rt. (args_res,args_st) = (r,rt) ==> _`
    (qspecl_then [`args_res`,`args_st`] mp_tac) >>
  simp_tac(srw_ss())[] >> strip_tac >>
  Cases_on `args_res`
  >- (rename1 `type_builtin_args cx tb es st = (INL vs,args_st)` >>
      qpat_x_assum `case INL vs of INL vs => exprs_runtime_typed env es vs | INR v1 => T`
        mp_tac >> simp_tac(srw_ss())[] >> strip_tac >>
      Cases_on `evaluate_type_builtin cx tb target_ty (MAP expr_type es) vs`
      >- (rename1 `evaluate_type_builtin cx tb target_ty (MAP expr_type es) vs = INL builtin_v` >>
          strip_tac >>
          gvs[lift_sum_def, return_def, no_type_error_result_def] >>
          simp_tac(srw_ss())[expr_type_def] >>
          metis_tac[type_builtin_exprs_runtime_success_type_stmt_adapter,
                    value_runtime_typed_def]) >>
      rename1 `evaluate_type_builtin cx tb target_ty (MAP expr_type es) vs = INR type_exn` >>
      strip_tac >>
      gvs[lift_sum_def, raise_def, no_type_error_result_def] >>
      strip_tac >> spose_not_then assume_tac >> gvs[] >>
      metis_tac[type_builtin_exprs_runtime_no_type_error_stmt_adapter]) >>
  strip_tac >> gvs[eval_exprs_failure_type_builtin_case, no_type_error_result_def]
QED


Resume eval_scc_type_sound_results_mutual[Expr_Pop]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_expr cx (Pop v11 bt) st = (res,st')` >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Pop v11 bt))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  reverse conj_tac
  >- (gen_tac >> strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  drule well_typed_expr_Pop_dynamic_target_assignable >> strip_tac >>
  `well_typed_target env bt (ArrayT v11 (Dynamic n))` by simp[well_typed_target_def] >>
  qpat_x_assum `eval_expr cx (Pop v11 bt) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,st1)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => live_memory_result _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => writable_place_result _ _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  rpt (qpat_x_assum `!env ty st res st'. _` kall_tac) >>
  Cases_on `target_res`
  >- (rename1 `eval_target_place cx bt st = (INL p,st1)` >>
      gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
      rename1 `evaluate_type env.type_defs v11 = SOME tv` >>
      `runtime_consistent env cx st1` by simp[runtime_consistent_def] >>
      `runtime_place_writable cx st1 p` by gvs[writable_place_result_def] >>
      Cases_on `pop_place cx p st1` >>
      rename1 `pop_place cx p st1 = (pop_res,pop_st)` >>
      `runtime_consistent env cx pop_st /\ no_type_error_result pop_res` by
        (irule pop_place_sound >> goal_assum (drule_at Any) >>
         Cases_on `p` >> gvs[live_memory_result_def] >> metis_tac[]) >>
      Cases_on `pop_res`
      >- (rename1 `pop_place cx p st1 = (INL pv,pop_st)` >>
          `case pv of Value v => value_has_type tv v
             | PlaceR q => runtime_place_typed cx pop_st q tv
             | HashMapRef _ _ _ _ => F` by
            (irule pop_place_result_typed >>
             goal_assum (drule_at (Pat `pop_place _ _ _ = _`)) >>
             Cases_on `p` >> gvs[live_memory_result_def] >> metis_tac[]) >>
          simp_tac(srw_ss())[] >> strip_tac >>
          gvs[runtime_consistent_def, expr_type_def, eval_result_typed_def] >>
          Cases_on `pv` >> gvs[]) >>
      simp_tac(srw_ss())[] >> strip_tac >> gvs[runtime_consistent_def]) >>
  simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]
QED


(* ===== Internal call helpers and Resume block ===== *)

Theorem defaults_env_empty_frame_consistent:
  !env_body cx st.
    env_context_consistent env_body cx /\
    env_immutables_consistent env_body cx st ==>
    env_consistent (defaults_env env_body) cx (st with scopes := [FEMPTY])
Proof
  rw[defaults_env_def, env_consistent_def, env_context_consistent_def,
     env_scopes_consistent_def, env_immutables_consistent_def,
     lookup_scopes_def] >>
  gvs[] >>
  metis_tac[]
QED

Theorem default_frame_eval_result[local]:
  !cx es st prev res st'.
    finally
      (do set_scopes [FEMPTY]; eval_exprs cx es od)
      (set_scopes prev) st = (res,st') ==>
    ?framed_st.
      eval_exprs cx es (st with scopes := [FEMPTY]) = (res,framed_st) /\
      st' = (framed_st with scopes := prev)
Proof
  rw[finally_def, bind_def, ignore_bind_def, set_scopes_def,
     return_def, raise_def] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  Cases_on `q` >>
  gvs[ignore_bind_def, set_scopes_def, return_def, raise_def]
QED

Theorem state_well_typed_restore_scopes[local]:
  !st scopes_src.
    state_well_typed st /\ state_well_typed scopes_src ==>
    state_well_typed (st with scopes := scopes_src.scopes)
Proof
  rw[state_well_typed_def]
QED


Theorem env_consistent_restore_intcall_default_frame[local]:
  !env env_body cx src_id_opt fn base_st framed_st.
    env_consistent env cx base_st /\
    env_consistent (defaults_env env_body)
      (cx with stk updated_by CONS (src_id_opt,fn)) framed_st /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    env_consistent env cx (framed_st with scopes := base_st.scopes)
Proof
  rw[env_consistent_def]
  >- (qpat_x_assum `env_scopes_consistent env cx base_st` mp_tac >>
      simp[env_scopes_consistent_def] >> metis_tac[]) >>
  gvs[env_immutables_consistent_def, defaults_env_def,
      get_tenv_stk_irrelevant, get_module_code_stk_irrelevant] >>
  metis_tac[]
QED

Theorem intcall_defaults_restored_sound[local]:
  env_consistent env cx base_st /\ state_well_typed base_st /\
  env_body.type_defs = get_tenv cx /\
  env_body.bare_globals = env.bare_globals /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  expr_results_typed (env,cx,base_st) es results /\
  (!r fs. eval_exprs (cx with stk updated_by CONS (src_id_opt,fn)) needed
               (base_st with scopes := [FEMPTY]) = (r,fs) ==>
     state_well_typed fs /\
     env_consistent (defaults_env env_body)
       (cx with stk updated_by CONS (src_id_opt,fn)) fs /\
     accounts_well_typed fs.accounts /\ no_type_error_result r /\
     (case r of INL vs => exprs_runtime_typed (defaults_env env_body) needed vs
              | INR _ => T)) /\
  finally (do set_scopes [FEMPTY];
              eval_exprs (cx with stk updated_by CONS (src_id_opt,fn)) needed od)
    (set_scopes base_st.scopes) base_st = (res,st') ==>
  st'.scopes = base_st.scopes /\ state_well_typed st' /\
  env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
  no_type_error_result res /\ expr_results_typed (env,cx,st') es results /\
  (case res of INL vs => exprs_runtime_typed (defaults_env env_body) needed vs
             | INR _ => T)
Proof
  strip_tac >> drule default_frame_eval_result >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `state_well_typed (framed_st with scopes := base_st.scopes)` by
    (irule state_well_typed_restore_scopes >> simp[]) >>
  `env_consistent env cx (framed_st with scopes := base_st.scopes)` by
    (metis_tac[env_consistent_restore_intcall_default_frame]) >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame
     (base_st with scopes := [FEMPTY]) framed_st` by
    (drule (cj 6 eval_metadata_frame_mutual) >> simp[]) >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame base_st st'` by
    (gvs[vyperImmutableMetadataFrameTheory.immutable_metadata_frame_def] >>
     metis_tac[]) >>
  `st'.scopes = base_st.scopes` by simp[] >>
  drule_all expr_results_typed_restore_scopes >>
  gvs[]
QED

Theorem intcall_safe_cast_NoneTV_NoneV[local]:
  safe_cast NoneTV NoneV = SOME NoneV
Proof
  simp[Once safe_cast_def]
QED

Theorem intcall_finally_try_handle_success_rv[local]:
  !fn_m cleanup pushed_st rv st_final.
    finally (try (do fn_m; return NoneV od) handle_function)
      cleanup pushed_st = (INL rv,st_final) ==>
    (rv = NoneV /\ (?st_bdy. fn_m pushed_st = (INL (),st_bdy))) \/
    (?v st_bdy. rv = v /\ fn_m pushed_st = (INR (ReturnException v),st_bdy))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[finally_def] >>
  Cases_on `try (do fn_m; return NoneV od) handle_function pushed_st` >>
  rename1 `_ = (try_res,try_st)` >>
  Cases_on `try_res` >> gvs[ignore_bind_apply] >>
  Cases_on `cleanup try_st` >> rename1 `_ = (cl_res,cl_st)` >>
  Cases_on `cl_res` >> gvs[return_def, raise_def] >>
  gvs[try_def] >>
  Cases_on `(do fn_m; return NoneV od) pushed_st` >>
  rename1 `_ = (inner_res,inner_st)` >>
  Cases_on `inner_res` >> gvs[return_def]
  >- (gvs[ignore_bind_apply, return_def] >>
      Cases_on `fn_m pushed_st` >> rename1 `_ = (fn_res,fn_st)` >>
      Cases_on `fn_res` >> gvs[return_def, raise_def])
  >- (Cases_on `y` >>
      gvs[handle_function_def, return_def, raise_def] >>
      Cases_on `fn_m pushed_st` >> Cases_on `q` >>
      gvs[return_def, raise_def, ignore_bind_apply])
QED

Theorem intcall_finally_try_handle_success_cleanup[local]:
  !fn_m cleanup pushed_st rv st_final.
    finally (try (do fn_m; return NoneV od) handle_function)
      cleanup pushed_st = (INL rv,st_final) ==>
    (rv = NoneV /\
     (?st_bdy. fn_m pushed_st = (INL (),st_bdy) /\
               cleanup st_bdy = (INL (),st_final))) \/
    (?v st_bdy. rv = v /\ fn_m pushed_st = (INR (ReturnException v),st_bdy) /\
                cleanup st_bdy = (INL (),st_final))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[finally_def] >>
  Cases_on `try (do fn_m; return NoneV od) handle_function pushed_st` >>
  rename1 `_ = (try_res,try_st)` >>
  Cases_on `try_res` >> gvs[ignore_bind_apply] >>
  Cases_on `cleanup try_st` >> rename1 `_ = (cl_res,cl_st)` >>
  Cases_on `cl_res` >> gvs[return_def, raise_def] >>
  gvs[try_def] >>
  Cases_on `(do fn_m; return NoneV od) pushed_st` >>
  rename1 `_ = (inner_res,inner_st)` >>
  Cases_on `inner_res` >> gvs[return_def]
  >- (gvs[ignore_bind_apply, return_def] >>
      Cases_on `fn_m pushed_st` >> rename1 `_ = (fn_res,fn_st)` >>
      Cases_on `fn_res` >> gvs[return_def, raise_def])
  >- (Cases_on `y` >>
      gvs[handle_function_def, return_def, raise_def] >>
      Cases_on `fn_m pushed_st` >> Cases_on `q` >>
      gvs[return_def, raise_def, ignore_bind_apply])
QED


Theorem intcall_finally_try_handle_inr_body_cleanup_cases[local]:
  !fn_m cleanup pushed_st y fin_st.
    finally (try (do fn_m; return NoneV od) handle_function)
      cleanup pushed_st = (INR y,fin_st) ==>
    (?st_bdy.
       fn_m pushed_st = (INL (),st_bdy) /\
       cleanup st_bdy = (INR y,fin_st)) \/
    (?body_exn st_bdy cleanup_res.
       fn_m pushed_st = (INR body_exn,st_bdy) /\
       cleanup st_bdy = (cleanup_res,fin_st))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[finally_def] >>
  Cases_on `try (do fn_m; return NoneV od) handle_function pushed_st` >>
  rename1 `_ = (try_res,try_st)` >>
  Cases_on `try_res` >> gvs[ignore_bind_apply] >>
  Cases_on `cleanup try_st` >> rename1 `_ = (cl_res,cl_st)` >>
  Cases_on `cl_res` >> gvs[return_def, raise_def] >>
  gvs[try_def] >>
  Cases_on `(do fn_m; return NoneV od) pushed_st` >>
  rename1 `_ = (inner_res,inner_st)` >>
  Cases_on `inner_res` >> gvs[return_def]
  >- (gvs[ignore_bind_apply, return_def] >>
      Cases_on `fn_m pushed_st` >> rename1 `_ = (fn_res,fn_st)` >>
      Cases_on `fn_res` >> gvs[return_def, raise_def]) >>
  Cases_on `fn_m pushed_st` >> rename1 `_ = (fn_res,fn_st)` >>
  Cases_on `fn_res` >>
  gvs[bind_apply, bind_def, return_def, raise_def, ignore_bind_apply] >>
  rename1 `handle_function body_exn _ = _` >>
  Cases_on `body_exn` >>
  gvs[handle_function_def, bind_apply, bind_def, return_def, raise_def,
      ignore_bind_apply]
QED
Theorem lift_safe_cast_value_has_type_no_type_error[local]:
  !tv v msg st res st'.
    value_has_type tv v /\
    lift_option_type (safe_cast tv v) msg st = (res,st') ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  `safe_cast tv v = SOME v` by (irule safe_cast_well_typed >> simp[]) >>
  gvs[lift_option_type_def, return_def, raise_def, no_type_error_result_def]
QED

Theorem env_consistent_restore_intcall_body_frame[local]:
  !env env_body cx src_id_opt fn base_st framed_st.
    env_consistent env cx base_st /\
    env_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) framed_st /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    env_consistent env cx (framed_st with scopes := base_st.scopes)
Proof
  rw[env_consistent_def]
  >- (qpat_x_assum `env_scopes_consistent env cx base_st` mp_tac >>
      simp[env_scopes_consistent_def] >> metis_tac[]) >>
  gvs[env_immutables_consistent_def, get_tenv_stk_irrelevant,
      get_module_code_stk_irrelevant] >>
  metis_tac[]
QED

Theorem env_consistent_same_scopes_immutables[local]:
  !env cx st st'.
    env_consistent env cx st /\
    st'.scopes = st.scopes /\
    st'.immutables = st.immutables ==>
    env_consistent env cx st'
Proof
  rw[env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def] >> metis_tac[]
QED

Theorem intcall_cleanup_frame_restore_sound[local]:
  !env env_body cx src_id_opt fn args_st st_bdy fin_st.
    env_consistent env cx args_st /\
    env_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) st_bdy /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    state_well_typed args_st /\
    state_well_typed st_bdy /\
    accounts_well_typed st_bdy.accounts /\
    fin_st.scopes = args_st.scopes /\
    fin_st.immutables = st_bdy.immutables /\
    fin_st.accounts = st_bdy.accounts ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt strip_tac >>
  `state_well_typed fin_st` by gvs[state_well_typed_def] >>
  `env_consistent env cx (st_bdy with scopes := args_st.scopes)` by
    (qspecl_then [`env`, `env_body`, `cx`, `src_id_opt`, `fn`,
                  `args_st`, `st_bdy`] mp_tac
       env_consistent_restore_intcall_body_frame >> simp[]) >>
  `env_consistent env cx fin_st` by
    (qspecl_then [`env`, `cx`, `st_bdy with scopes := args_st.scopes`,
                  `fin_st`] mp_tac env_consistent_same_scopes_immutables >>
     simp[]) >>
  simp[]
QED

Theorem intcall_cleanup_after_body_preserves_caller_frame[local]:
  !env env_body cx src_id_opt fn args_st st_bdy cleanup_res fin_st nr is_view.
    env_consistent env cx args_st /\
    env_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) st_bdy /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    state_well_typed args_st /\
    state_well_typed st_bdy /\
    accounts_well_typed st_bdy.accounts /\
    (do pop_function args_st.scopes;
        if nr /\ ~is_view then
          case cx.nonreentrant_slot of
          | NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ()
     od) st_bdy = (cleanup_res,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt strip_tac >>
  drule intcall_cleanup_after_pop_preserves_frame >>
  simp[] >> strip_tac >>
  qspecl_then [`env`, `env_body`, `cx`, `src_id_opt`, `fn`,
                `args_st`, `st_bdy`, `fin_st`] mp_tac
    intcall_cleanup_frame_restore_sound >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[]
QED


Theorem intcall_default_finally_inr_preserves_frame[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after y fin_st.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    type_stmts env_body NoneT body = SOME env_after /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
    accounts_well_typed (lock_st with scopes := [call_env]).accounts /\
    functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> strip_tac >>
  drule intcall_finally_try_handle_inr_body_cleanup_cases >>
  strip_tac
  >- (
    first_x_assum (qspecl_then [`env_body`, `NoneT`, `env_after`,
                                 `lock_st with scopes := [call_env]`,
                                 `INL ()`, `st_bdy`] mp_tac) >>
    simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
    strip_tac >>
    drule type_stmts_env_preserved_static >> strip_tac >>
    qspecl_then [`env`, `env_after`, `cx`, `env_body.current_src`, `fn`,
                  `args_st`, `st_bdy`, `INR y`, `fin_st`, `nr`,
                  `fm = View \/ fm = Pure`] irule
      intcall_cleanup_after_body_preserves_caller_frame >>
    qexistsl [`args_st`, `env_after`, `env_body`, `fm`, `fn`, `nr`,
              `st_bdy`, `y`] >>
    gvs[]) >>
  first_x_assum (qspecl_then [`env_body`, `NoneT`, `env_after`,
                               `lock_st with scopes := [call_env]`,
                               `INR body_exn`, `st_bdy`] mp_tac) >>
  simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
  strip_tac >> gvs[] >>
  qspecl_then [`env`, `env_exn`, `cx`, `env_body.current_src`, `fn`,
                `args_st`, `st_bdy`, `cleanup_res`, `fin_st`, `nr`,
                `fm = View \/ fm = Pure`] irule
    intcall_cleanup_after_body_preserves_caller_frame >>
  qexistsl [`args_st`, `cleanup_res`, `env_body`, `env_exn`, `fm`, `fn`,
            `nr`, `st_bdy`] >>
  gvs[env_extends_def]
QED

Theorem intcall_default_finally_inr_preserves_frame_from_caller_ctx[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after y fin_st.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    type_stmts env_body NoneT body = SOME env_after /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    context_well_typed cx /\
    accounts_well_typed lock_st.accounts /\
    functions_well_typed cx /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                `y`, `fin_st`] mp_tac
    intcall_default_finally_inr_preserves_frame >>
  impl_tac >-
    (simp[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant] >>
     rpt strip_tac >>
     qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
       (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
     (impl_tac >-
       (simp[context_well_typed_stk_irrelevant,
             functions_well_typed_stk_irrelevant] >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[]) >>
  simp[]
QED

Theorem intcall_default_success_post_push_outer_inr_frame[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after y fin_st.
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) /\
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    type_stmts env_body NoneT body = SOME env_after /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    context_well_typed cx /\
    accounts_well_typed lock_st.accounts /\
    functions_well_typed cx /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                `y`, `fin_st`] mp_tac
    intcall_default_finally_inr_preserves_frame_from_caller_ctx >>
  impl_tac >-
    (simp[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant] >>
     rpt strip_tac >>
     qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
       (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
     (impl_tac >-
       rw[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant]) >>
     simp[]) >>
  simp[]
QED

Theorem intcall_default_success_post_push_outer_inr_frame_live[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after y fin_st.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    type_stmts env_body NoneT body = SOME env_after /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    context_well_typed cx /\
    accounts_well_typed lock_st.accounts /\
    functions_well_typed cx /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                `y`, `fin_st`] mp_tac
    intcall_default_success_post_push_outer_inr_frame >>
  impl_tac >-
    (simp[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant] >>
     rpt strip_tac >>
     qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
       (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
     simp[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant]) >>
  simp[]
QED

Theorem intcall_default_success_post_push_outer_inr_frame_apply[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after y fin_st.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) ==>
    type_stmts env_body NoneT body = SOME env_after ==>
    env_consistent env cx args_st ==>
    state_well_typed args_st ==>
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) ==>
    state_well_typed (lock_st with scopes := [call_env]) ==>
    context_well_typed cx ==>
    accounts_well_typed lock_st.accounts ==>
    functions_well_typed cx ==>
    env_body.type_defs = get_tenv cx ==>
    env_body.bare_globals = env.bare_globals ==>
    env_body.bare_global_assignable = env.bare_global_assignable ==>
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> ntac 14 strip_tac >>
  qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                `y`, `fin_st`] mp_tac
    intcall_default_success_post_push_outer_inr_frame_live >>
  impl_tac >-
    (simp[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant] >>
     rpt strip_tac >>
     qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
       (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
     simp[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant]) >>
  simp[]
QED

Theorem intcall_default_success_post_push_outer_inr_frame_ret[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after ret y fin_st.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) ==>
    type_stmts env_body ret body = SOME env_after ==>
    (ret = NoneT \/ stmts_no_fallthrough body) ==>
    env_consistent env cx args_st ==>
    state_well_typed args_st ==>
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) ==>
    state_well_typed (lock_st with scopes := [call_env]) ==>
    context_well_typed cx ==>
    accounts_well_typed lock_st.accounts ==>
    functions_well_typed cx ==>
    env_body.type_defs = get_tenv cx ==>
    env_body.bare_globals = env.bare_globals ==>
    env_body.bare_global_assignable = env.bare_global_assignable ==>
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> ntac 14 strip_tac >>
  gvs[]
  >- (
    qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                  `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                  `y`, `fin_st`] mp_tac
      intcall_default_success_post_push_outer_inr_frame_apply >>
    impl_tac >- first_assum ACCEPT_TAC >>
    rpt (impl_tac >- (first_assum ACCEPT_TAC ORELSE
                      simp[context_well_typed_stk_irrelevant,
                           functions_well_typed_stk_irrelevant])) >>
    simp[]) >>
  strip_tac >>
  drule intcall_finally_try_handle_inr_body_cleanup_cases >>
  strip_tac
  >- (
    drule (cj 2 no_fallthrough_eval_no_success) >>
    disch_then (qspecl_then [`cx with stk updated_by CONS (env_body.current_src,fn)`,
                             `lock_st with scopes := [call_env]`, `st_bdy`] mp_tac) >>
    simp[]) >>
  qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
    (qspecl_then [`env_body`, `ret`, `env_after`,
                  `lock_st with scopes := [call_env]`,
                  `INR body_exn`, `st_bdy`] mp_tac) >>
  simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
  strip_tac >> gvs[] >>
  qspecl_then [`env`, `env_exn`, `cx`, `env_body.current_src`, `fn`,
                `args_st`, `st_bdy`, `cleanup_res`, `fin_st`, `nr`,
                `fm = View \/ fm = Pure`] irule
    intcall_cleanup_after_body_preserves_caller_frame >>
  qexistsl [`args_st`, `cleanup_res`, `env_body`, `env_exn`, `fm`, `fn`,
            `nr`, `st_bdy`] >>
  gvs[env_extends_def]
QED

Theorem intcall_post_push_tail_no_type_error[local]:
  !cxf body pushed_st prev nr is_view cx rtv ret env_body env_after res st'.
    evaluate_type env_body.type_defs ret = SOME rtv /\
    type_stmts env_body ret body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    stmts_no_control_escape body /\
    (!res_body st_body.
       eval_stmts cxf body pushed_st = (res_body,st_body) ==>
       no_type_error_result res_body /\
       (case res_body of
        | INL _ => T
        | INR exn => return_exception_typed env_body ret exn)) /\
    (do
       rv <- finally
         (try (do eval_stmts cxf body; return NoneV od) handle_function)
         (do pop_function prev;
             if nr /\ ~is_view then
               case cx.nonreentrant_slot of
               | NONE => return ()
               | SOME slot => release_nonreentrant_lock cx.txn.target slot
             else return ()
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) pushed_st = (res,st') ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  gvs[bind_apply] >>
  Cases_on
    `finally (try (do eval_stmts cxf body'; return NoneV od) handle_function)
       (do pop_function prev;
           if nr /\ ~is_view then
             case cx.nonreentrant_slot of
             | NONE => return ()
             | SOME slot => release_nonreentrant_lock cx.txn.target slot
           else return ()
        od) pushed_st` >>
  rename1 `_ = (fin_res,fin_st)` >>
  Cases_on `fin_res` >> gvs[]
  >- (
    rename1 `finally _ _ pushed_st = (INL rv,st_final)` >>
    `!v st_bdy. eval_stmts cxf body' pushed_st = (INR (ReturnException v),st_bdy) ==>
                value_has_type NoneTV v` by (
      rpt strip_tac >>
      qpat_x_assum `!res_body st_body. eval_stmts cxf body' pushed_st = (res_body,st_body) ==> _`
        (qspecl_then [`INR (ReturnException v)`, `st_bdy`] mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (fn th => assume_tac (CONJUNCT2 th)) >>
      gvs[return_exception_typed_def, value_runtime_typed_def]) >>
    drule intcall_finally_try_handle_success_rv >>
    strip_tac >>
    `value_has_type NoneTV rv` by gvs[] >>
    Cases_on `lift_option_type (safe_cast NoneTV rv) "IntCall cast ret" st_final` >>
    rename1 `_ = (cast_res,cast_st)` >>
    `no_type_error_result cast_res` by
      metis_tac[lift_safe_cast_value_has_type_no_type_error] >>
    Cases_on `cast_res` >> gvs[return_def, no_type_error_result_def]) >>
  gvs[finally_def, ignore_bind_def, bind_def, return_def, raise_def,
      prod_CASE_rator, sum_CASE_rator] >>
  gvs[AllCaseEqs(), no_type_error_result_def] >>
  `!exn st'. eval_stmts cxf body' pushed_st = (INR exn,st') ==>
      exn <> BreakException /\ exn <> ContinueException` by
    metis_tac[stmts_no_control_escape_eval_stmts_no_loop_control] >>
  Cases_on `eval_stmts cxf body' pushed_st` >>
  Cases_on `q` >>
  TRY (drule (cj 2 no_fallthrough_eval_no_success) >>
       disch_then (qspecl_then [`cxf`, `pushed_st`, `r`] mp_tac) >>
       simp[] >> NO_TAC) >>
  TRY (rename1 `eval_stmts cxf body' pushed_st = (INR y,_)` >>
       Cases_on `y`) >>
  gvs[try_def, handle_function_def, pop_function_def, set_scopes_def,
      release_nonreentrant_lock_def, get_transient_storage_def, update_transient_def,
      bind_def, return_def, raise_def, no_type_error_result_def, AllCaseEqs()] >>
  Cases_on `nr /\ ~is_view` >>
  gvs[release_nonreentrant_lock_def, get_transient_storage_def, update_transient_def,
      bind_def, return_def, raise_def, no_type_error_result_def, AllCaseEqs()] >>
  Cases_on `cx.nonreentrant_slot` >>
  gvs[release_nonreentrant_lock_def, get_transient_storage_def, update_transient_def,
      bind_def, return_def, raise_def, no_type_error_result_def, AllCaseEqs()] >>
  `value_has_type rtv v` by
    gvs[return_exception_typed_def, value_runtime_typed_def] >>
  `safe_cast rtv v = SOME v` by
    (irule safe_cast_well_typed >> simp[]) >>
  gvs[lift_option_type_def, return_def, raise_def, no_type_error_result_def]
QED

Theorem intcall_pushed_body_tail_no_type_error_from_body_ih[local]:
  (!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body0 = SOME env2 /\
      env_consistent env1 cxf st0 /\ state_well_typed st0 /\
      context_well_typed cxf /\ accounts_well_typed st0.accounts /\
      functions_well_typed cxf /\ eval_stmts cxf body0 st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
      no_type_error_result res0 /\
      case res0 of
        INL v => env_consistent env2 cxf st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\ env_consistent env_exn cxf st0' /\
            return_exception_typed env_exn ret_ty1 exn) /\
  evaluate_type env_body.type_defs ret = SOME rtv /\
  type_stmts env_body ret body0 = SOME env_after /\
  (ret = NoneT \/ stmts_no_fallthrough body0) /\
  stmts_no_control_escape body0 /\
  env_consistent env_body cxf pushed_st /\ state_well_typed pushed_st /\
  context_well_typed cxf /\ accounts_well_typed pushed_st.accounts /\
  functions_well_typed cxf /\
  (do
     rv <- finally
       (try (do eval_stmts cxf body0; return NoneV od) handle_function)
       (do pop_function prev;
           if nr /\ ~is_view then
             case cx.nonreentrant_slot of
             | NONE => return ()
             | SOME slot => release_nonreentrant_lock cx.txn.target slot
           else return ()
        od);
     crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
     return (Value crv)
   od) pushed_st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  irule intcall_post_push_tail_no_type_error >>
  qexistsl_tac [`body0`, `cx`, `cxf`, `env_after`, `env_body`, `is_view`,
                `nr`, `prev`, `pushed_st`, `ret`, `rtv`, `st'`] >>
  simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
    (qspecl_then [`env_body`, `ret`, `env_after`, `pushed_st`,
                  `res_body`, `st_body`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `res_body` >> gvs[] >>
  metis_tac[env_extends_return_exception_typed]
QED


Theorem intcall_current_src_pushed_body_tail_no_type_error[local]:
  !cx env_body fn body ret rtv env_after pushed_st prev nr is_view res st'.
    (!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body = SOME env2 /\
      env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
      state_well_typed st0 /\
      context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      accounts_well_typed st0.accounts /\
      functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
      no_type_error_result res0 /\
      case res0 of
        INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\
            env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
            return_exception_typed env_exn ret_ty1 exn) /\
  evaluate_type env_body.type_defs ret = SOME rtv /\
  type_stmts env_body ret body = SOME env_after /\
  (ret = NoneT \/ stmts_no_fallthrough body) /\
  stmts_no_control_escape body /\
  env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn)) pushed_st /\
  state_well_typed pushed_st /\ context_well_typed cx /\
  accounts_well_typed pushed_st.accounts /\ functions_well_typed cx /\
  (do
     rv <- finally
       (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                return NoneV od) handle_function)
       (do pop_function prev;
           if nr /\ ~is_view then
             case cx.nonreentrant_slot of
             | NONE => return ()
             | SOME slot => release_nonreentrant_lock cx.txn.target slot
           else return ()
        od);
     crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
     return (Value crv)
   od) pushed_st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  irule intcall_pushed_body_tail_no_type_error_from_body_ih >>
  qexistsl_tac [`body'`, `cx`, `cx with stk updated_by CONS (env_body.current_src,fn)`,
                `env_after`, `env_body`, `is_view`, `nr`, `prev`,
                `pushed_st`, `ret`, `rtv`, `st'`] >>
  simp[context_well_typed_stk_irrelevant,
       functions_well_typed_stk_irrelevant] >>
  rpt strip_tac >>
  qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
    (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
  simp[context_well_typed_stk_irrelevant,
       functions_well_typed_stk_irrelevant]
QED

Theorem intcall_current_src_pushed_body_tail_no_type_error_irule[local]:
  !cx env_body fn body ret rtv env_after pushed_st prev nr is_view res st'.
    (!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body = SOME env2 /\
      env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
      state_well_typed st0 /\
      context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      accounts_well_typed st0.accounts /\
      functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
      no_type_error_result res0 /\
      case res0 of
        INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\
            env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
            return_exception_typed env_exn ret_ty1 exn) ==>
    evaluate_type env_body.type_defs ret = SOME rtv ==>
    type_stmts env_body ret body = SOME env_after ==>
    (ret = NoneT \/ stmts_no_fallthrough body) ==>
    stmts_no_control_escape body ==>
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn)) pushed_st ==>
    state_well_typed pushed_st ==>
    context_well_typed cx ==>
    accounts_well_typed pushed_st.accounts ==>
    functions_well_typed cx ==>
    (do
       rv <- finally
         (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                  return NoneV od) handle_function)
         (do pop_function prev;
             if nr /\ ~is_view then
               case cx.nonreentrant_slot of
               | NONE => return ()
               | SOME slot => release_nonreentrant_lock cx.txn.target slot
             else return ()
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) pushed_st = (res,st') ==>
    no_type_error_result res
Proof
  rpt gen_tac >> disch_tac >>
  rpt (disch_tac ORELSE gen_tac) >>
  qspecl_then [`cx`, `env_body`, `fn`, `body'`, `ret`, `rtv`,
                `env_after`, `pushed_st`, `prev`, `nr`, `is_view`,
                `res`, `st'`] mp_tac
    intcall_current_src_pushed_body_tail_no_type_error >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  simp[]
QED
Theorem intcall_default_success_post_push_no_type_error[local]:
  !cx env env_body args_st dflt_st lock_st call_env fn fm nr ret body env_after rtv res st'.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
         INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    evaluate_type env_body.type_defs ret = SOME rtv /\
    type_stmts env_body ret body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    stmts_no_control_escape body /\
    env_consistent env cx args_st /\ state_well_typed dflt_st /\
    context_well_typed cx /\ accounts_well_typed dflt_st.accounts /\
    functions_well_typed cx /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\ env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn)) dflt_st /\
    scope_well_typed call_env /\
    env_scopes_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (dflt_st with scopes := [call_env]) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
     else return ()) dflt_st = (INL (),lock_st) /\
    (do
       rv <- finally
         (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                  return NoneV od) handle_function)
         (do pop_function args_st.scopes;
             if nr /\ ~(fm = View \/ fm = Pure) then
               case cx.nonreentrant_slot of
               | NONE => return ()
               | SOME slot => release_nonreentrant_lock cx.txn.target slot
             else return ()
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) (lock_st with scopes := [call_env]) = (res,st') ==>
    no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  drule_all intcall_live_pushed_body_preconditions >>
  strip_tac >>
  qspecl_then [`cx`, `env_body`, `fn`, `body'`, `ret`, `rtv`,
                `env_after`, `lock_st with scopes := [call_env]`,
                `args_st.scopes`, `nr`, `fm = View \/ fm = Pure`, `res`, `st'`]
    mp_tac intcall_current_src_pushed_body_tail_no_type_error_irule >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- (first_assum ACCEPT_TAC ORELSE simp[])) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  first_x_assum irule >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Theorem intcall_safe_cast_expr_result_typed[local]:
  !env loc src_id_opt fn es extra ret_ty ret_tv rv crv.
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
    type_widens_to env.type_defs ret_ty (expr_type (Call loc (IntCall (src_id_opt,fn)) es extra)) /\
    evaluate_type env.type_defs ret_ty = SOME ret_tv /\
    value_has_type ret_tv rv /\
    safe_cast ret_tv rv = SOME crv ==>
    expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) (Value crv)
Proof
  rpt strip_tac >>
  `value_has_type ret_tv crv` by
    (drule_all safe_cast_preserves_well_typed >> simp[]) >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  simp[expr_result_typed_def, expr_runtime_typed_def,
       value_result_typed_def] >>
  metis_tac[well_typed_expr_not_hashmap_place]
QED

Theorem intcall_default_success_post_push_sound[local]:
  !cx env loc src_id_opt es extra env_body args_st dflt_st lock_st call_env fn fm nr ret body env_after rtv res st'.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       call_evaluation_safe
         (cx with stk updated_by CONS (env_body.current_src,fn))
         (int_calls_stmts body) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
    type_widens_to env.type_defs ret (expr_type (Call loc (IntCall (src_id_opt,fn)) es extra)) /\
    evaluate_type env_body.type_defs ret = SOME rtv /\
    type_stmts env_body ret body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    stmts_no_control_escape body /\
    env_consistent env cx args_st /\ state_well_typed args_st /\
    state_well_typed dflt_st /\
    context_well_typed cx /\ accounts_well_typed dflt_st.accounts /\
    functions_well_typed cx /\
    call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (int_calls_stmts body) /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\ env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn)) dflt_st /\
    scope_well_typed call_env /\
    env_scopes_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (dflt_st with scopes := [call_env]) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
     else return ()) dflt_st = (INL (),lock_st) /\
    (do
       rv <- finally
         (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                  return NoneV od) handle_function)
         (do pop_function args_st.scopes;
             if nr /\ ~(fm = View \/ fm = Pure) then
               case cx.nonreentrant_slot of
               | NONE => return ()
               | SOME slot => release_nonreentrant_lock cx.txn.target slot
             else return ()
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) (lock_st with scopes := [call_env]) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  drule_all intcall_live_pushed_body_preconditions >>
  strip_tac >>
  `no_type_error_result res` by (
    irule intcall_default_success_post_push_no_type_error >>
    qexistsl_tac [`args_st`, `body'`, `call_env`, `cx`, `dflt_st`, `env`,
                  `env_after`, `env_body`, `fm`, `fn`, `lock_st`, `nr`,
                  `ret`, `rtv`, `st'`] >>
    simp[] >>
    rpt strip_tac >>
    qhdtm_assum `bool$!`
      (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[]) >>
  gvs[bind_apply] >>
  Cases_on
    `finally
       (try
          do
            eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body';
            return NoneV
          od handle_function)
       do
         pop_function args_st.scopes;
         if nr /\ ~(fm = View \/ fm = Pure) then
           (case cx.nonreentrant_slot of
              NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot)
         else return ()
       od (lock_st with scopes := [call_env])` >>
  rename1 `_ = (fin_res,fin_st)` >>
  Cases_on `fin_res` >> gvs[]
  >- (
    rename1 `finally _ _ _ = (INL rv,fin_st)` >>
    drule intcall_finally_try_handle_success_cleanup >>
    disch_then strip_assume_tac >>
    gvs[] >~ [`eval_stmts _ _ _ = (INL (),_)`] >- (
      qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
        (qspecl_then [`env_body`, `NoneT`, `env_after`,
                      `lock_st with scopes := [call_env]`, `INL ()`, `st_bdy`] mp_tac) >>
      simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
      strip_tac >>
      qpat_x_assum `do pop_function args_st.scopes; _ od st_bdy = (INL (),fin_st)` mp_tac >>
      qspecl_then [`cx`, `nr`, `fm = View \/ fm = Pure`, `args_st.scopes`,
                    `st_bdy`, `INL ()`, `fin_st`] mp_tac
        intcall_cleanup_after_pop_preserves_frame >>
      simp[] >> strip_tac >> strip_tac >>
      `env_after.type_defs = get_tenv cx /\
       env_after.bare_globals = env.bare_globals /\
       env_after.bare_global_assignable = env.bare_global_assignable /\
       env_after.toplevel_vtypes = env.toplevel_vtypes` by
        (drule type_stmts_env_preserved_static >> simp[]) >>
      `state_well_typed fin_st /\ env_consistent env cx fin_st /\
       accounts_well_typed fin_st.accounts` by (
        qspecl_then [`env`, `env_after`, `cx`, `env_body.current_src`, `fn`,
                      `args_st`, `st_bdy`, `fin_st`] mp_tac
          intcall_cleanup_frame_restore_sound >>
        (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
        strip_tac >> simp[]) >>
      gvs[intcall_safe_cast_NoneTV_NoneV, lift_option_type_def,
          return_def, raise_def, expr_result_typed_def, expr_runtime_typed_def,
          value_result_typed_def, evaluate_type_def]) >>
    qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
      (qspecl_then [`env_body`, `NoneT`, `env_after`,
                    `lock_st with scopes := [call_env]`,
                    `INR (ReturnException rv)`, `st_bdy`] mp_tac) >>
    simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
    strip_tac >>
    qpat_x_assum `do pop_function args_st.scopes; _ od st_bdy = (INL (),fin_st)` mp_tac >>
    qspecl_then [`cx`, `nr`, `fm = View \/ fm = Pure`, `args_st.scopes`,
                  `st_bdy`, `INL ()`, `fin_st`] mp_tac
      intcall_cleanup_after_pop_preserves_frame >>
    simp[] >> strip_tac >> strip_tac >>
    gvs[] >>
    `env_exn.type_defs = get_tenv cx /\
     env_exn.bare_globals = env.bare_globals /\
     env_exn.bare_global_assignable = env.bare_global_assignable /\
     env_exn.toplevel_vtypes = env.toplevel_vtypes` by
      (gvs[env_extends_def]) >>
    `state_well_typed fin_st /\ env_consistent env cx fin_st /\
     accounts_well_typed fin_st.accounts` by (
      qspecl_then [`env`, `env_exn`, `cx`, `env_body.current_src`, `fn`,
                    `args_st`, `st_bdy`, `fin_st`] mp_tac
        intcall_cleanup_frame_restore_sound >>
      (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
      strip_tac >> simp[]) >>
    `rv = NoneV` by
      gvs[return_exception_typed_def, value_runtime_typed_def, evaluate_type_def] >>
    gvs[intcall_safe_cast_NoneTV_NoneV, lift_option_type_def,
        return_def, raise_def, expr_result_typed_def, expr_runtime_typed_def,
        value_result_typed_def, evaluate_type_def])
  >- (
    `(!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body' = SOME env2 /\
      env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
      state_well_typed st0 /\
      context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      accounts_well_typed st0.accounts /\
      functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body' st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
      case res0 of
      | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\
            env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
            return_exception_typed env_exn ret_ty1 exn)` by (
      rpt strip_tac >>
      qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
        (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
      simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant]) >>
    `state_well_typed fin_st /\ env_consistent env cx fin_st /\
     accounts_well_typed fin_st.accounts` by
      (qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                    `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                    `NoneT`,
                    `y`, `fin_st`] mp_tac
         intcall_default_success_post_push_outer_inr_frame_ret >>
       impl_tac >- first_assum ACCEPT_TAC >>
       rpt (impl_tac >- (first_assum ACCEPT_TAC ORELSE
                         simp[context_well_typed_stk_irrelevant,
                              functions_well_typed_stk_irrelevant])) >>
       simp[]) >>
    gvs[] ) >>
  all_tac >~ [`finally _ _ _ = (INL _,_)`] >- (
    drule intcall_finally_try_handle_success_cleanup >>
    disch_then strip_assume_tac >> gvs[]
    >- (
      drule (cj 2 no_fallthrough_eval_no_success) >>
      disch_then (qspecl_then [`cx with stk updated_by CONS (env_body.current_src,fn)`,
                               `lock_st with scopes := [call_env]`, `st_bdy`] mp_tac) >>
      simp[]) >>
    qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
      (qspecl_then [`env_body`, `ret`, `env_after`,
                    `lock_st with scopes := [call_env]`,
                    `INR (ReturnException v)`, `st_bdy`] mp_tac) >>
    simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
    strip_tac >>
    qpat_x_assum `do pop_function args_st.scopes; _ od st_bdy = (INL (),fin_st)` mp_tac >>
    qspecl_then [`cx`, `nr`, `fm = View \/ fm = Pure`, `args_st.scopes`,
                  `st_bdy`, `INL ()`, `fin_st`] mp_tac
      intcall_cleanup_after_pop_preserves_frame >>
    simp[] >> strip_tac >> strip_tac >>
    gvs[] >>
    `env_exn.type_defs = get_tenv cx /\
     env_exn.bare_globals = env.bare_globals /\
     env_exn.bare_global_assignable = env.bare_global_assignable /\
     env_exn.toplevel_vtypes = env.toplevel_vtypes` by
      (gvs[env_extends_def]) >>
    `state_well_typed fin_st /\ env_consistent env cx fin_st /\
     accounts_well_typed fin_st.accounts` by (
      qspecl_then [`env`, `env_exn`, `cx`, `env_body.current_src`, `fn`,
                    `args_st`, `st_bdy`, `fin_st`] mp_tac
        intcall_cleanup_frame_restore_sound >>
      (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
      strip_tac >> simp[]) >>
    `value_has_type rtv v` by
      gvs[return_exception_typed_def, value_runtime_typed_def] >>
    `safe_cast rtv v = SOME v` by
      (irule safe_cast_well_typed >> simp[]) >>
    gvs[lift_option_type_def, return_def, raise_def] >>
    `env.type_defs = get_tenv cx` by
      gvs[env_consistent_def, env_context_consistent_def] >>
    qspecl_then [`env`, `loc`, `src_id_opt`, `fn`, `es`, `extra`, `ret`, `rtv`,
                  `v`, `v`] mp_tac intcall_safe_cast_expr_result_typed >>
    simp[]) >>
  all_tac >~ [`finally _ _ _ = (INR _,_)`] >- (
    `(!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body' = SOME env2 /\
      env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
      state_well_typed st0 /\
      context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      accounts_well_typed st0.accounts /\
      functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body' st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
      case res0 of
      | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\
            env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
            return_exception_typed env_exn ret_ty1 exn)` by (
      rpt strip_tac >>
      qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
        (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
      simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant]) >>
    qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                  `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                  `ret`,
                  `y`, `fin_st`] mp_tac
      intcall_default_success_post_push_outer_inr_frame_ret >>
    impl_tac >- first_assum ACCEPT_TAC >>
    rpt (impl_tac >- (first_assum ACCEPT_TAC ORELSE
                      simp[context_well_typed_stk_irrelevant,
                           functions_well_typed_stk_irrelevant])) >>
    simp[])
QED


Theorem intcall_lock_no_type_error_result[local]:
  !cx nr is_view st res st'.
    (nr ==> cx.nonreentrant_slot <> NONE) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) st = (res,st') ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  Cases_on `nr` >> gvs[return_def, raise_def, no_type_error_result_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  gvs[raise_def, no_type_error_result_def, acquire_nonreentrant_lock_def,
      get_transient_storage_def, update_transient_def, bind_def, ignore_bind_def,
      return_def, raise_def] >>
  Cases_on `lookup_storage (n2w x) (lookup_transient_storage cx.txn.target st.tStorage) = 1w` >>
  gvs[raise_def, return_def, update_transient_def, no_type_error_result_def] >>
  Cases_on `is_view` >>
  gvs[raise_def, return_def, update_transient_def, no_type_error_result_def]
QED

Theorem intcall_lock_attempt_sound_frame[local]:
  !env cx nr is_view dflt_st lock_res lock_st.
    env_consistent env cx dflt_st /\ state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    (nr ==> cx.nonreentrant_slot <> NONE) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) dflt_st = (lock_res,lock_st) ==>
    state_well_typed lock_st /\ accounts_well_typed lock_st.accounts /\
    no_type_error_result lock_res /\
    (case lock_res of INL _ => T | INR _ => env_consistent env cx lock_st)
Proof
  rpt strip_tac >>
  `no_type_error_result lock_res` by
    (irule intcall_lock_no_type_error_result >> goal_assum drule >> simp[]) >>
  Cases_on `lock_res`
  >- (Cases_on `x` >>
      drule intcall_lock_state_preserves_frame >>
      strip_tac >>
      gvs[state_well_typed_def]) >>
  gvs[no_type_error_result_def] >>
  Cases_on `nr` >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  gvs[raise_def, acquire_nonreentrant_lock_def, get_transient_storage_def,
      update_transient_def, bind_def, ignore_bind_def, return_def,
      no_type_error_result_def] >>
  Cases_on `lookup_storage (n2w x) (lookup_transient_storage cx.txn.target dflt_st.tStorage) = 1w` >>
  gvs[raise_def, return_def, update_transient_def, state_well_typed_def] >>
  Cases_on `is_view` >>
  gvs[raise_def, return_def, update_transient_def, state_well_typed_def]
QED



Theorem env_consistent_type_defs_get_tenv[local]:
  !env cx st. env_consistent env cx st ==> env.type_defs = get_tenv cx
Proof
  simp[env_consistent_def, env_context_consistent_def]
QED



Theorem intcall_successful_defaults_lock_success_sound_from_body_ih[local]:
  !cx env loc res st' src_id_opt fn es extra env_body args_st dflt_st lock_st
     call_env fn_name fm nr ret body env_after ret_tv.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn_name)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn_name)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn_name)) /\
       call_evaluation_safe
         (cx with stk updated_by CONS (env_body.current_src,fn_name))
         (int_calls_stmts body) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn_name)) body st0 =
         (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn_name)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn_name)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn_name)) es extra) /\
    type_widens_to env.type_defs ret (expr_type (Call loc (IntCall (src_id_opt,fn_name)) es extra)) /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    type_stmts env_body ret body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    stmts_no_control_escape body /\
    env_consistent env cx args_st /\ state_well_typed args_st /\
    state_well_typed dflt_st /\
    context_well_typed cx /\ accounts_well_typed dflt_st.accounts /\
    functions_well_typed cx /\
    call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn_name))
      (int_calls_stmts body) /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\ env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn_name)) dflt_st /\
    scope_well_typed call_env /\
    env_scopes_consistent env_body cx (dflt_st with scopes := [call_env]) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
     else return ()) dflt_st = (INL (),lock_st) /\
    (do rv <- finally
          (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn_name)) body;
                   return NoneV od) handle_function)
          (do pop_function args_st.scopes;
              if nr /\ ~(fm = View \/ fm = Pure) then
                case cx.nonreentrant_slot of
                | NONE => return ()
                | SOME slot => release_nonreentrant_lock cx.txn.target slot
              else return () od);
        crv <- lift_option_type (safe_cast ret_tv rv) "IntCall cast ret";
        return (Value crv) od) (lock_st with scopes := [call_env]) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn_name)) es extra) tv
    | INR _ => T
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  MATCH_MP_TAC (Q.SPECL [`cx`, `env`, `loc`, `src_id_opt`, `es`, `extra`,
                         `env_body`, `args_st`, `dflt_st`, `lock_st`,
                         `call_env`, `fn_name`, `fm`, `nr`, `ret`, `body'`,
                         `env_after`, `ret_tv`, `res`, `st'`]
    intcall_default_success_post_push_sound) >>
  (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
  (CONJ_TAC THEN1 (qpat_assum `well_typed_expr _ _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `type_widens_to _ ret _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (
    qpat_assum `env_body.type_defs = get_tenv cx` (fn th =>
      simp[th] >> qpat_assum `evaluate_type (get_tenv cx) ret = SOME ret_tv` ACCEPT_TAC))) >>
  (CONJ_TAC THEN1 (qpat_assum `type_stmts _ _ _ = SOME _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
  (CONJ_TAC THEN1 (qpat_assum `stmts_no_control_escape _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_consistent env cx args_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `state_well_typed args_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `state_well_typed dflt_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `context_well_typed cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `accounts_well_typed dflt_st.accounts` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `functions_well_typed cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1
    (qpat_assum `call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn_name))
      (int_calls_stmts body')` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.type_defs = get_tenv cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.fn_sigs = env.fn_sigs` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.bare_globals = env.bare_globals` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.bare_global_assignable = env.bare_global_assignable` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.toplevel_vtypes = env.toplevel_vtypes` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.flag_members = env.flag_members` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_immutables_consistent _ _ _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `scope_well_typed call_env` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (
    qpat_assum `env_scopes_consistent env_body cx (dflt_st with scopes := [call_env])` mp_tac >>
    simp[env_scopes_consistent_stk_irrelevant])) >>
  (CONJ_TAC THEN1 (qpat_assum `(if _ then _ else _) dflt_st = _` mp_tac >> simp[])) >>
  first_assum ACCEPT_TAC
QED


Theorem intcall_post_read_continuation_sound[local]:
  !cx env loc res st' src_id_opt fn es extra env_body args_st dflt_st lock_st
    call_env fm nr ret body env_after ret_tv lock_res.
  (!env1 ret_ty1 env2 st0 res0 st0'.
     type_stmts env1 ret_ty1 body = SOME env2 /\
     env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
     state_well_typed st0 /\
     context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
     accounts_well_typed st0.accounts /\
     functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
     call_evaluation_safe (cx with stk updated_by CONS (env_body.current_src,fn))
       (int_calls_stmts body) /\
     eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 =
       (res0,st0') ==>
     state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
     no_type_error_result res0 /\
     (case res0 of
      | INL _ => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn => ?env_exn. env_extends env1 env_exn /\
          env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
          return_exception_typed env_exn ret_ty1 exn)) /\
  well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
  type_widens_to env.type_defs ret (expr_type (Call loc (IntCall (src_id_opt,fn)) es extra)) /\
  evaluate_type (get_tenv cx) ret = SOME ret_tv /\
  type_stmts env_body ret body = SOME env_after /\
  (ret = NoneT \/ stmts_no_fallthrough body) /\ stmts_no_control_escape body /\
  env_consistent env cx args_st /\ state_well_typed args_st /\
  env_consistent env cx dflt_st /\ state_well_typed dflt_st /\
  context_well_typed cx /\ accounts_well_typed dflt_st.accounts /\ functions_well_typed cx /\
  call_evaluation_safe (cx with stk updated_by CONS (env_body.current_src,fn))
    (int_calls_stmts body) /\
  env_body.type_defs = get_tenv cx /\ env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\ env_body.flag_members = env.flag_members /\
  env_immutables_consistent env_body
    (cx with stk updated_by CONS (env_body.current_src,fn)) dflt_st /\
  scope_well_typed call_env /\
  env_scopes_consistent env_body cx (dflt_st with scopes := [call_env]) /\
  (nr ==> cx.nonreentrant_slot <> NONE) /\
  (if nr then case cx.nonreentrant_slot of
     NONE => raise (Error (TypeError "nonreentrant slot missing"))
   | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
   else return ()) dflt_st = (lock_res,lock_st) /\
  (case lock_res of
   | INL _ =>
       (do rv <- finally
             (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                      return NoneV od) handle_function)
             (do pop_function args_st.scopes;
                 if nr /\ ~(fm = View \/ fm = Pure) then
                   case cx.nonreentrant_slot of NONE => return ()
                   | SOME slot => release_nonreentrant_lock cx.txn.target slot
                 else return () od);
           crv <- lift_option_type (safe_cast ret_tv rv) "IntCall cast ret";
           return (Value crv) od) (lock_st with scopes := [call_env])
   | INR exn => (INR exn,lock_st)) = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  (case res of INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
             | INR _ => T)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  Cases_on `lock_res`
  >- (Cases_on `x` >>
      qpat_x_assum `(case INL _ of INL _ => _ | INR _ => _) = _`
        (assume_tac o REWRITE_RULE [sum_case_def]) >>
      drule_all intcall_successful_defaults_lock_success_sound_from_body_ih >> simp[]) >>
  drule_all intcall_lock_attempt_sound_frame >> strip_tac >>
  gvs[no_type_error_result_def]
QED


(* ===== Internal call final placement helper ===== *)

Theorem type_place_expr_Call_IntCall_NONE[local]:
  !env ty src_id_opt fn es drv.
    type_place_expr env (Call ty (IntCall (src_id_opt,fn)) es drv) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Call_IntCall]:
  rpt gen_tac >> strip_tac >>
  reverse conj_tac >- (
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `type_place_expr _ (Call _ (IntCall _) _ _) = SOME _` mp_tac >>
    simp[type_place_expr_Call_IntCall_NONE]) >>
  strip_tac >>
  drule intcall_call_evaluation_safe_target_not_mem >> strip_tac >>
  qpat_x_assum `well_typed_expr env (Call _ (IntCall _) _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE (pure_ss ++ boolSimps.UNWIND_ss)
    [lock_if_nr_def, unlock_if_nr_def, is_view_mut_def]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[Once evaluate_def] >>
  simp_tac(srw_ss())[bind_apply, ignore_bind_apply, LET_THM] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (strip_tac >>
    rpt (qpat_x_assum `!a b c. _` kall_tac) >>
    gvs[type_check_def, assert_def]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (strip_tac >>
    rpt (qpat_x_assum `!a b c. _` kall_tac) >>
    `fn_sigs_consistent env.fn_sigs cx` by
      gvs[env_consistent_def, env_context_consistent_def] >>
    qpat_x_assum `fn_sigs_consistent env.fn_sigs cx` mp_tac >>
    simp[fn_sigs_consistent_def] >>
    disch_then (qspecl_then [`src_id_opt`, `fn`, `sig`] mp_tac) >>
    simp[] >> strip_tac >>
    gvs[lift_option_type_def, return_def, raise_def, no_type_error_result_def]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (strip_tac >>
    rpt (qpat_x_assum `!a b c. _` kall_tac) >>
    `fn_sigs_consistent env.fn_sigs cx` by
      gvs[env_consistent_def, env_context_consistent_def] >>
    qpat_x_assum `lift_option_type (get_module_code cx src_id_opt) _ r = (INL x',r)`
      (fn th => assume_tac (MATCH_MP (iffLR lift_option_type_INL_eq) th)) >>
    drule_all fn_sigs_consistent_FLOOKUP >> strip_tac >>
    qpat_x_assum `get_module_code cx src_id_opt = SOME x' /\ _` strip_assume_tac >>
    drule_all intcall_lookup_function_not_INR >> strip_tac >>
    first_x_assum (qspecl_then [`r''`, `r`, `"IntCall lookup_function"`, `y`] mp_tac) >>
    simp[]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (strip_tac >>
    rpt (qpat_x_assum `!a b c. _` kall_tac) >>
    `fn_sigs_consistent env.fn_sigs cx` by
      gvs[env_consistent_def, env_context_consistent_def] >>
    drule_all intcall_args_length_condition >> strip_tac >>
    gvs[type_check_def, assert_def, return_def, raise_def,
        no_type_error_result_def]) >>
  simp_tac(srw_ss())[bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  qmatch_asmsub_rename_tac `eval_expr_results cx es r = (args_res,args_st)` >>
  drule intcall_call_evaluation_safe_args >> strip_tac >>
  qmatch_asmsub_rename_tac `type_check _ "IntCall args length" r = (INL tc_ok,tc_st)` >>
  `type_check
     (LENGTH es <= LENGTH (FST (SND (SND x''))) /\
      LENGTH (FST (SND (SND x''))) - LENGTH es <=
        LENGTH (FST (SND (SND (SND x'')))))
     "IntCall args length" r = (INL tc_ok,tc_st)` by
    (qpat_x_assum `type_check _ "IntCall args length" _ = _` mp_tac >> simp[]) >>
  first_x_assum (drule_all o cj 1) >> strip_tac >>
  reverse (Cases_on `args_res`) >- (
    rpt (qpat_x_assum `!a b c. _` kall_tac) >>
    gvs[no_type_error_result_def] >> strip_tac >> gvs[no_type_error_result_def]) >>
  rename1 `eval_expr_results cx es r = (INL results,args_st)` >>
  RULE_ASSUM_TAC (REWRITE_RULE [sumTheory.sum_case_def]) >>
  qpat_assum `lift_option_type (get_module_code cx src_id_opt) _ _ = _`
    (mp_tac o MATCH_MP (iffLR lift_option_type_INL_eq)) >> strip_tac >>
  qpat_assum `lift_option_type (lookup_callable_function cx.in_deploy fn _) _ _ = _`
    (mp_tac o MATCH_MP (iffLR lift_option_type_INL_eq)) >> strip_tac >>
  PairCases_on `x''` >>
  RULE_ASSUM_TAC (BETA_RULE o SIMP_RULE (pure_ss ++ pairSimps.PAIR_ss) []) >>
  `IS_SOME (FLOOKUP env.fn_sigs (src_id_opt,fn))` by
    (qpat_x_assum `FLOOKUP env.fn_sigs (src_id_opt,fn) = SOME _`
       (fn th => simp[th])) >>
  drule_all callable_body_typing_from_env_consistent >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `env_body` (qx_choose_then `ret_tv` (qx_choose_then `env_after`
      (fn th => map_every assume_tac (CONJUNCTS th)))))) >>
  simp_tac(srw_ss())[get_scopes_def, return_def] >>
  BasicProvers.TOP_CASE_TAC >>
  `get_scopes args_st = (INL args_st.scopes,args_st)` by
    simp[get_scopes_def, return_def] >>
  `set_scopes [FEMPTY] args_st = (INL (),args_st with scopes := [FEMPTY])` by
    simp[set_scopes_def, return_def] >>
  first_x_assum (drule o cj 1) >>
  ntac 6 (disch_then (drule o SIMP_RULE (pure_ss ++ pairSimps.PAIR_ss) [])) >>
  disch_then (mk_asm "default_sound") >>
  drule_all intcall_default_env_side_conditions >>
  disch_then (qspec_then `fn` strip_assume_tac) >>
  drule_all intcall_call_evaluation_safe_needed_defaults >>
  disch_then (qspec_then `LENGTH x''3 - (LENGTH x''2 - LENGTH es)` assume_tac) >>
  `env_consistent (defaults_env env_body)
      (cx with stk updated_by CONS (src_id_opt,fn))
      (args_st with scopes := [FEMPTY])` by
    (irule defaults_env_empty_frame_consistent >> simp[]) >>
  `state_well_typed (args_st with scopes := [FEMPTY])` by
    (qpat_assum `state_well_typed args_st` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[state_well_typed_def, scope_well_typed_def]) >>
  `well_typed_exprs (defaults_env env_body)
      (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3)` by
    (irule well_typed_exprs_DROP >> simp[]) >>
  qmatch_asmsub_rename_tac `finally _ _ args_st = (dflt_res,dflt_st)` >>
  `dflt_st.scopes = args_st.scopes /\ state_well_typed dflt_st /\
   env_consistent env cx dflt_st /\ accounts_well_typed dflt_st.accounts /\
   no_type_error_result dflt_res /\ expr_results_typed (env,cx,dflt_st) es results /\
   (case dflt_res of INL vs => exprs_runtime_typed (defaults_env env_body)
      (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3) vs | INR _ => T)` by
    (irule intcall_defaults_restored_sound >>
     qpat_x_assum `!a b c d e f. _` kall_tac >>
     simp[] >> qexistsl_tac [`fn`, `src_id_opt`] >>
     simp[ignore_bind_def] >>
     rpt gen_tac >> disch_tac >>
     `accounts_well_typed (args_st with scopes := [FEMPTY]).accounts` by simp[] >>
     asm "default_sound" drule_all >> simp[]) >>
  Cases_on `dflt_res` >>
  pure_rewrite_tac [sumTheory.sum_case_def]
  >- (RULE_ASSUM_TAC (BETA_RULE o REWRITE_RULE [sumTheory.sum_case_def]) >>
      rename1 `exprs_runtime_typed _ _ dflt_vs` >>
      BasicProvers.TOP_CASE_TAC >>
      rename1 `read_results cx results dflt_st = (read_res,read_st)` >>
      drule read_results_state >> disch_then SUBST_ALL_TAC >>
      drule_all read_results_typed >> strip_tac >>
      Cases_on `read_res` >> pure_rewrite_tac [sumTheory.sum_case_def]
      >- (RULE_ASSUM_TAC (BETA_RULE o REWRITE_RULE [sumTheory.sum_case_def]) >>
          rename1 `exprs_runtime_typed env es actual_vs` >>
          `fn_sigs_consistent env.fn_sigs cx` by
            (qpat_assum `env_consistent env cx args_st` mp_tac >>
             POP_ASSUM_LIST (K ALL_TAC) >>
             simp[env_consistent_def, env_context_consistent_def]) >>
          `sig.param_types = MAP SND x''2 /\ sig.num_defaults = LENGTH x''3 /\
           sig.ret_ty = x''4` by
            (drule_all fn_sigs_consistent_FLOOKUP >>
             qpat_assum `get_module_code cx src_id_opt = SOME x'` mp_tac >>
             qpat_assum `lookup_callable_function cx.in_deploy fn x' = SOME _` mp_tac >>
             POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
          drule env_consistent_type_defs_get_tenv >> strip_tac >>
          `LENGTH es <= LENGTH x''2 /\ LENGTH x''2 - LENGTH es <= LENGTH x''3` by
            (qpat_assum `type_check _ "IntCall args length" r = _` mp_tac >>
             POP_ASSUM_LIST (K ALL_TAC) >>
             simp[type_check_def, assert_def] >> IF_CASES_TAC >> simp[] >> decide_tac) >>
          `MAP expr_type es = TAKE (LENGTH es) (MAP SND x''2)` by metis_tac[] >>
          `?call_env. bind_arguments (get_tenv cx) x''2 (actual_vs ++ dflt_vs) = SOME call_env /\
             scope_well_typed call_env /\
             env_scopes_consistent env_body cx (dflt_st with scopes := [call_env])` by
            (irule intcall_bind_arguments_from_runtime_typed >>
             qpat_x_assum `!a b c d e f. _` kall_tac >>
             asm_x "default_sound" kall_tac >> simp[] >>
             conj_tac >- metis_tac[] >>
             qexistsl_tac [`x''3`, `env`, `es`] >> simp[]) >>
          BETA_TAC >>
          qpat_assum `bind_arguments _ _ _ = SOME call_env`
            (fn th => simp_tac(srw_ss())[th, lift_option_type_def, return_def]) >>
          BasicProvers.TOP_CASE_TAC >>
          rename1 `(if x''1 then _ else _) dflt_st = (lock_res,lock_st)` >>
          Cases_on `lock_res`
          >- (Cases_on `x` >>
              `lift_option_type (bind_arguments (get_tenv cx) x''2 (actual_vs ++ dflt_vs))
                 "IntCall bind_arguments" dflt_st = (INL call_env,dflt_st)` by
                simp[lift_option_type_def, return_def] >>
              `lift_option_type (evaluate_type (get_tenv cx) x''4) "IntCall eval ret"
                 dflt_st = (INL ret_tv,dflt_st)` by simp[lift_option_type_def, return_def] >>
              `push_function (src_id_opt,fn) call_env cx lock_st =
                (INL (cx with stk updated_by CONS (src_id_opt,fn)),
                 lock_st with scopes := [call_env])` by simp[push_function_def, return_def] >>
              first_x_assum drule >>
              ntac 11 (disch_then (drule o SIMP_RULE (pure_ss ++ pairSimps.PAIR_ss) [])) >>
              disch_then (mk_asm "body_sound") >>
              asm_x "default_sound" kall_tac >>
              `env_immutables_consistent env_body
                 (cx with stk updated_by CONS (src_id_opt,fn)) dflt_st` by
                (irule (cj 2 intcall_env_body_consistency_for_defaults) >>
                 simp[] >> qexists_tac `env` >> simp[]) >>
              drule_all intcall_call_evaluation_safe_body >> strip_tac >>
              suspend "IntCall_semantic_tail") >>
          asm_x "default_sound" kall_tac >>
          qpat_x_assum `!a b c d e f. _` kall_tac >>
          drule_all intcall_lock_attempt_sound_frame >> strip_tac >>
          gvs[no_type_error_result_def] >> strip_tac >>
          gvs[no_type_error_result_def]) >>
      qpat_x_assum `!a b c d e f. _` kall_tac >>
      gvs[no_type_error_result_def] >> strip_tac >> gvs[no_type_error_result_def]) >>
  qpat_x_assum `!a b c d e f. _` kall_tac >>
  gvs[no_type_error_result_def] >> strip_tac >> gvs[no_type_error_result_def]
QED

Resume eval_scc_type_sound_results_mutual[IntCall_semantic_tail]:
  strip_tac >>
  qsuff_tac `state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    (case res of INL pv => expr_result_typed env
      (Call v16 (IntCall (src_id_opt,fn)) es v17) pv | INR _ => T)`
  >- (disch_tac >> Cases_on `res` >>
      gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
          eval_result_typed_def]) >>
  irule intcall_post_read_continuation_sound >>
  simp[] >> conj_tac
  >- (simp[Once well_typed_expr_def] >> metis_tac[]) >>
  qexistsl_tac [`args_st`, `x''5`, `call_env`, `dflt_st`, `env_after`,
    `env_body`, `x''0`, `INL x'' : unit + exception`, `lock_st`, `x''1`,
    `x''4`, `ret_tv`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> asm "body_sound" drule_all >> simp[]) >>
  reverse conj_tac >- (simp[expr_type_def] >> metis_tac[]) >>
  qpat_x_assum `(case INL _ of INL _ => _ | INR _ => _) = _` mp_tac >>
  qpat_x_assum `push_function _ _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  gvs[bind_apply, ignore_bind_apply, return_def, lift_option_type_def]
QED

(* ===== External and special call Resume blocks ===== *)

Resume eval_scc_type_sound_results_mutual[Expr_Call_ExtCall_result]:
  rpt gen_tac >> strip_tac >>
  drule extcall_call_evaluation_safe_args >> strip_tac >>
  rename1 `Call _ (ExtCall _ _ fsig _) _ _` >> PairCases_on `fsig` >>
  qpat_x_assum `well_typed_expr env (Call _ (ExtCall _ _ _ _) _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  `?ret_tv. evaluate_type env.type_defs fsig2 = SOME ret_tv` by
    (qpat_assum `well_formed_type env.type_defs v14`
       (mp_tac o REWRITE_RULE [well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
     simp[]) >>
  `well_typed_exprs env (TAKE 1 es) /\
   well_typed_exprs env (TAKE (LENGTH fsig1) (DROP 1 es)) /\
   well_typed_exprs env (DROP (1 + LENGTH fsig1) es)` by
    metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE 1 es)) /\
   call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH fsig1) (DROP 1 es))) /\
   call_evaluation_safe cx (int_calls_exprs (DROP (1 + LENGTH fsig1) es))` by
    metis_tac[call_evaluation_safe_exprs_TAKE, call_evaluation_safe_exprs_DROP] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_exprs cx (TAKE 1 es) st` >>
  rename1 `eval_exprs cx (TAKE 1 es) st = (target_res,target_st)` >>
  qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
    (case res0 of INL vs => exprs_runtime_typed env0 (TAKE 1 es) vs | INR _ => T)`
    drule_all >> strip_tac >>
  Cases_on `target_res`
  >- (qpat_assum `eval_exprs cx (TAKE 1 es) st = _`
        (fn th => simp_tac(srw_ss())[th, sum_case_def, pair_case_def]) >>
      qpat_x_assum `!s target t nargs. eval_exprs cx (TAKE 1 es) s = (INL target,t) /\ _ ==> _`
        (drule o SIMP_RULE (srw_ss()) []) >> strip_tac >>
      Cases_on `eval_expr_results cx (TAKE (LENGTH fsig1) (DROP 1 es)) target_st` >>
      rename1 `eval_expr_results _ _ target_st = (capture_res,capture_st)` >>
      qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
        (case res0 of INL rs => expr_results_typed _ _ rs | INR _ => T)`
        drule_all >> strip_tac >>
      Cases_on `capture_res`
      >- (qpat_x_assum `!s target t nargs s1 rs t1. _ ==> _`
            (drule o SIMP_RULE (srw_ss()) []) >>
          disch_then drule >> strip_tac >>
          qpat_assum `eval_expr_results _ _ target_st = _`
            (fn th => simp_tac(srw_ss())[th, LET_THM, bind_apply]) >>
          Cases_on `eval_exprs cx (DROP (1 + LENGTH fsig1) es) capture_st` >>
          rename1 `eval_exprs _ _ capture_st = (kw_res,kw_st)` >>
          qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
            (case res0 of INL vs => exprs_runtime_typed env0 (DROP _ es) vs | INR _ => T)`
            drule_all >> strip_tac >>
          qpat_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (DROP _ es) /\ _ ==> typed_scope_transition st0 st0'`
            drule_all >> strip_tac >>
          drule (cj 6 eval_metadata_frame_mutual) >> strip_tac >>
          rule_assum_tac (BETA_RULE o REWRITE_RULE [sum_case_def]) >>
          Cases_on `kw_res`
          >- (qpat_assum `eval_exprs _ _ capture_st = _`
                (fn th => simp_tac(srw_ss())[th, bind_apply]) >>
              Cases_on `read_results cx x' kw_st` >>
              rename1 `read_results _ _ kw_st = (read_res,read_st)` >>
              drule_all delayed_read_results_sound >> strip_tac >>
              rpt (qpat_x_assum `!env0 st0 res0 st0'. _` kall_tac) >>
              Cases_on `read_res` >>
              gvs[no_type_error_result_def] >> strip_tac
              >- (`exprs_runtime_typed env es (x ++ x''' ++ x'')` by
                    (irule exprs_runtime_typed_slices >>
                     qexistsl [`1`, `LENGTH fsig1`] >> simp[DROP_DROP]) >>
                  `runtime_consistent env cx kw_st` by simp[runtime_consistent_def] >>
                  `MAP expr_type es =
                     BaseT AddressT :: MAP expr_type (TAKE (LENGTH fsig1) (TL es)) ++
                     MAP (ext_call_kw_type fsig2) opts` by
                    (qspecl_then [`es`, `expr_type`, `LENGTH fsig1`] mp_tac
                       (Q.GENL [`xs`, `f`, `n`] MAP_HD_TAKE_DROP) >> simp[]) >>
                  drule_all eval_ext_call_result_sound >>
                  disch_then (qspec_then `NONE` mp_tac) >>
                  strip_tac >> Cases_on `res` >>
                  gvs[no_type_error_result_def, expr_result_typed_def,
                      expr_runtime_typed_def, value_result_typed_def,
                      eval_result_typed_def, expr_type_def]) >> gvs[]) >>
          rpt (qpat_x_assum `!env0 st0 res0 st0'. _` kall_tac) >>
          gvs[no_type_error_result_def] >> strip_tac >> gvs[]) >>
      rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
      gvs[LET_THM, bind_apply, no_type_error_result_def] >> strip_tac >> gvs[]) >>
  rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
  gvs[no_type_error_result_def] >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Call_Send]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule send_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ (Send _) _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    `LENGTH es = if has_gas then 3 else 2` by
      (qpat_x_assum `MAP expr_type es = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
       rw[]) >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    asm_simp_tac bool_ss [Once evaluate_def, bind_def, ignore_bind_def,
                           type_check_def, assert_def, return_def] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    qpat_x_assum `!s'' x t. type_check _ "Send args" s'' = (INL x,t) ==> _`
      (qspecl_then [`st`, `()`, `st`] mp_tac) >>
    impl_tac >- simp[type_check_def, assert_def, return_def] >>
    disch_then (fn th =>
      qspecl_then [`env`, `st`, `args_res`, `args_st`] mp_tac (cj 1 th)) >>
    simp[] >> strip_tac >>
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (strip_tac >>
        `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
        `MAP expr_type es = [BaseT AddressT; BaseT (UintT 256)] ++
           (if has_gas then [BaseT (UintT 256)] else [])` by fs[] >>
        drule_all eval_send_result_sound >>
        disch_then (qspec_then `NONE` mp_tac) >>
        strip_tac >> Cases_on `res` >>
        gvs[no_type_error_result_def, expr_result_typed_def,
            expr_runtime_typed_def, value_result_typed_def,
            eval_result_typed_def, expr_type_def]) >>
    strip_tac >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
  simp[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Call_RawCallTarget]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule rawcall_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ (RawCallTarget _) _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    qpat_x_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
      (case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T)`
      drule_all >> strip_tac >>
    (Cases_on `args_res`
    >- (gvs[no_type_error_result_def] >>
      rename1 `exprs_runtime_typed env es vs` >>
      mp_tac raw_call_args_runtime_typed_dest >>
      impl_tac >- simp[] >>
      strip_tac >> gvs[] >>
      `LENGTH vs = 3` by (gvs[exprs_runtime_typed_def] >> metis_tac[listTheory.LIST_REL_LENGTH]) >>
      `((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0)` by (
        strip_tac >>
        `EL 2 es = Literal (BaseT (UintT 256)) (IntL 0)` by simp[] >>
        `2 < LENGTH es` by simp[] >>
        drule_all eval_exprs_EL_literal >> strip_tac >>
        gvs[evaluate_literal_def, dest_NumV_def]) >>
      simp[bind_def, return_def] >> strip_tac >>
      `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
      mp_tac (Q.INST [`st` |-> `args_st`, `calldata` |-> `data`]
        eval_raw_call_result_sound) >>
      impl_tac >- simp[] >> strip_tac >>
      Cases_on `res` >>
      gvs[runtime_consistent_def, no_type_error_result_def, expr_type_def] >>
      qpat_x_assum `!e. expr_type e = raw_call_return_type flags ==> _`
        (qspec_then `Literal (raw_call_return_type flags) (IntL 0)` mp_tac) >>
      simp[expr_type_def, expr_result_typed_def, expr_runtime_typed_def,
           value_result_typed_def] >>
      strip_tac >> gvs[eval_result_typed_def]) >>
      gvs[no_type_error_result_def] >> strip_tac >> gvs[]))) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Call_RawCallCalldataTarget]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (
    strip_tac >>
    qpat_x_assum `call_evaluation_safe cx
      (int_calls_expr (Call _ (RawCallCalldataTarget _) es _))` mp_tac >>
    simp[int_calls_expr_def] >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ (RawCallCalldataTarget _) _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
      type_check_def, assert_def, return_def, raise_def, lift_option_type_def] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    qpat_x_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
      (case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T)`
      drule_all >> strip_tac >>
    (Cases_on `args_res`
    >- (gvs[no_type_error_result_def] >>
      drule_all raw_call_calldata_args_runtime_typed_dest >> strip_tac >>
      `((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0)` by (
        strip_tac >>
        `EL 1 es = Literal (BaseT (UintT 256)) (IntL 0)` by simp[] >>
        `1 < LENGTH es` by (
          Cases_on `es` >> gvs[] >>
          rename1 `MAP expr_type rest = [_]` >>
          Cases_on `rest` >> gvs[]) >>
        drule_all eval_exprs_EL_literal >> strip_tac >>
        gvs[evaluate_literal_def, dest_NumV_def]) >>
      gvs[bind_def, return_def] >> strip_tac >>
      `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
      mp_tac (Q.INST [`st` |-> `args_st`, `calldata` |-> `cx.txn.calldata`]
        eval_raw_call_result_sound) >>
      impl_tac >- simp[] >> strip_tac >>
      Cases_on `res` >>
      gvs[runtime_consistent_def, no_type_error_result_def, expr_type_def] >>
      qpat_x_assum `!e. expr_type e = raw_call_return_type flags ==> _`
        (qspec_then `Literal (raw_call_return_type flags) (IntL 0)` mp_tac) >>
      simp[expr_type_def, expr_result_typed_def, expr_runtime_typed_def,
           value_result_typed_def] >>
      strip_tac >> gvs[eval_result_typed_def]) >>
      gvs[no_type_error_result_def] >> strip_tac >> gvs[]))) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Call_RawLog]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule rawlog_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ RawLog _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def, push_log_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    qpat_x_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
      (case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T)`
      drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `exprs_runtime_typed env es vs` >>
      mp_tac raw_log_args_runtime_typed_dest >> simp[] >> strip_tac >> gvs[] >>
      strip_tac >>
      qpat_x_assum `LENGTH (case topics of _ => _) <= 4` $
        mk_asm "topics_bound" >>
      asm "topics_bound" (fn th =>
        fs[th, type_check_def, bind_def, ignore_bind_def, assert_def,
           return_def]) >>
      qspecl_then [`env`, `cx`, `es`, `vs`, `args_st`, `topics`, `data`, `res`, `st'`, `bd`, `bd'`]
        mp_tac raw_log_tail_result_sound_simp >>
      asm "topics_bound" (fn th =>
        simp[th, type_check_def, bind_def, ignore_bind_def, assert_def,
             return_def, runtime_consistent_def]) >>
      strip_tac >> Cases_on `res` >>
      gvs[expr_result_typed_def, expr_runtime_typed_def,
          value_result_typed_def, eval_result_typed_def, expr_type_def]) >>
    strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Call_RawRevert]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule rawrevert_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ RawRevert _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    qpat_x_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
      (case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T)`
      drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `exprs_runtime_typed env es vs` >>
      `LENGTH vs = 1` by
        (gvs[exprs_runtime_typed_def] >>
         metis_tac[listTheory.LIST_REL_LENGTH]) >>
      qspecl_then [`env`, `cx`, `vs`, `args_st`] mp_tac raw_revert_tail_sound >>
      simp[type_check_def, bind_def, ignore_bind_def, assert_def, raise_def,
           return_def, no_type_error_result_def, runtime_consistent_def] >>
      strip_tac >> gvs[]) >>
    strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Call_SelfDestructTarget]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule selfdestruct_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ SelfDestructTarget _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def, get_accounts_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    qpat_x_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
      (case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T)`
      drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `exprs_runtime_typed env es vs` >>
      strip_tac >>
      qspecl_then [`env`, `cx`, `es`, `vs`, `args_st`, `res`, `st'`]
        mp_tac selfdestruct_tail_result_sound_simp >>
      simp[type_check_def, assert_def, runtime_consistent_def] >>
      strip_tac >> Cases_on `res` >>
      gvs[expr_result_typed_def, expr_runtime_typed_def,
          value_result_typed_def, eval_result_typed_def, expr_type_def]) >>
    strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Call_CreateTarget]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule create_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ (CreateTarget _ _ _) _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    Cases_on `kind`
    >~ [`CreateFromBlueprint raw_args`] >- (
      rename1 `CreateFromBlueprint raw_args` >>
      full_simp_tac bool_ss [create_kind_11, create_kind_distinct] >>
      `well_typed_exprs env (TAKE (if has_salt then 4 else 3) es)` by
        metis_tac[well_typed_exprs_TAKE] >>
      `well_typed_exprs env (DROP (if has_salt then 4 else 3) es)` by
        metis_tac[well_typed_exprs_DROP] >>
      `call_evaluation_safe cx
         (int_calls_exprs (TAKE (if has_salt then 4 else 3) es))` by
        metis_tac[call_evaluation_safe_exprs_TAKE] >>
      `call_evaluation_safe cx
         (int_calls_exprs (DROP (if has_salt then 4 else 3) es))` by
        metis_tac[call_evaluation_safe_exprs_DROP] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
      Cases_on `eval_exprs cx (TAKE (if has_salt then 4 else 3) es) st` >>
      rename1 `eval_exprs cx (TAKE (if has_salt then 4 else 3) es) st =
                 (prefix_res,prefix_st)` >>
      qpat_x_assum `!s0 prefix0 t0 s1 code0 t1. _ ==> _`
        (mk_asm "suffix_package") >>
      qpat_x_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
        (case res0 of INL vs => exprs_runtime_typed env0 (TAKE _ es) vs | INR _ => T)`
        drule_all >> strip_tac >>
      Cases_on `prefix_res` >> gvs[no_type_error_result_def]
      >- (
        rename1 `exprs_runtime_typed env
                   (TAKE (if has_salt then 4 else 3) es) prefix` >>
        Cases_on `check_create_blueprint has_salt prefix prefix_st` >>
        rename1 `check_create_blueprint has_salt prefix prefix_st =
                   (gate_res,gate_st)` >>
        `gate_st = prefix_st` by (
          qpat_x_assum `check_create_blueprint has_salt prefix prefix_st = _`
            (mp_tac o Q.AP_TERM `SND`) >> simp[]) >>
        gvs[] >>
        Cases_on `gate_res` >> gvs[]
        >- (
          rename1 `check_create_blueprint has_salt prefix prefix_st =
                     (INL code_size,prefix_st)` >>
          Cases_on `eval_expr_results cx (DROP (if has_salt then 4 else 3) es) prefix_st` >>
          rename1 `eval_expr_results cx (DROP (if has_salt then 4 else 3) es) prefix_st =
                     (suffix_res,suffix_st)` >>
          asm "suffix_package" drule_all >>
          disch_then (fn th => assume_tac (cj 1 th)) >>
          qpat_x_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
            (case res0 of INL vs => expr_results_typed (env0,_,_) (DROP _ es) vs | INR _ => T)`
            drule_all >> strip_tac >>
          Cases_on `suffix_res` >> gvs[no_type_error_result_def]
          >- (
            rename1 `expr_results_typed (env,cx,suffix_st)
                       (DROP (if has_salt then 4 else 3) es) results` >>
            Cases_on `read_results cx results suffix_st` >>
            rename1 `read_results cx results suffix_st = (read_res,read_st)` >>
            drule read_results_state >> strip_tac >> gvs[] >>
            drule_all read_results_typed >> strip_tac >>
            Cases_on `read_res` >> gvs[no_type_error_result_def]
            >- (
            rename1 `exprs_runtime_typed env
                       (DROP (if has_salt then 4 else 3) es) suffix` >>
            `exprs_runtime_typed env es (prefix ++ suffix)` by
              metis_tac[exprs_runtime_typed_APPEND, TAKE_DROP] >>
            `runtime_consistent env cx read_st` by
              simp[runtime_consistent_def] >>
            strip_tac >>
            drule_all create_tail_result_sound_simp >>
            simp[no_type_error_result_def] >>
            strip_tac >> Cases_on `res` >>
            gvs[expr_result_typed_def, expr_runtime_typed_def,
                value_result_typed_def, eval_result_typed_def, expr_type_def]) >>
            strip_tac >> gvs[]) >>
          strip_tac >> gvs[]) >>
        strip_tac >> gvs[] >>
        metis_tac[check_create_blueprint_no_type_error]) >>
      strip_tac >> gvs[]) >>
    rule_assum_tac (REWRITE_RULE [create_kind_11, create_kind_distinct])
    >~ [`RawCreate`] >- (
      qpat_x_assum `!raw_args. RawCreate = CreateFromBlueprint raw_args ==> _` kall_tac >>
      qpat_x_assum `!raw_args s prefix t s1 code t1.
        RawCreate = CreateFromBlueprint raw_args /\ _ ==> _` kall_tac >>
      rpt (qpat_x_assum `RawCreate = _ ==> _` kall_tac) >>
      qpat_x_assum `(_ /\ _)` strip_assume_tac >>
      rpt BasicProvers.VAR_EQ_TAC >>
      `well_typed_exprs env (TAKE 2 es) /\
       well_typed_exprs env (TAKE (LENGTH (DROP 2 es) - (if has_salt then 1 else 0)) (DROP 2 es)) /\
       well_typed_exprs env (DROP (LENGTH (DROP 2 es) - (if has_salt then 1 else 0)) (DROP 2 es))` by
        metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
      `call_evaluation_safe cx (int_calls_exprs (TAKE 2 es)) /\
       call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH (DROP 2 es) - (if has_salt then 1 else 0)) (DROP 2 es))) /\
       call_evaluation_safe cx (int_calls_exprs (DROP (LENGTH (DROP 2 es) - (if has_salt then 1 else 0)) (DROP 2 es)))` by
        metis_tac[call_evaluation_safe_exprs_TAKE, call_evaluation_safe_exprs_DROP] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
      Cases_on `eval_exprs cx (TAKE 2 es) st` >>
      rename1 `eval_exprs cx (TAKE 2 es) st = (prefix_res,prefix_st)` >>
      qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
        (case res0 of INL vs => exprs_runtime_typed env0 (TAKE 2 es) vs | INR _ => T)`
        drule_all >> strip_tac >>
      Cases_on `prefix_res`
      >- (qpat_assum `eval_exprs cx (TAKE 2 es) st = _`
            (fn th => simp_tac(srw_ss())[th, LET_THM, bind_apply]) >>
          qpat_x_assum `!s prefix t ctor_es nargs. _ ==> _`
            (drule o SIMP_RULE (srw_ss()) []) >> strip_tac >>
          rule_assum_tac (REWRITE_RULE [LENGTH_DROP]) >>
          Cases_on `eval_expr_results cx
            (TAKE (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)) prefix_st` >>
          rename1 `eval_expr_results _ _ prefix_st = (capture_res,capture_st)` >>
          qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
            (case res0 of INL rs => expr_results_typed _ _ rs | INR _ => T)`
            drule_all >> strip_tac >>
          Cases_on `capture_res`
          >- (qpat_assum `eval_expr_results _ _ prefix_st = _`
                (fn th => simp_tac(srw_ss())[th, LET_THM, bind_apply]) >>
              rule_assum_tac (BETA_RULE o REWRITE_RULE [sum_case_def]) >>
              Cases_on `read_results cx x' capture_st` >>
              rename1 `read_results cx x' capture_st = (read_res,read_st)` >>
              drule read_results_state >> strip_tac >>
              drule_all read_results_typed >> strip_tac >>
              Cases_on `read_res`
              >- (qpat_x_assum `!s prefix t ctor_es nargs s1 rs t1 s2 args t2. _ ==> _`
                    (drule o SIMP_RULE (srw_ss()) []) >>
                  disch_then drule >> disch_then drule >> strip_tac >>
                  qpat_x_assum `read_st = capture_st` (SUBST_ALL_TAC o SYM) >>
                  qpat_assum `read_results cx _ capture_st = _`
                    (fn th => simp_tac(srw_ss())[th, bind_apply]) >>
                  Cases_on `eval_exprs cx
                    (DROP (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)) read_st` >>
                  rename1 `eval_exprs _ _ read_st = (salt_res,salt_st)` >>
                  qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
                    (case res0 of INL vs => exprs_runtime_typed env0 (DROP _ _) vs | INR _ => T)`
                    drule_all >> strip_tac >>
                  rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
                  Cases_on `salt_res` >> gvs[no_type_error_result_def] >> strip_tac
                  >- (`exprs_runtime_typed env es (x ++ x'' ++ x''')` by
                        (irule exprs_runtime_typed_slices >>
                         qexistsl [`2`, `LENGTH es - 2 - (if has_salt then 1 else 0)`] >>
                         simp[DROP_DROP]) >>
                      `runtime_consistent env cx salt_st` by simp[runtime_consistent_def] >>
                      drule_all create_tail_result_sound_simp >>
                      simp[no_type_error_result_def] >> strip_tac >> Cases_on `res` >>
                      gvs[expr_result_typed_def, expr_runtime_typed_def,
                          value_result_typed_def, eval_result_typed_def, expr_type_def]) >>
                  gvs[]) >>
              rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
              gvs[no_type_error_result_def] >> strip_tac >> gvs[]) >>
          rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
          gvs[no_type_error_result_def] >> strip_tac >> gvs[]) >>
      rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
      gvs[no_type_error_result_def] >> strip_tac >> gvs[]) >>
    (qpat_x_assum `(_ /\ _)` strip_assume_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def, get_accounts_def, update_accounts_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    qpat_x_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
      (case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T)`
      drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (
      `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
      strip_tac >>
      drule_all create_tail_result_sound_simp >>
      simp[no_type_error_result_def] >>
      strip_tac >> Cases_on `res` >>
      gvs[expr_result_typed_def, expr_runtime_typed_def,
          value_result_typed_def, eval_result_typed_def, expr_type_def]) >>
    strip_tac >> gvs[])) >>
  rpt strip_tac >>
  qpat_x_assum `type_place_expr env (Call _ _ _ _) = SOME _` mp_tac >>
  simp[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Results_nil]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr_results _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, return_def, no_type_error_result_def,
       expr_results_typed_def] >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Results_cons]:
  rpt gen_tac >> strip_tac >>
  drule exprs_cons_call_evaluation_safe_head >> strip_tac >>
  drule exprs_cons_call_evaluation_safe_tail >> strip_tac >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr_results _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (head_res,head_st)` >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  reverse (Cases_on `head_res`) >-
    (strip_tac >> gvs[no_type_error_result_def]) >>
  rename1 `eval_expr cx e st = (INL pv,head_st)` >>
  `live_memory_result head_st pv` by
    (qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
       (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     disch_then (qspec_then `env` mp_tac) >> simp[]) >>
  qpat_x_assum `!s pv t. eval_expr _ _ _ = (INL _,_) ==> _`
    drule_all >> strip_tac >>
  Cases_on `eval_expr_results cx es head_st` >>
  rename1 `eval_expr_results cx es head_st = (tail_res,tail_st)` >>
  qpat_x_assum `!env st res st'. _ ==> _ /\ _ /\ _ /\ _ /\ _`
    drule_all >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    drule_all >> strip_tac >>
  reverse (Cases_on `tail_res`)
  >- (rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
      gvs[no_type_error_result_def] >> strip_tac >> gvs[]) >>
  rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
  simp_tac(srw_ss())[] >> strip_tac >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame head_st tail_st` by
    (drule eval_expr_results_immutable_metadata_frame >> simp[]) >>
  rule_assum_tac (BETA_RULE o REWRITE_RULE [sum_case_def]) >>
  `eval_result_typed (env,cx,tail_st) pv (Type (expr_type e))` by
    (irule eval_result_typed_transport >> goal_assum drule_all) >>
  `live_memory_result tail_st pv` by metis_tac[live_result_transport] >>
  gvs[expr_results_typed_def, no_type_error_result_def]
QED

Resume eval_scc_type_sound_results_mutual[Exprs_nil]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >>
  gvs[no_type_error_result_def, exprs_runtime_typed_def]
QED

Resume eval_scc_type_sound_results_mutual[Exprs_cons]:
  rpt gen_tac >> strip_tac >>
  drule exprs_cons_call_evaluation_safe_head >> strip_tac >>
  drule exprs_cons_call_evaluation_safe_tail >> strip_tac >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (r1,st1)` >>
  qpat_x_assum `!env0 st0 res0 st0'. _ ==>
    (well_typed_expr env0 e ==> _) /\ _` drule_all >>
  strip_tac >>
  Cases_on `r1`
  >- (
    `live_memory_result st1 x` by (
      qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
        (qspecl_then [`env`,`st`,`INL x`,`st1`] mp_tac) >>
      (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >>
      simp[]) >>
    qpat_x_assum `well_typed_expr env e ==> _` drule >>
    simp_tac(srw_ss())[] >> strip_tac >>
    `runtime_consistent env cx st1` by simp[runtime_consistent_def] >>
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (mr,stm)` >>
    drule_all live_result_read_typed >> strip_tac >> gvs[] >>
    Cases_on `mr`
    >- (
      Cases_on `eval_exprs cx es st1` >>
      rename1 `eval_exprs cx es st1 = (r2,st2)` >>
      qpat_x_assum `!s tv t sr v tr. _ ==> _ /\ _` drule_all >>
      disch_then (strip_assume_tac o cj 1) >>
      qpat_x_assum `!env st res st'. _ ==> _ /\ _ /\ _ /\ _ /\
        (case res of INL vs => exprs_runtime_typed _ _ vs | INR _ => T)`
        drule_all >> strip_tac >>
      Cases_on `r2` >> gvs[no_type_error_result_def]
      >- (strip_tac >>
          gvs[exprs_runtime_typed_def, value_runtime_typed_def] >>
          qexists_tac `tv::tvs` >> simp[]) >>
      strip_tac >> gvs[]) >>
    strip_tac >> gvs[no_type_error_result_def]) >>
  strip_tac >> gvs[no_type_error_result_def]
QED

(* ABI primitives only change representation arenas, never source scopes. *)
val abi_scope_frames = let
  val rule = Q.INST [`R` |-> `\s t. t.scopes = s.scopes`]
    state_rel_frame_abi_primitives
  val guard = prove (fst (dest_imp (concl rule)), simp[] >> metis_tac[])
 in map (GEN_ALL o SIMP_RULE (srw_ss()) [state_rel_frame_result])
      (CONJUNCTS (MP rule guard)) end;
fun ABI_SCOPE_TAC g = map_every imp_res_tac abi_scope_frames g;

Theorem typed_scope_transition_abi_memory[local,simp]:
  typed_scope_transition st (rt with abi_memory := mem) <=> typed_scope_transition st rt
Proof
  simp[typed_scope_transition_def]
QED

Theorem typed_scope_transition_abi_immutables[local,simp]:
  typed_scope_transition st (rt with abi_immutables := mem) <=> typed_scope_transition st rt
Proof
  simp[typed_scope_transition_def]
QED

(* Each transition root has exactly one semantic key and one suspended goal. *)
val trace_root_labels = [
  "Trace_Target", "Trace_Base_SubscriptTarget", "Trace_Base_AttributeTarget",
  "Trace_Base_TopLevelNameTarget", "Trace_Base_NameTarget",
  "Trace_Exprs_cons", "Trace_Exprs_nil", "Trace_Results_cons", "Trace_Results_nil",
  "Trace_Expr_Call_CreateTarget", "Trace_Expr_Call_SelfDestructTarget",
  "Trace_Expr_Call_RawRevert", "Trace_Expr_Call_RawLog",
  "Trace_Expr_Call_RawCallCalldataTarget", "Trace_Expr_Call_RawCallTarget",
  "Trace_Expr_Call_IntCall", "Trace_Expr_Call_ExtCall", "Trace_Expr_Call_Send",
  "Trace_Expr_TypeBuiltin", "Trace_Expr_Pop", "Trace_Expr_Builtin",
  "Trace_Expr_Attribute", "Trace_Expr_Subscript", "Trace_Expr_StructLit",
  "Trace_Expr_Literal", "Trace_Expr_IfExp", "Trace_Expr_FlagMember",
  "Trace_Expr_TopLevelName", "Trace_Expr_Name",
  "Trace_AbiExprs_nil", "Trace_AbiExprs_cons", "Trace_AbiExpr_Name",
  "Trace_AbiExpr_TopLevelName", "Trace_AbiExpr_IfExp", "Trace_AbiExpr_Subscript",
  "Trace_AbiExpr_Attribute", "Trace_AbiExpr_Pop", "Trace_AbiExpr_FlagMember",
  "Trace_AbiExpr_Literal", "Trace_AbiExpr_StructLit", "Trace_AbiExpr_Builtin",
  "Trace_AbiExpr_TypeBuiltin", "Trace_AbiExpr_Call"];
val _ = let
  val SOME (_,parent) = markerLib.lookup_suspension "eval_scc_type_sound_results_mutual"
  fun check label =
    let val roots = markerLib.extract_suspended_goal [parent] label
        val _ = if length roots = 1 then () else raise Fail ("non-singleton " ^ label)
        val (_,tm) = markerLib.resumption_to_goal roots
        val _ = if trace_root_key tm = label then ()
                else raise Fail ("Wrong transition key: " ^ label)
    in print ("Singleton transition obligation " ^ label ^ "\n") end
  val actual = map #1 (!trace_root_inventory)
  val _ = if List.all (fn key => List.exists (fn x => x = key) actual) trace_root_labels
             andalso List.all (fn key => List.exists (fn x => x = key) trace_root_labels) actual
          then () else raise Fail "Transition inventory mismatch"
in List.app check trace_root_labels end;

Resume eval_scc_type_sound_results_mutual[Trace_Results_nil]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr_results _ [] _ = _` mp_tac >>
  simp[Once evaluate_def, return_def] >> strip_tac >> gvs[] >>
  irule typed_scope_transition_refl
QED

Resume eval_scc_type_sound_results_mutual[Trace_Results_cons]:
  rpt gen_tac >> strip_tac >>
  drule exprs_cons_call_evaluation_safe_head >> strip_tac >>
  drule exprs_cons_call_evaluation_safe_tail >> strip_tac >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr_results _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >>
  strip_tac >>
  FIRST [first_assum ACCEPT_TAC,
    qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
      (drule_at (Pat `eval_expr _ _ _ = _`)) >>
    disch_then (qspec_then `env` mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
    qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    qpat_x_assum `!s pv t. eval_expr _ _ _ = (INL _,_) ==> _`
      (drule_all_then strip_assume_tac) >>
    qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
      (drule_at (Pat `eval_expr_results _ _ _ = _`)) >>
    disch_then (qspec_then `env` mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
    metis_tac[typed_scope_transition_trans]]
QED



(* The semantic root selects its handler before any recursive equation unfolds. *)
fun trace_value_start_tac g = (
  rpt gen_tac >> strip_tac >>
  IF (qpat_assum `type_place_expr _ _ = SOME _` (K all_tac))
    (qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
     simp[NoAsms, Once well_typed_expr_def])
    all_tac) g;

fun trace_result_tac label g = let val suspend = trace_result_tac in
  (case label of
    "Trace_Target" => (rpt gen_tac >> strip_tac >> suspend "TraceTarget")
  | "Trace_Base_NameTarget" => (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, get_scopes_def, type_check_def,
           assert_def, ignore_bind_def, bind_def, return_def, raise_def,
           AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      irule typed_scope_transition_refl)
  | "Trace_Base_TopLevelNameTarget" => (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
      rewrite_tac[Once evaluate_def] >> strip_tac >>
      drule lookup_global_state >> strip_tac >> gvs[] >>
      irule typed_scope_transition_refl)
  | "Trace_Base_AttributeTarget" => (rpt gen_tac >> strip_tac >>
      suspend "TraceBaseAttribute")
  | "Trace_Base_SubscriptTarget" => (rpt gen_tac >> strip_tac >>
      markerLib.suspend "Trace_Base_Subscript_Selection")
  | "Trace_Exprs_nil" => (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_exprs _ [] _ = _` mp_tac >>
      simp[Once evaluate_def, return_def] >> strip_tac >> gvs[] >>
      irule typed_scope_transition_refl)
  | "Trace_Exprs_cons" => (rpt gen_tac >> strip_tac >> suspend "TraceExprsCons")
  | "Trace_Expr_Name" => (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, get_scopes_def, type_check_def,
           assert_def, ignore_bind_def, bind_def, return_def, raise_def,
           AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      irule typed_scope_transition_refl)
  | "Trace_Expr_TopLevelName" => (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      rewrite_tac[Once evaluate_def] >> strip_tac >>
      drule lookup_global_state >> strip_tac >> gvs[] >>
      irule typed_scope_transition_refl)
  | "Trace_Expr_FlagMember" => (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, lift_option_type_def,
           return_def, raise_def, AllCaseEqs()] >> strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >> irule typed_scope_transition_refl)
  | "Trace_Expr_Literal" => (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, return_def] >> strip_tac >> gvs[] >>
      irule typed_scope_transition_refl)
  | "Trace_Expr_Call_ExtCall" => (trace_value_start_tac >>
      markerLib.suspend "Trace_ExtCall_Operands")
  | "Trace_Expr_Call_IntCall" => (trace_value_start_tac >> markerLib.suspend "Trace_IntCall_Operands")
  | "Trace_Expr_Call_CreateTarget" => (trace_value_start_tac >>
      markerLib.suspend "Trace_Create_Operands")
  | "Trace_Expr_Call_Send" => (trace_value_start_tac >> suspend "TraceSend")
  | "Trace_Expr_Call_RawLog" => (trace_value_start_tac >> suspend "TraceRawLog")
  | "Trace_Expr_Call_RawRevert" => (trace_value_start_tac >> suspend "TraceRawRevert")
  | "Trace_Expr_Call_SelfDestructTarget" => (trace_value_start_tac >> suspend "TraceSelfDestruct")
  | "Trace_Expr_Call_RawCallCalldataTarget" => (trace_value_start_tac >> suspend "TraceRawCalldata")
  | "Trace_Expr_Call_RawCallTarget" => (trace_value_start_tac >> suspend "TraceRawCall")
  | "Trace_Expr_TypeBuiltin" => (trace_value_start_tac >> suspend "TraceTypeBuiltin")
  | "Trace_Expr_Builtin" => (trace_value_start_tac >> suspend "TraceBuiltin")
  | "Trace_Expr_StructLit" => (trace_value_start_tac >> suspend "TraceStructLit")
  | "Trace_Expr_Attribute" => (rpt gen_tac >> strip_tac >>
      markerLib.suspend "Trace_Attribute_Selection")
  | "Trace_Expr_Subscript" => (rpt gen_tac >> strip_tac >>
      suspend "TraceExprSubscript")
  | "Trace_Expr_IfExp" => (trace_value_start_tac >> suspend "TraceExprIfExp")
  | "Trace_Expr_Pop" => (rpt gen_tac >> strip_tac >>
      markerLib.suspend "Trace_Pop_Target")
  | "TraceTarget" => (
      qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
      Cases_on `eval_base_place cx bt st` >>
      rename1 `eval_base_place cx bt st = (base_res,mid)` >>
      Cases_on `base_res` >>
      simp[Once evaluate_def, bind_def, get_place_def, AllCaseEqs()] >>
      strip_tac >> gvs[well_typed_target_def] >>
      imp_res_tac vyperPlaceFramesTheory.get_place_state >> rpt BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!env vt st res st'. _ ==> typed_scope_transition _ _` drule_all >>
      simp[])
  | "TraceBaseAttribute" => (
      qpat_x_assum `type_place_target _ (AttributeTarget _ _) = SOME _` mp_tac >>
      rewrite_tac[type_place_target_AttributeTarget] >> strip_tac >>
      markerLib.suspend "Trace_Base_Attribute_Selection")
  | "TraceExprsCons" => (
      qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
      simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
      drule exprs_cons_call_evaluation_safe_head >> strip_tac >>
      drule exprs_cons_call_evaluation_safe_tail >> strip_tac >>
      qpat_x_assum `eval_exprs _ (_::_) _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
      strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
        (drule_at (Pat `eval_expr _ _ _ = _`)) >>
      disch_then (qspec_then `env` mp_tac) >>
      (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
      imp_res_tac read_result_state >> rpt BasicProvers.VAR_EQ_TAC >>
      FIRST [first_assum ACCEPT_TAC,
        qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
          (drule_at (Pat `eval_expr _ _ _ = _`)) >>
        disch_then (qspec_then `env` mp_tac) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
        qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
        (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
        qpat_x_assum `!s0 tv t s1 v t1. eval_expr _ _ _ = _ /\ read_result _ _ _ = _ ==> _`
          (drule_all_then strip_assume_tac) >>
        qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
          (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
        disch_then (qspec_then `env` mp_tac) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
        rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
        metis_tac[typed_scope_transition_trans]])
  | "TraceSend" => (
  drule send_call_evaluation_safe_args >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  `LENGTH es = if has_gas then 3 else 2` by
    (qpat_x_assum `MAP expr_type es = _` (mp_tac o Q.AP_TERM `LENGTH`) >> rw[]) >>
  qpat_x_assum `!s'' x t. type_check _ _ s'' = (INL x,t) ==> _`
    (qspecl_then [`st`, `()`, `st`] mp_tac) >>
  (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, return_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  asm_rewrite_tac[] >>
  imp_res_tac eval_send_preserves_non_accounts >>
  metis_tac[typed_scope_transition_trans, typed_scope_transition_scopes]
)
  | "TraceRawLog" => (
  drule rawlog_call_evaluation_safe_args >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, return_def,
       AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  asm_rewrite_tac[] >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
  rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qpat_x_assum `push_log _ _ = _` mp_tac >>
  simp[NoAsms, push_log_def, return_def] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qmatch_asmsub_rename_tac `eval_exprs cx es st = (INL vs,mid)` >>
  irule typed_scope_transition_trans >> qexists_tac `mid` >>
  conj_tac >- (irule typed_scope_transition_scopes >> simp[]) >>
  first_assum ACCEPT_TAC
)
  | "TraceRawRevert" => (
  drule rawrevert_call_evaluation_safe_args >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, return_def,
       raise_def, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
  rpt BasicProvers.VAR_EQ_TAC >> first_assum ACCEPT_TAC
)
  | "TraceSelfDestruct" => (
  drule selfdestruct_call_evaluation_safe_args >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, return_def,
       raise_def, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
  rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qpat_x_assum `get_accounts _ = _` mp_tac >>
  simp[NoAsms, get_accounts_def, return_def] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac transfer_value_scopes >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  qmatch_asmsub_rename_tac `eval_exprs cx es st = (INL vs,mid)` >>
  irule typed_scope_transition_trans >> qexists_tac `mid` >>
  (conj_tac >- (irule typed_scope_transition_scopes >> first_assum ACCEPT_TAC) >>
   first_assum ACCEPT_TAC)
)
  | "TraceBuiltin" => (
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  `builtin_args_length_ok bt (LENGTH es)` by
    (drule well_typed_builtin_app_length >> simp[]) >>
  Cases_on `bt = Len`
  >- suspend "TraceBuiltinLen" >>
  qpat_x_assum `!s'' x t. _ /\ bt <> Len ==> _`
    (qspecl_then [`st`,`()`,`st`] mp_tac) >>
  (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th =>
    simp_tac (srw_ss()) [Once evaluate_def, bind_def, return_def, raise_def,
      type_check_def, assert_def, th]) >>
  qpat_assum `bt <> Len` (fn th => rewrite_tac[th]) >>
  simp[NoAsms, bind_def, ignore_bind_def, assert_def, return_def, raise_def,
       AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  imp_res_tac lift_sum_state >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qpat_x_assum `get_accounts _ = _` mp_tac >>
  simp[NoAsms, get_accounts_def, return_def] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >> first_assum ACCEPT_TAC
)
  | "TraceBuiltinLen" => (
  `es <> []` by
    (Cases_on `es` >> simp[] >>
     qpat_x_assum `well_typed_builtin_app _ _ _` mp_tac >>
     simp[well_typed_builtin_app_def]) >>
  `call_evaluation_safe cx (int_calls_expr (HD es))` by
    metis_tac[call_evaluation_safe_int_calls_exprs_HD] >>
  `well_typed_expr env (HD es)` by
    (qpat_x_assum `well_typed_exprs env es` mp_tac >>
     qpat_x_assum `es <> []` mp_tac >>
     Cases_on `es` >> simp[Once well_typed_expr_def]) >>
  qpat_x_assum `!s'' x t. _ /\ bt = Len ==> _`
    (qspecl_then [`st`,`()`,`st`] mp_tac) >>
  (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th =>
    simp_tac (srw_ss()) [Once evaluate_def, bind_def, return_def, raise_def,
      type_check_def, assert_def, th]) >>
  qpat_assum `bt = Len` (fn th => rewrite_tac[th]) >>
  simp[NoAsms, bind_def, ignore_bind_def, assert_def, return_def, raise_def,
       AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  imp_res_tac lift_sum_state >> imp_res_tac result_array_length_state >>
  rpt BasicProvers.VAR_EQ_TAC >> first_assum ACCEPT_TAC
)
  | "TraceExprSubscript" => (
      IF (qpat_assum `well_typed_expr _ (Subscript _ _ _)` (K all_tac))
        (qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac)
        (qpat_x_assum `type_place_expr _ (Subscript _ _ _) = SOME _` mp_tac) >>
      simp[NoAsms, Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
      qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
      simp[NoAsms, int_calls_expr_def] >> strip_tac >>
      drule call_evaluation_safe_append_left >> strip_tac >>
      drule call_evaluation_safe_append_right >> strip_tac >>
      Cases_on `eval_expr cx e st` >>
      qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
        (drule_at (Pat `eval_expr _ _ _ = _`)) >>
      disch_then (qspec_then `env` mp_tac) >>
      (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
        disj1_tac >> first_assum ACCEPT_TAC,
        disj2_tac >> goal_assum drule])) >> strip_tac >>
      qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
        (drule_at (Pat `eval_expr _ _ _ = _`)) >>
      disch_then (qspec_then `env` mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
      FIRST [
        qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> _` drule >> strip_tac,
        qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
          (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac] >>
      qpat_x_assum `!env st res st'. _ ==> (case res of INL pv => live_memory_result _ _ | INR _ => T)` kall_tac >>
      (reverse (Cases_on `q`)
      >- (qpat_x_assum `!s'' res t. _` kall_tac >>
          qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
          simp[NoAsms, Once evaluate_def, bind_def] >>
          asm_rewrite_tac[] >> simp[NoAsms, raise_def] >>
          strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `!s'' res t. eval_expr _ _ _ = _ ==> _`
        (qspecl_then [`st`,`x`,`r`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      Cases_on `eval_expr cx e' r` >>
      qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
        (drule_at (Pat `eval_expr _ _ _ = _`)) >>
      disch_then (qspec_then `env` mp_tac) >>
      (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
        disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
      rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
      qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
      simp[NoAsms, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      imp_res_tac read_result_state >> imp_res_tac vyperPlaceFramesTheory.select_result_state >>
      gvs[] >> metis_tac[typed_scope_transition_trans]))
  | "TraceStructLit" => (
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def, GSYM int_calls_exprs_MAP_SND] >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  `well_typed_exprs env (MAP SND kes)` by
    (irule well_typed_named_exprs_MAP_SND_stmt >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!ks. ks = MAP FST kes ==> _`
    (qspec_then `MAP FST kes` mp_tac) >>
  simp_tac bool_ss [] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, LET_THM, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
)
  | "TraceRawCalldata" => (
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, return_def,
       AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qmatch_asmsub_rename_tac `eval_exprs cx es st = (INL vs,mid)` >>
  irule typed_scope_transition_trans >> qexists_tac `mid` >>
  (conj_tac >- (irule typed_scope_transition_scopes >> first_assum ACCEPT_TAC) >>
   first_assum ACCEPT_TAC)
)
  | "TraceRawCall" => (
  drule rawcall_call_evaluation_safe_args >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, return_def,
       AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qmatch_asmsub_rename_tac `eval_exprs cx es st = (INL vs,mid)` >>
  irule typed_scope_transition_trans >> qexists_tac `mid` >>
  (conj_tac >- (irule typed_scope_transition_scopes >> first_assum ACCEPT_TAC) >>
   first_assum ACCEPT_TAC)
)
  | "TraceTypeBuiltin" => (
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  `type_builtin_args_length_ok tb (LENGTH es)` by
    (drule well_typed_type_builtin_args_length >> simp[]) >>
  Cases_on `tb` >> fs[type_check_def, assert_def, mark_abi_captures_def,
                      bind_def, return_def] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, finally_def,
       mark_abi_captures_def, release_abi_captures_def, return_def, raise_def,
       type_check_def, assert_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  ABI_SCOPE_TAC >> imp_res_tac lift_sum_state >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (fn th => FIRST [drule_at (Pat `eval_exprs _ _ _ = _`) th,
                    drule_at (Pat `eval_abi_exprs _ _ _ = _`) th]) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- simp[]) >> simp[typed_scope_transition_def]
)
  | "TraceExprIfExp" => (
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  asm_rewrite_tac[] >>
  qpat_x_assum `!env st res st'. _ ==> (_ ==> _) /\ _` drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _ ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms] >> strip_tac >>
  imp_res_tac read_result_state >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  rpt (qpat_x_assum `!s'' tv t. eval_expr _ _ s'' = (INL tv,t) ==> _` drule >> strip_tac) >>
  qpat_x_assum `switch_BoolV cx _ _ _ _ = _` mp_tac >>
  simp[NoAsms, switch_BoolV_def, bind_def, return_def, raise_def,
       AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac read_result_state >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  simp[NoAsms, COND_RATOR, raise_def] >> rpt IF_CASES_TAC >>
  simp[NoAsms, raise_def] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  imp_res_tac conditional_result_state >> rpt BasicProvers.VAR_EQ_TAC >>
  irule typed_scope_transition_trans >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[]
)
  | _ => raise Fail ("Unknown Trace route: " ^ label)) g end;

Resume eval_scc_type_sound_results_mutual[Trace_Target]:
  RESUME_TAC >> trace_result_tac "Trace_Target"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Base_SubscriptTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Base_SubscriptTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Base_AttributeTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Base_AttributeTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Base_TopLevelNameTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Base_TopLevelNameTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Base_NameTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Base_NameTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Exprs_cons]:
  RESUME_TAC >> trace_result_tac "Trace_Exprs_cons"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Exprs_nil]:
  RESUME_TAC >> trace_result_tac "Trace_Exprs_nil"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_CreateTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_CreateTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_SelfDestructTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_SelfDestructTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_RawRevert]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_RawRevert"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_RawLog]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_RawLog"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_RawCallCalldataTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_RawCallCalldataTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_RawCallTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_RawCallTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_IntCall]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_IntCall"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_ExtCall]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_ExtCall"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_Send]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_Send"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_TypeBuiltin]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_TypeBuiltin"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Pop]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Pop"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Builtin]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Builtin"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Attribute]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Attribute"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Subscript]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Subscript"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_StructLit]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_StructLit"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Literal]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Literal"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_IfExp]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_IfExp"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_FlagMember]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >> strip_tac >>
  drule lookup_flag_mem_state >> strip_tac >> gvs[] >>
  irule typed_scope_transition_refl
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_TopLevelName]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_TopLevelName"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Name]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Name"
QED

Resume eval_scc_type_sound_results_mutual[Trace_IntCall_Operands]:
  RESUME_TAC >>
  ntac 2 (pop_last_assum kall_tac) >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def,
       type_check_def, assert_def,
       return_def, raise_def, get_scopes_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac lift_option_type_state >> rpt BasicProvers.VAR_EQ_TAC >>
  simp[NoAsms, typed_scope_transition_refl] >>
  pop_last_assum mp_tac >>
  simp[NoAsms, type_check_def, assert_def, return_def, raise_def,
       lift_option_type_INL_eq] >>
  imp_res_tac lift_option_type_INL_eq >>
  disch_then drule_all >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
     simp[NoAsms, call_evaluation_safe_def] >> metis_tac[]) >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr_results _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  imp_res_tac read_results_state >>
  imp_res_tac finally_set_scopes >>
  imp_res_tac (SRULE[ignore_bind_def] finally_conditional_lock_scopes) >>
  qpat_assum `typed_scope_transition _ _`
    (mp_then Any irule typed_scope_transition_trans) >>
  irule typed_scope_transition_scopes >>
  asm_rewrite_tac[] >>
  gvs[push_function_def, return_def, AllCaseEqs()] >>
  Cases_on `FST (SND tup)` >> gvs[return_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
  drule acquire_nonreentrant_lock_scopes >> simp[]
QED

(* External calls evaluate every operand before the shared call helper. *)
Resume eval_scc_type_sound_results_mutual[Trace_ExtCall_Operands]:
  RESUME_TAC >>
  drule extcall_call_evaluation_safe_args >> strip_tac >>
  PairCases_on `sig` >>
  qpat_x_assum `well_typed_expr env (Call _ (ExtCall _ _ _ _) _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  `well_typed_exprs env (TAKE 1 es) /\
   well_typed_exprs env (TAKE (LENGTH sig1) (DROP 1 es)) /\
   well_typed_exprs env (DROP (1 + LENGTH sig1) es)` by
    metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE 1 es)) /\
   call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH sig1) (DROP 1 es))) /\
   call_evaluation_safe cx (int_calls_exprs (DROP (1 + LENGTH sig1) es))` by
    metis_tac[call_evaluation_safe_exprs_TAKE, call_evaluation_safe_exprs_DROP] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_exprs cx (TAKE 1 es) st` >>
  rename1 `eval_exprs cx (TAKE 1 es) st = (target_res,target_st)` >>
  qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
    (case res0 of INL vs => exprs_runtime_typed env0 (TAKE 1 es) vs | INR _ => T)`
    drule_all >> strip_tac >>
  qpat_assum `!env0 st0 res0 st0'. _ ==> typed_scope_transition _ _`
    drule_all >> strip_tac >>
  Cases_on `target_res`
  >- (qpat_assum `eval_exprs cx (TAKE 1 es) st = _`
        (fn th => simp_tac(srw_ss())[th, sum_case_def, pair_case_def]) >>
      qpat_x_assum `!s target t nargs. eval_exprs cx (TAKE 1 es) s = (INL target,t) /\ _ ==> _`
        (drule o SIMP_RULE (srw_ss()) []) >> strip_tac >>
      Cases_on `eval_expr_results cx (TAKE (LENGTH sig1) (DROP 1 es)) target_st` >>
      rename1 `eval_expr_results _ _ target_st = (capture_res,capture_st)` >>
      qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
        (case res0 of INL rs => expr_results_typed _ _ rs | INR _ => T)`
        drule_all >> strip_tac >>
      qpat_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (TAKE _ (DROP _ es)) /\ _ ==> typed_scope_transition _ _`
        drule_all >> strip_tac >>
      Cases_on `capture_res`
      >- (qpat_x_assum `!s target t nargs s1 rs t1. _ ==> _`
            (drule o SIMP_RULE (srw_ss()) []) >>
          disch_then drule >> strip_tac >>
          qpat_assum `eval_expr_results _ _ target_st = _`
            (fn th => simp_tac(srw_ss())[th, LET_THM, bind_apply]) >>
          Cases_on `eval_exprs cx (DROP (1 + LENGTH sig1) es) capture_st` >>
          rename1 `eval_exprs _ _ capture_st = (kw_res,kw_st)` >>
          qpat_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (DROP _ es) /\ _ ==> typed_scope_transition _ _`
            drule_all >> strip_tac >>
          rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
          Cases_on `kw_res` >> simp_tac(srw_ss())[sum_case_def, pair_case_def]
          >- (Cases_on `read_results cx x' kw_st` >>
              drule read_results_state >> strip_tac >> gvs[] >>
              rename1 `read_results cx _ kw_st = (read_res,kw_st)` >>
              Cases_on `read_res` >>
              simp_tac(srw_ss())[sum_case_def, pair_case_def] >> strip_tac
              >- (drule eval_ext_call_preserves_non_accounts >> strip_tac >>
                  metis_tac[typed_scope_transition_trans, typed_scope_transition_scopes]) >>
              gvs[] >> metis_tac[typed_scope_transition_trans]) >>
          strip_tac >> gvs[] >> metis_tac[typed_scope_transition_trans]) >>
      rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
      gvs[LET_THM, bind_apply] >> strip_tac >> gvs[] >>
      metis_tac[typed_scope_transition_trans]) >>
  rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
  gvs[] >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Trace_Create_Operands]:
  RESUME_TAC >>
  drule create_call_evaluation_safe_args >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  Cases_on `kind` >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [create_kind_11, create_kind_distinct]) >>
  rpt (first_x_assum (fn th => if is_conj (concl th) then strip_assume_tac th else NO_TAC)) >>
  rpt BasicProvers.VAR_EQ_TAC
  >~ [`CreateFromBlueprint raw_args`] >- suspend "TraceCreateBlueprint"
  >~ [`RawCreate`] >- suspend "TraceRawCreate" >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` drule_all >>
  strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  Cases_on `args_res` >> gvs[] >> strip_tac >> gvs[] >>
  drule vyperCreateFrameTheory.eval_create_preserves_scopes_immutables >> strip_tac >>
  metis_tac[typed_scope_transition_trans, typed_scope_transition_scopes]
QED

Resume eval_scc_type_sound_results_mutual[TraceRawCreate]:
  RESUME_TAC >>
  `well_typed_exprs env (TAKE 2 es) /\
   well_typed_exprs env (TAKE (LENGTH (DROP 2 es) - (if has_salt then 1 else 0)) (DROP 2 es)) /\
   well_typed_exprs env (DROP (LENGTH (DROP 2 es) - (if has_salt then 1 else 0)) (DROP 2 es))` by
    metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE 2 es)) /\
   call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH (DROP 2 es) - (if has_salt then 1 else 0)) (DROP 2 es))) /\
   call_evaluation_safe cx (int_calls_exprs (DROP (LENGTH (DROP 2 es) - (if has_salt then 1 else 0)) (DROP 2 es)))` by
    metis_tac[call_evaluation_safe_exprs_TAKE, call_evaluation_safe_exprs_DROP] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_exprs cx (TAKE 2 es) st` >>
  rename1 `eval_exprs cx (TAKE 2 es) st = (prefix_res,prefix_st)` >>
  qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
    (case res0 of INL vs => exprs_runtime_typed env0 (TAKE 2 es) vs | INR _ => T)`
    drule_all >> strip_tac >>
  qpat_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (TAKE 2 es) /\ _ ==> typed_scope_transition _ _`
    drule_all >> strip_tac >>
  Cases_on `prefix_res`
  >- (qpat_assum `eval_exprs cx (TAKE 2 es) st = _`
        (fn th => simp_tac(srw_ss())[th, LET_THM, bind_apply]) >>
      qpat_x_assum `!s prefix t. eval_exprs cx (TAKE 2 es) s = (INL prefix,t) ==> _`
        drule >> strip_tac >>
      Cases_on `eval_expr_results cx
        (TAKE (LENGTH (DROP 2 es) - (if has_salt then 1 else 0)) (DROP 2 es)) prefix_st` >>
      rename1 `eval_expr_results _ _ prefix_st = (capture_res,capture_st)` >>
      qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
        (case res0 of INL rs => expr_results_typed _ _ rs | INR _ => T)`
        drule_all >> strip_tac >>
      qpat_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (TAKE _ (DROP _ es)) /\ _ ==> typed_scope_transition _ _`
        drule_all >> strip_tac >>
      Cases_on `capture_res`
      >- (qpat_assum `eval_expr_results _ _ prefix_st = _`
            (fn th => simp_tac(srw_ss())[th, LET_THM, bind_apply]) >>
          Cases_on `read_results cx x' capture_st` >>
          rename1 `read_results cx x' capture_st = (read_res,read_st)` >>
          drule read_results_state >> strip_tac >>
          Cases_on `read_res`
          >- (qpat_x_assum `!s prefix t s1 rs t1 s2 args t2. _ ==> _`
                drule >> disch_then drule >> disch_then drule >> strip_tac >>
              qpat_x_assum `read_st = capture_st` (SUBST_ALL_TAC o SYM) >>
              qpat_assum `read_results cx _ capture_st = _`
                (fn th => simp_tac(srw_ss())[th, bind_apply]) >>
              Cases_on `eval_exprs cx
                (DROP (LENGTH (DROP 2 es) - (if has_salt then 1 else 0)) (DROP 2 es)) read_st` >>
              rename1 `eval_exprs _ _ read_st = (salt_res,salt_st)` >>
              qpat_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (DROP _ _) /\ _ ==> typed_scope_transition _ _`
                drule_all >> strip_tac >>
              rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
              Cases_on `salt_res` >> gvs[] >> strip_tac >> gvs[]
              >- (drule eval_create_preserves_scopes_immutables >> strip_tac >>
                  metis_tac[typed_scope_transition_trans, typed_scope_transition_scopes]) >>
              metis_tac[typed_scope_transition_trans]) >>
          rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
          gvs[] >> strip_tac >> gvs[] >> metis_tac[typed_scope_transition_trans]) >>
      rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
      gvs[LET_THM, bind_apply] >> strip_tac >> gvs[] >> metis_tac[typed_scope_transition_trans]) >>
  rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
  gvs[] >> strip_tac >> gvs[]
QED

val live_root_labels = [
  "LiveRootExpr_Name", "LiveRootExpr_TopLevelName", "LiveRootExpr_FlagMember",
  "LiveRootExpr_IfExp", "LiveRootExpr_Literal", "LiveRootExpr_StructLit",
  "LiveRootExpr_Subscript", "LiveRootExpr_Attribute", "LiveRootExpr_Builtin",
  "LiveRootExpr_TypeBuiltin", "LiveRootExpr_Pop",
  "LiveRootExpr_Call_IntCall", "LiveRootExpr_Call_ExtCall", "LiveRootExpr_Call_Send",
  "LiveRootExpr_Call_RawCallTarget", "LiveRootExpr_Call_RawCallCalldataTarget",
  "LiveRootExpr_Call_RawLog", "LiveRootExpr_Call_RawRevert",
  "LiveRootExpr_Call_SelfDestructTarget", "LiveRootExpr_Call_CreateTarget",
  "LiveRootBase_NameTarget", "LiveRootBase_TopLevelNameTarget",
  "LiveRootBase_AttributeTarget", "LiveRootBase_SubscriptTarget", "LiveRootTarget"];
val _ = let
  val SOME (_,parent) = markerLib.lookup_suspension "eval_scc_type_sound_results_mutual"
  val actual = map #1 (!live_root_inventory)
  fun check label =
    if length (markerLib.extract_suspended_goal [parent] label) = 1
    then print ("Singleton live-result obligation: " ^ label ^ "\n")
    else raise Fail ("Non-singleton live-result obligation: " ^ label)
  val _ = if List.all (fn key => List.exists (fn x => x = key) actual) live_root_labels
             andalso List.all (fn key => List.exists (fn x => x = key) live_root_labels) actual
          then () else raise Fail "Live-result inventory mismatch"
 in List.app check live_root_labels end;

Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Name]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, get_scopes_def, type_check_def,
       assert_def, check_def, ignore_bind_def, return_def, raise_def,
       AllCaseEqs()] >> strip_tac >> gvs[IS_SOME_EXISTS] >>
  irule live_memory_result_fresh >> goal_assum (drule_at Any) >>
  simp[memory_eval_path_def, subscripts_type_def, evaluate_subscripts_def]
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_TopLevelName]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac[evaluate_def] >> metis_tac[lookup_global_live]
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_FlagMember]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >> PairCases_on `nsid` >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, lookup_flag_mem_def, lift_option_type_def,
       bind_def, return_def, raise_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `get_module_code cx nsid0` >> gvs[raise_def] >>
  Cases_on `lookup_flag nsid1 x` >> gvs[raise_def] >>
  Cases_on `INDEX_OF mid x'` >>
  gvs[return_def, raise_def, live_memory_result_def]
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_IfExp]:
  RESUME_TAC >> trace_value_start_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  suspend "Live_IfExp_Selected_Conversion"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Literal]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, return_def] >> strip_tac >>
  gvs[live_memory_result_def]
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_StructLit]:
  RESUME_TAC >> trace_value_start_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[live_memory_result_def]
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Subscript]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  suspend "Live_Subscript_Capture_Index_Selection"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Attribute]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  suspend "Live_Attribute_Capture_Selection"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Builtin]:
  RESUME_TAC >> trace_value_start_tac >>
  suspend "Live_Builtin_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_TypeBuiltin]:
  RESUME_TAC >> trace_value_start_tac >>
  suspend "Live_TypeBuiltin_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Pop]:
  RESUME_TAC >> trace_value_start_tac >>
  suspend "Live_Pop_Retained_Owner"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_IntCall]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_IntCall_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_ExtCall]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_ExtCall_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_Send]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_Send_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_RawCallTarget]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_RawCall_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_RawCallCalldataTarget]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_RawCallCalldata_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_RawLog]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_RawLog_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_RawRevert]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_RawRevert_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_SelfDestructTarget]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_SelfDestruct_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_CreateTarget]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_Create_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootBase_NameTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, get_scopes_def, lift_option_type_def,
       ignore_bind_def, type_check_def, assert_def, check_def,
       return_def, raise_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  fs[IS_SOME_EXISTS] >> irule live_memory_result_fresh >>
  goal_assum (drule_at Any) >>
  simp[evaluate_subscripts_def, memory_eval_path_def, subscripts_type_def, subscript_type_def]
QED
Resume eval_scc_type_sound_results_mutual[LiveRootBase_TopLevelNameTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac[evaluate_def] >> metis_tac[lookup_global_live]
QED
Resume eval_scc_type_sound_results_mutual[LiveRootBase_AttributeTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ (AttributeTarget _ _) = SOME _` mp_tac >>
  rewrite_tac[type_place_target_AttributeTarget] >> strip_tac >>
  suspend "Live_Base_Attribute_Selection"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootBase_SubscriptTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = SOME _` mp_tac >>
  rewrite_tac[type_place_target_SubscriptTarget] >> strip_tac >>
  suspend "Live_Base_Subscript_Capture_Index_Selection"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac vyperPlaceFramesTheory.get_place_state >> gvs[] >>
  gvs[well_typed_target_def] >>
  qpat_x_assum `!env vt st res st'. _ ==> (case _ of INL pv => live_memory_result _ _ | INR _ => T)`
    (drule_all_then assume_tac) >>
  Cases_on `res` >> gvs[get_place_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def]
QED

Resume eval_scc_type_sound_results_mutual[TargetPlace]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  gvs[well_typed_target_def] >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac vyperPlaceFramesTheory.get_place_state >> gvs[] >>
  qpat_x_assum `!env vt st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  all_tac >~ [`eval_base_place _ _ _ = (INR _,_)`]
  >- gvs[no_type_error_result_def] >>
  drule eval_base_place_result_shape >> strip_tac >>
  gvs[get_place_def, return_def, raise_def, AllCaseEqs(), is_HashMapRef_def,
      eval_result_typed_def, no_type_error_result_def]
QED



Theorem typed_result_read_sound[local]:
  state_well_typed st /\
  eval_result_typed (env,cx,st) pv (Type ty) /\ live_memory_result st pv /\
  read_result cx pv st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  case res of INL v => value_runtime_typed env ty v | INR _ => T
Proof
  rpt strip_tac >> imp_res_tac read_result_state >> gvs[] >>
  Cases_on `res` >> simp[no_type_error_result_def] >>
  metis_tac[read_live_result_success_type, read_typed_result_error]
QED

Theorem live_place_read_sound:
  state_well_typed st /\ runtime_place_typed cx st p tv /\
  live_memory_result st (PlaceR p) /\ read_place cx p st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  case res of INL v => value_has_type tv v | INR _ => T
Proof
  rpt gen_tac >> strip_tac >> imp_res_tac read_place_preserves_state >> gvs[] >>
  Cases_on `res` >> simp[no_type_error_result_def]
  >- (drule_all read_live_place_success_type >> simp[]) >>
  drule_all read_place_typed_error >> simp[]
QED

Theorem typed_target_place_write_sound[local]:
  env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
  accounts_well_typed st.accounts /\
  eval_result_typed (env,cx,st) (PlaceR p) (Type ty) /\
  writable_place_result cx st (PlaceR p) /\ value_runtime_typed env ty v /\
  write_place cx p v st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  `runtime_consistent env cx st` by simp[runtime_consistent_def] >>
  gvs[value_runtime_typed_def, eval_result_typed_def, writable_place_result_def] >>
  drule_all write_place_sound >> simp[runtime_consistent_def]
QED

Resume eval_scc_type_sound_results_mutual[Assign_Base_sequence]:
  RESUME_TAC >> rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  `?tty. well_typed_atarget env (BaseTarget bt) tty /\
         type_widens_to env.type_defs (expr_type e) tty /\
         assignable_type env.type_defs tty` by
    metis_tac[atarget_accepts_well_typed_atarget] >>
  qpat_x_assum `well_typed_atarget env (BaseTarget bt) tty`
    (assume_tac o REWRITE_RULE [well_typed_atarget_def]) >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_atarget_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (rhs_res,rhs_st)` >>
  qpat_x_assum `!env st res st'. _ ==> _ /\ !vt. _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac) >>
  reverse (Cases_on `rhs_res`)
  >- (POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
      simp[] >> strip_tac >> gvs[no_type_error_result_def] >>
      drule eval_expr_exception_return_typed >> simp[]) >>
  qpat_x_assum `!s'' pv t'. eval_expr _ _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> (case _ of INL pv => live_memory_result _ _ | INR _ => T)`
    (qspec_then `env` mp_tac) >> simp[] >>
  disch_then (drule_all_then strip_assume_tac) >>
  simp_tac (srw_ss()) [] >>
  Cases_on `eval_target_place cx bt rhs_st` >>
  rename1 `eval_target_place cx bt rhs_st = (target_res,target_st)` >>
  qpat_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!env ty st res st'. _ ==> (case _ of INL p => writable_place_result _ _ _ | INR _ => T)`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> typed_scope_transition _ _`
    (drule_all_then strip_assume_tac) >>
  reverse (Cases_on `target_res`)
  >- (simp_tac (srw_ss()) [] >> strip_tac >> gvs[no_type_error_result_def] >>
      irule no_control_exc_return_exception_typed >>
      drule eval_target_place_no_control >> simp[]) >>
  simp_tac (srw_ss()) [] >> suspend "Assign_Base_write"
QED

(* The resolved target preserves the delayed RHS place until its read. *)
Resume eval_scc_type_sound_results_mutual[Assign_Base_write]:
  RESUME_TAC >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  qmatch_assum_rename_tac `eval_expr cx e st = (INL pv,rhs_st)` >>
  qmatch_assum_rename_tac `eval_target_place cx bt rhs_st = (INL p,target_st)` >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame rhs_st target_st` by
    (drule (cj 8 eval_metadata_frame_mutual) >> simp[]) >>
  `eval_result_typed (env,cx,target_st) pv (Type (expr_type e))` by
    (irule eval_result_typed_transport >> qexists_tac `rhs_st` >> simp[]) >>
  `live_memory_result target_st pv` by
    (irule live_result_transport >> qexists_tac `rhs_st` >> simp[]) >>
  Cases_on `read_result cx pv target_st` >>
  rename1 `read_result cx pv target_st = (read_res,read_st)` >>
  drule_all typed_result_read_sound >> strip_tac >> gvs[] >>
  Cases_on `read_res` >> simp[] >> strip_tac >> gvs[no_type_error_result_def]
  >- (qmatch_assum_rename_tac
        `read_result cx pv target_st = (INL v,target_st)` >>
      `value_runtime_typed env tty v` by
        (fs[value_runtime_typed_def] >>
         drule_all type_widens_to_value_has_type >> strip_tac >> gvs[]) >>
      `eval_result_typed (env,cx,target_st) (PlaceR p) (Type tty)` by
        simp[eval_result_typed_def] >>
      drule_all typed_target_place_write_sound >> strip_tac >>
      simp[no_type_error_result_def] >>
      Cases_on `res` >> fs[no_type_error_result_def] >>
      irule no_control_exc_return_exception_typed >>
      drule write_place_no_control >> simp[]) >>
  irule no_control_exc_return_exception_typed >>
  drule read_result_no_control >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[AugAssign_place]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,target_st)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> (case _ of INL p => writable_place_result _ _ _ | INR _ => T)`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> (case _ of INL p => live_memory_result _ _ | INR _ => T)`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
  reverse (Cases_on `target_res`)
  >- (POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
      simp_tac (srw_ss()) [] >> strip_tac >> gvs[no_type_error_result_def] >>
      irule no_control_exc_return_exception_typed >>
      drule eval_target_place_no_control >> simp[]) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `?tv. evaluate_type _ _ = SOME tv /\ _` strip_assume_tac >>
  qmatch_assum_rename_tac `runtime_place_typed cx target_st p ptv` >>
  `place_type_value cx p target_st = (INL ptv,target_st)` by
    (qpat_assum `runtime_place_typed cx target_st p ptv`
      (ACCEPT_TAC o CONJUNCT2 o REWRITE_RULE [runtime_place_typed_def])) >>
  simp_tac (srw_ss()) [] >> Cases_on `read_place cx p target_st` >>
  rename1 `read_place cx p target_st = (read_res,read_st)` >>
  drule_all live_place_read_sound >> strip_tac >>
  qpat_x_assum `read_st = target_st` SUBST_ALL_TAC >>
  (reverse (Cases_on `read_res`) >| [
    POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
      simp_tac (srw_ss()) [] >> strip_tac >> gvs[no_type_error_result_def] >>
      irule no_control_exc_return_exception_typed >>
      drule read_place_no_control >> simp[],
    simp_tac (srw_ss()) [] >> suspend "AugAssign_rhs"])
QED

Resume eval_scc_type_sound_results_mutual[AugAssign_rhs]:
  RESUME_TAC >>
  qmatch_assum_rename_tac `read_place cx p target_st = (INL cur,target_st)` >>
  qpat_x_assum `!s'' p t' s3 cur t2 s4 ptv t3. _`
    (drule_all_then strip_assume_tac) >>
  simp_tac (srw_ss()) [] >>
  Cases_on `eval_expr cx e target_st` >>
  rename1 `eval_expr cx e target_st = (rhs_res,rhs_st)` >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
    (drule_all_then (CONJUNCTS_THEN2 (drule_then strip_assume_tac) kall_tac)) >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (qspec_then `env` mp_tac) >> simp[] >>
  disch_then (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (qspecl_then [`env`, `target_st`, `rhs_res`, `rhs_st`] mp_tac) >> simp[] >> strip_tac >>
  (reverse (Cases_on `rhs_res`) >| [
    simp[] >> strip_tac >> gvs[no_type_error_result_def] >>
      drule eval_expr_exception_return_typed >> simp[],
    simp_tac (srw_ss()) [] >> suspend "AugAssign_write"])
QED

Resume eval_scc_type_sound_results_mutual[AugAssign_write]:
  RESUME_TAC >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  qmatch_assum_rename_tac `eval_expr cx e target_st = (INL rhs,rhs_st)` >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame target_st rhs_st` by
    (drule eval_expr_immutable_metadata_frame >> simp[]) >>
  `runtime_place_typed cx rhs_st p ptv` by
    (irule runtime_place_typed_transport >> qexists_tac `target_st` >> simp[]) >>
  `writable_place_result cx rhs_st (PlaceR p)` by
    (irule writable_place_result_transport >> qexists_tac `target_st` >> simp[]) >>
  `runtime_place_writable cx rhs_st p` by fs[writable_place_result_def] >>
  `runtime_consistent env cx rhs_st` by simp[runtime_consistent_def] >>
  Cases_on `read_result cx rhs rhs_st` >>
  rename1 `read_result cx rhs rhs_st = (loaded,read_st)` >>
  drule_all typed_result_read_sound >> strip_tac >> gvs[] >>
  reverse (Cases_on `loaded`)
  >- (simp[] >> strip_tac >> gvs[no_type_error_result_def] >>
      drule read_result_no_control >> simp[no_control_exc_return_exception_typed]) >>
  simp[] >> strip_tac >> suspend "AugAssign_value_write"
QED

Resume eval_scc_type_sound_results_mutual[AugAssign_value_write]:
  RESUME_TAC >>
  qmatch_assum_rename_tac `read_result cx rhs rhs_st = (INL right,rhs_st)` >>
  fs[value_runtime_typed_def] >>
  qmatch_assum_rename_tac `evaluate_type env.type_defs (expr_type e) = SOME rhs_tv` >>
  `!msg. evaluate_binop
    (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0) ptv bop cur right <>
    INR (TypeError msg)` by
    (irule well_typed_binop_no_type_error >>
     qexistsl_tac [`ptv`,`ty`,`expr_type e`,`env.type_defs`,`ptv`,`rhs_tv`,`ty`] >> simp[]) >>
  qpat_x_assum `_ = (res,st')` mp_tac >>
  simp_tac (srw_ss()) [bind_def, lift_sum_def] >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0) ptv bop cur right` >>
  simp[return_def, raise_def] >> strip_tac >> gvs[no_type_error_result_def]
  >- (qmatch_assum_rename_tac `evaluate_binop _ ptv bop cur right = INL result` >>
      `value_has_type ptv result` by
        (irule well_typed_binop_success_type >>
         qexistsl_tac [`bop`,`ty`,`expr_type e`,`env.type_defs`,`ptv`,`ptv`,`rhs_tv`,`ty`,
           `case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0`,
           `cur`,`right`] >> simp[]) >>
      drule_all write_place_sound >> strip_tac >> gvs[runtime_consistent_def] >>
      Cases_on `res` >> gvs[no_type_error_result_def] >>
      drule write_place_no_control >> simp[no_control_exc_return_exception_typed]) >>
  simp[return_exception_typed_def]
QED

Theorem value_runtime_typed_tuple_components:
  value_runtime_typed env (TupleT tys) v ==>
  ?vs. v = ArrayV (TupleV vs) /\ LIST_REL (value_runtime_typed env) tys vs
Proof
  rw[value_runtime_typed_def] >> drule evaluate_type_TupleT_cases >> strip_tac >>
  gvs[] >> drule value_has_type_TupleTV_dest_stmt >> strip_tac >> gvs[] >>
  simp[LIST_REL_EL_EQN, value_runtime_typed_def] >>
  fs[values_have_types_LIST_REL_stmt, LIST_REL_EL_EQN] >> metis_tac[]
QED

Resume eval_scc_type_sound_results_mutual[TupleStore_BaseTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_atarget _ _ _` mp_tac >>
  simp_tac (srw_ss()) [well_typed_atarget_def] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_atarget _)` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (answer,middle)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> (case _ of INL p => writable_place_result _ _ _ | INR _ => T)`
    (drule_all_then strip_assume_tac) >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  reverse (Cases_on `answer`)
  >- (simp_tac (srw_ss()) [] >> strip_tac >> gvs[no_type_error_result_def]) >>
  simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >>
  qmatch_assum_rename_tac `eval_target_place cx bt st = (INL p,middle)` >>
  `eval_result_typed (env,cx,middle) (PlaceR p) (Type ty)` by
    simp[eval_result_typed_def] >>
  drule_all typed_target_place_write_sound >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[TupleStore_TupleTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  gvs[well_typed_atarget_def, int_calls_atarget_def] >>
  drule value_runtime_typed_tuple_components >> strip_tac >> gvs[] >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[TupleStores_nil_nil]:
  RESUME_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, return_def, no_type_error_result_def]
QED

Resume eval_scc_type_sound_results_mutual[TupleStores_nil_cons]:
  RESUME_TAC >> rpt strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[TupleStores_cons_nil]:
  RESUME_TAC >> rpt strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[TupleStores_cons_cons]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  rename1 `assign_tuple_target_list cx (g::gs) (v::vs) st = (res,st')` >>
  Cases_on `tys`
  >- (qpat_x_assum `LIST_REL _ (g::gs) []` mp_tac >> simp[]) >>
  rename1 `LIST_REL _ (g::gs) (head_ty::tail_tys)` >>
  qpat_x_assum `LIST_REL _ (g::gs) (head_ty::tail_tys)` mp_tac >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_x_assum `LIST_REL _ (head_ty::tail_tys) (v::vs)` mp_tac >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_atargets (g::gs))` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `assign_tuple_target_list _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `assign_tuple_targets cx g v st` >>
  rename1 `assign_tuple_targets cx g v st = (answer,middle)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  reverse (Cases_on `answer`)
  >- (POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
      simp_tac (srw_ss()) [] >> strip_tac >> gvs[]) >>
  qpat_x_assum `!s'' x t. assign_tuple_targets _ _ _ s'' = (INL x,t) ==> _`
    (drule_then strip_assume_tac) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

(* Assignability is an additional proved SCC conclusion. The original typing
   and public compatibility contracts keep their original preconditions. *)
Theorem subscript_vtype_result_step_type[local]:
  subscript_vtype bvt (expr_type e) = SOME out /\
  value_runtime_typed env (expr_type e) key ==>
  target_path_step_type env bvt (ValueSubscript key) out
Proof
  strip_tac >> Cases_on `bvt` >> gvs[subscript_vtype_def]
  >- (Cases_on `t` >> gvs[subscript_vtype_def] >>
      Cases_on `expr_type e` >>
      gvs[is_int_type_def, value_runtime_typed_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `key` >> gvs[value_has_type_def, target_path_step_type_def]) >>
  Cases_on `expr_type e` >>
  gvs[hashmap_key_type_def, value_runtime_typed_def, evaluate_type_def, AllCaseEqs(), LET_THM] >>
  Cases_on `key` >>
  gvs[value_has_type_def, target_path_step_type_def, hashmap_key_type_def,
      value_runtime_typed_def, evaluate_type_def, value_has_type_def]
QED

Resume eval_scc_type_sound_results_mutual[WritableRootBase_NameTarget]:
  RESUME_TAC >> rpt strip_tac >>
  `?ty. vt = Type ty` by gvs[well_typed_expr_def, AllCaseEqs()] >>
  gvs[] >> drule_all NameTarget_sound >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, assert_def, ignore_bind_def,
       get_scopes_def, type_check_def] >> strip_tac >> gvs[] >>
  simp[writable_place_result_def, runtime_place_writable_def,
       mutable_place_path_def] >> metis_tac[]
QED

Resume eval_scc_type_sound_results_mutual[WritableRootBase_TopLevelNameTarget]:
  RESUME_TAC >> rpt strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  rewrite_tac[Once evaluate_def] >> metis_tac[lookup_global_writable]
QED

Resume eval_scc_type_sound_results_mutual[WritableRootBase_AttributeTarget]:
  RESUME_TAC >> rpt gen_tac >>
  rewrite_tac[type_place_target_AttributeTarget] >> strip_tac >>
  gvs[int_calls_expr_def] >>
  Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  first_assum (drule_all_then strip_assume_tac) >>
  qpat_assum `!env vt st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!env vt st res st'. _ ==> (case _ of INL pv => writable_place_result _ _ _ | INR _ => T)`
    (drule_all_then strip_assume_tac) >> gvs[] >>
  irule extend_place_writable >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  qexists_tac `Type ty` >> Cases_on `tgt_ty` >>
  gvs[target_path_step_type_def, attribute_type_def]
QED

Resume eval_scc_type_sound_results_mutual[WritableRootBase_SubscriptTarget]:
  RESUME_TAC >> rpt gen_tac >>
  rewrite_tac[type_place_target_SubscriptTarget] >> strip_tac >>
  qmatch_assum_rename_tac `type_place_target env bt = SOME base_vt` >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_target (SubscriptTarget bt e))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!s pv t. eval_base_place _ _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!env vt st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!env vt st res st'. _ ==> (case _ of INL pv => writable_place_result _ _ _ | INR _ => T)`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> _ /\ !vt. _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (qspec_then `env` mp_tac) >> simp[] >>
  disch_then (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (qspec_then `env` mp_tac) >> simp[] >>
  disch_then (drule_all_then strip_assume_tac) >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  gvs[] >>
  qmatch_assum_rename_tac `eval_base_place cx bt st = (INL base_pv,st1)` >>
  qmatch_assum_rename_tac `eval_expr cx e st1 = (INL idx,st2)` >>
  drule_all typed_result_read_sound >> strip_tac >> gvs[] >>
  qmatch_assum_rename_tac `eval_expr cx e st1 = (INL idx,st2)` >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame st1 st2` by
    (drule eval_expr_immutable_metadata_frame >> simp[]) >>
  `eval_result_typed (env,cx,st2) base_pv base_vt` by
    (irule eval_result_typed_transport >> qexists_tac `st1` >> simp[eval_result_typed_def]) >>
  `writable_place_result cx st2 base_pv` by
    metis_tac[writable_place_result_transport] >>
  drule_all subscript_vtype_result_step_type >> strip_tac >>
  drule_all extend_place_writable >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[WritableRootTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  gvs[well_typed_target_def] >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, get_place_def, return_def,
       raise_def, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env vt st res st'. _ ==> (case _ of INL pv => writable_place_result _ _ _ | INR _ => T)`
    (drule_all_then strip_assume_tac) >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  qmatch_assum_rename_tac `get_place resolved_pv from_st = (INL resolved_place,target_st)` >>
  Cases_on `resolved_pv` >> gvs[get_place_def, return_def, raise_def]
QED

(* Exhaustive coverage audit, including descendant labels. This is diagnostic:
   Finalise below remains the only assembly operation. *)
val _ = let
  val SOME (thy,parent) = markerLib.lookup_suspension "eval_scc_type_sound_results_mutual"
  val seen = ref ([] : string list)
  fun label tm =
    let val (h,args) = strip_comb tm
    in if #Name (dest_thy_const h) = "suspendlabel" then
         SOME (#1 (boolLib.decode_suspend_label (#1 (dest_var (hd args)))))
       else NONE end handle HOL_ERR _ => NONE
  fun walk th = List.app visit (List.mapPartial label (hyp th))
  and visit name = if List.exists (fn x => x = name) (!seen) then () else
    let val _ = seen := name :: !seen
        val candidates = markerLib.lookup_resumption
          {parent_thy=thy,parent_name="eval_scc_type_sound_results_mutual",label=name}
        val proofs = List.filter (fn th => label (concl th) = SOME name) candidates
        val _ = print ("SCC coverage " ^ name ^ ": " ^
          Int.toString (length proofs) ^ " registered bodies\n")
        val _ = if null proofs then
          List.app (fn (_,tm) => print ("MISSING SCC ROOT " ^ name ^ ": " ^
             term_to_string tm ^ "\n"))
            (markerLib.extract_suspended_goal (parent::candidates) name handle HOL_ERR _ => [])
          else ()
    in List.app walk proofs end
in walk parent end;

Resume eval_scc_type_sound_results_mutual[TraceCreateBlueprint]:
  RESUME_TAC >>
  `well_typed_exprs env (TAKE (if has_salt then 4 else 3) es)` by
    metis_tac[well_typed_exprs_TAKE] >>
  `well_typed_exprs env (DROP (if has_salt then 4 else 3) es)` by
    metis_tac[well_typed_exprs_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE (if has_salt then 4 else 3) es))` by
    metis_tac[call_evaluation_safe_exprs_TAKE] >>
  `call_evaluation_safe cx (int_calls_exprs (DROP (if has_salt then 4 else 3) es))` by
    metis_tac[call_evaluation_safe_exprs_DROP] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_exprs cx (TAKE (if has_salt then 4 else 3) es) st` >>
  rename1 `eval_exprs cx (TAKE (if has_salt then 4 else 3) es) st = (prefix_res,prefix_st)` >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` drule_all >>
  strip_tac >>
  qpat_x_assum `!env st res st'. well_typed_exprs _ _ /\ _ ==> _` drule_all >>
  strip_tac >>
  Cases_on `prefix_res` >> gvs[]
  >- (rename1 `eval_exprs cx (TAKE (if has_salt then 4 else 3) es) st =
        (INL prefix,prefix_st)` >>
      Cases_on `check_create_blueprint has_salt prefix prefix_st` >>
      rename1 `check_create_blueprint has_salt prefix prefix_st = (gate_res,gate_st)` >>
      `gate_st = prefix_st` by metis_tac[check_create_blueprint_result_state] >>
      gvs[] >> Cases_on `gate_res` >> gvs[]
      >- suspend "TraceBlueprintSuffix" >>
      strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[TraceBlueprintSuffix]:
  RESUME_TAC >>
  rename1 `check_create_blueprint has_salt prefix prefix_st = (INL code_size,prefix_st)` >>
  qpat_x_assum `!a b c d e f. _ ==> _` drule_all >> strip_tac >>
  Cases_on `eval_expr_results cx (DROP (if has_salt then 4 else 3) es) prefix_st` >>
  rename1 `eval_expr_results cx (DROP (if has_salt then 4 else 3) es) prefix_st =
    (suffix_res,suffix_st)` >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` drule_all >>
  strip_tac >>
  rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
  Cases_on `suffix_res` >> gvs[]
  >- (rename1 `read_results cx results suffix_st` >>
      Cases_on `read_results cx results suffix_st` >>
      drule read_results_state >> strip_tac >> gvs[] >>
      rename1 `read_results cx results suffix_st = (read_res,suffix_st)` >>
      Cases_on `read_res` >> gvs[] >> strip_tac >> gvs[]
      >- (drule eval_create_preserves_scopes_immutables >> strip_tac >>
          metis_tac[typed_scope_transition_trans, typed_scope_transition_scopes]) >>
      metis_tac[typed_scope_transition_trans]) >>
  strip_tac >> gvs[] >> metis_tac[typed_scope_transition_trans]
QED

Resume eval_scc_type_sound_results_mutual[Live_Base_Attribute_Selection]:
  RESUME_TAC >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  gvs[int_calls_expr_def] >>
  qpat_assum `!env vt st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!env vt st res st'. _ ==> (case _ of INL pv => live_memory_result _ _ | INR _ => T)`
    (drule_all_then assume_tac) >>
  Cases_on `res` >> gvs[] >>
  drule_all extend_typed_result_live >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[Live_IntCall_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Trace_Base_Attribute_Selection]:
  RESUME_TAC >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  gvs[int_calls_expr_def] >>
  imp_res_tac vyperPlaceFramesTheory.extend_place_state >> gvs[] >>
  qpat_x_assum `!env vt st res st'. _ ==> typed_scope_transition _ _`
    (drule_all_then assume_tac) >> simp[]
QED

Theorem eval_create_success_value[local]:
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (INL pv,st') ==>
  ?v. pv = Value v
Proof
  Cases_on `dest_create_args kind has_salt vs` >>
  simp[vyperCreateTheory.eval_create_def, bind_apply, ignore_bind_apply,
       lift_option_type_def, get_accounts_def, update_accounts_def,
       get_pending_deletions_def, get_transient_storage_def, check_def, assert_def,
       vyperCreateTheory.create_soft_failure_def, return_def, raise_def] >>
  Cases_on `create_arg_ctor_types kind has_salt arg_tys` >>
  simp[bind_apply, ignore_bind_apply, return_def, raise_def] >>
  Cases_on `build_create_code (get_tenv cx) kind x st.accounts x' blueprint_size` >>
  simp[bind_apply, ignore_bind_apply, return_def, raise_def] >>
  rpt (IF_CASES_TAC >>
    simp[bind_apply, ignore_bind_apply, get_transient_storage_def,
         get_pending_deletions_def, update_accounts_def,
         check_def, assert_def, return_def, raise_def]) >>
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `run_create_evm ca cb cc cd ce cf cg ch` >>
  (Cases_on `run_create_evm ca cb cc cd ce cf cg ch`
   >- gvs[ignore_bind_apply, update_accounts_def, return_def, raise_def]) >>
  rename1 `run_create_evm ca cb cc cd ce cf cg ch = SOME adapter` >>
  PairCases_on `adapter` >>
  Cases_on `adapter0` >>
  gvs[ignore_bind_apply, update_accounts_def, update_transient_def,
      update_pending_deletions_def, append_logs_def, return_def, raise_def]
QED

Resume eval_scc_type_sound_results_mutual[Live_Create_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `kind` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule eval_create_success_value >> strip_tac >> gvs[]
QED

Theorem eval_ext_call_success_value[local]:
  eval_ext_call cx static skip sigt opts vs st = (INL pv,st') ==>
  ?v. pv = Value v
Proof
  PairCases_on `sigt` >> Cases_on `vs` >>
  simp[eval_ext_call_def, bind_apply, ignore_bind_apply,
       lift_option_type_def, type_check_def, check_def, assert_def,
       return_def, raise_def, get_accounts_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `eval_ext_call_effects ca cb cc cd ce cf cg` >>
  Cases_on `eval_ext_call_effects ca cb cc cd ce cf cg` >>
  gvs[bind_apply, ignore_bind_apply, lift_sum_runtime_def,
      return_def, raise_def, get_accounts_def, check_def, assert_def,
      AllCaseEqs()] >>
  Cases_on `if returnData = [] then
    ext_call_kwarg EKDefault opts (DROP (LENGTH sigt1) t) else NONE` >>
  gvs[bind_apply, ignore_bind_apply, return_def, raise_def,
      get_accounts_def, assert_def, AllCaseEqs()] >>
  Cases_on `evaluate_abi_decode_return (get_tenv ca) sigt2 returnData` >>
  gvs[bind_apply, return_def, raise_def]
QED

Resume eval_scc_type_sound_results_mutual[Live_ExtCall_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs(),
       live_memory_result_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule eval_ext_call_success_value >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_RawLog_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_RawRevert_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_SelfDestruct_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> gvs[]
QED

Theorem eval_send_success_value[local]:
  eval_send cx has_gas vs st = (INL pv,st') ==> ?v. pv = Value v
Proof
  Cases_on `vs` >- simp[eval_send_def, raise_def] >>
  Cases_on `t` >- simp[eval_send_def, raise_def] >>
  Cases_on `dest_AddressV h` >> Cases_on `dest_NumV h'` >>
  simp[eval_send_def, bind_apply, ignore_bind_apply, type_check_def,
       check_def, assert_def, return_def, raise_def, lift_option_type_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
  Cases_on `st.outcomes` >>
  gvs[bind_apply, ignore_bind_apply, return_def, raise_def, AllCaseEqs(),
      get_accounts_def, get_transient_storage_def, lift_option_def,
      bind_def, ignore_bind_def, check_def, assert_def] >>
  rpt strip_tac >> gvs[] >>
  pairarg_tac >> gvs[bind_def, ignore_bind_def, check_def, assert_def,
                       return_def, raise_def, AllCaseEqs()]
QED

Resume eval_scc_type_sound_results_mutual[Live_Send_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs(),
       live_memory_result_def, ignore_bind_def, type_check_def, assert_def,
       raise_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule eval_send_success_value >> strip_tac >> gvs[]
QED

Theorem eval_raw_call_success_value[local]:
  eval_raw_call cx flags addr data amount st = (INL pv,st') ==>
  ?v. pv = Value v
Proof
  simp[eval_raw_call_def, bind_apply, ignore_bind_apply, type_check_def,
       check_def, assert_def, get_accounts_def, get_transient_storage_def,
       return_def, raise_def] >>
  Cases_on `run_raw_call cx flags addr data amount st.accounts st.tStorage` >>
  simp[lift_option_def, bind_apply, ignore_bind_apply, return_def, raise_def,
       update_accounts_def, update_transient_def, append_logs_def] >>
  rpt (IF_CASES_TAC >>
    simp[bind_apply, ignore_bind_apply, return_def, raise_def]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_RawCall_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule eval_raw_call_success_value >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_RawCallCalldata_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule eval_raw_call_success_value >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_Builtin_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_TypeBuiltin_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Trace_Attribute_Selection]:
  RESUME_TAC >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Attribute _ _ _))`
    (assume_tac o REWRITE_RULE [int_calls_expr_def]) >>
  FIRST [
    qpat_x_assum `well_typed_expr env (Attribute _ _ _)`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [Once well_typed_expr_def]),
    qpat_x_assum `type_place_expr env (Attribute _ _ _) = SOME vt`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [Once well_typed_expr_def, AllCaseEqs()])] >>
  Cases_on `eval_expr cx e st` >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC,
    disj2_tac >> goal_assum drule])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_Attribute_Capture_Selection]:
  RESUME_TAC >>
  FIRST [
    qpat_x_assum `well_typed_expr env (Attribute _ _ _)`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [Once well_typed_expr_def]),
    qpat_x_assum `type_place_expr env (Attribute _ _ _) = SOME vt` mp_tac >>
      simp[Once well_typed_expr_def]] >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Attribute _ _ _))`
    (assume_tac o REWRITE_RULE [int_calls_expr_def]) >>
  Cases_on `eval_expr cx e st` >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  simp[] >> Cases_on `res` >> gvs[] >>
  irule transported_typed_result_extend_live >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexistsl_tac [`env`, `Type (expr_type e)`] >>
  simp[typed_scope_transition_refl, vyperImmutableMetadataFrameTheory.immutable_metadata_frame_refl]
QED

Resume eval_scc_type_sound_results_mutual[Live_Pop_Retained_Owner]:
  RESUME_TAC >>
  rename1 `eval_expr cx (Pop ty bt) st = (res,st')` >>
  drule well_typed_expr_Pop_dynamic_target_assignable >> strip_tac >>
  `well_typed_target env bt (ArrayT ty (Dynamic n))` by simp[well_typed_target_def] >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Pop _ _))`
    (assume_tac o REWRITE_RULE [int_calls_expr_def]) >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,st1)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => live_memory_result _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => writable_place_result _ _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  rpt (qpat_x_assum `!env ty st res st'. _` kall_tac) >>
  qpat_x_assum `eval_expr cx (Pop _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  (reverse (Cases_on `target_res`) >- (simp[] >> strip_tac >> gvs[])) >>
  simp[] >> strip_tac >>
  gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
  rename1 `evaluate_type env.type_defs ty = SOME tv` >>
  `runtime_consistent env cx st1` by simp[runtime_consistent_def] >>
  `runtime_place_writable cx st1 x` by gvs[writable_place_result_def] >>
  Cases_on `res` >> simp[] >> rename1 `pop_place cx x st1 = (INL pv,st')` >>
  Cases_on `pv` >> simp[live_memory_result_def] >>
  drule_at (Pat `pop_place _ _ _ = _`) pop_place_result_live >>
  disch_then (qspecl_then [`n`,`tv`,`env`] mp_tac) >>
  impl_tac >- (Cases_on `x` >> gvs[live_memory_result_def] >> metis_tac[]) >>
  simp[live_memory_result_def]
QED

Resume eval_scc_type_sound_results_mutual[Trace_Pop_Target]:
  RESUME_TAC >>
  rename1 `eval_expr cx (Pop ty bt) st = (res,st')` >>
  FIRST [drule well_typed_expr_Pop_dynamic_target_assignable >> strip_tac,
    qpat_x_assum `type_place_expr env (Pop _ _) = SOME vt` mp_tac >>
      simp[Once well_typed_expr_def]] >>
  `well_typed_target env bt (ArrayT ty (Dynamic n))` by simp[well_typed_target_def] >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Pop _ _))`
    (assume_tac o REWRITE_RULE [int_calls_expr_def]) >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,st1)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => live_memory_result _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => writable_place_result _ _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> typed_scope_transition _ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `eval_expr cx (Pop _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  (reverse (Cases_on `target_res`) >- (simp[] >> strip_tac >> gvs[])) >>
  simp[] >> strip_tac >>
  gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
  rename1 `evaluate_type env.type_defs ty = SOME tv` >>
  `runtime_consistent env cx st1` by simp[runtime_consistent_def] >>
  `runtime_place_writable cx st1 x` by gvs[writable_place_result_def] >>
  irule typed_scope_transition_trans >> qexists_tac `st1` >> simp[] >>
  irule pop_place_typed_transition >>
  goal_assum (drule_at (Pat `pop_place _ _ _ = _`)) >>
  qexistsl_tac [`env`,`tv`,`n`] >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[Live_Subscript_Capture_Index_Selection]:
  RESUME_TAC >>
  IF (qpat_assum `well_typed_expr _ (Subscript _ _ _)` (K all_tac))
    (qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac)
    (qpat_x_assum `type_place_expr _ (Subscript _ _ _) = SOME _` mp_tac) >>
  simp[NoAsms, Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_expr cx e st` >>
  qpat_assum `!env st res st'. _ ==> (_ /\ _)`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  FIRST [
    qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> _` drule >> strip_tac,
    qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac] >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC,
    disj2_tac >> goal_assum drule])) >> strip_tac >>
  (reverse (Cases_on `q`)
  >- (qpat_x_assum `!s'' res t. _` kall_tac >>
      rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
      qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
      simp[NoAsms, raise_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `!s'' res t. eval_expr _ _ _ = _ ==> _`
    (qspecl_then [`st`,`x`,`r`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  Cases_on `eval_expr cx e' r` >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `well_typed_expr env e' ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac read_result_state >> gvs[] >>
  Cases_on `res` >> simp[] >>
  irule transported_typed_result_extend_live >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  drule eval_expr_immutable_metadata_frame >> simp[])
QED

Resume eval_scc_type_sound_results_mutual[Trace_Base_Subscript_Selection]:
  RESUME_TAC >>
  qpat_x_assum `type_place_target env (SubscriptTarget _ _) = SOME _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_base_place cx bt st` >>
  qpat_x_assum `!env vt st res st'. _ ==> typed_scope_transition _ _`
    (drule_all_then assume_tac) >>
  qpat_x_assum `!env vt st res st'. _ ==> _ /\ _`
    (drule_all_then strip_assume_tac) >>
  (reverse (Cases_on `q`)
  >- (rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
      qpat_x_assum `eval_base_place cx (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
      simp[NoAsms, raise_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `!s'' pv t'. eval_base_place _ _ _ = _ ==> _`
    (qspecl_then [`st`,`x`,`r`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  Cases_on `eval_expr cx e r` >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  qpat_x_assum `eval_base_place cx (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac read_result_state >> imp_res_tac vyperPlaceFramesTheory.extend_place_state >>
  gvs[] >> metis_tac[typed_scope_transition_trans])
QED

Resume eval_scc_type_sound_results_mutual[Live_Base_Subscript_Capture_Index_Selection]:
  RESUME_TAC >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_base_place cx bt st` >>
  qpat_x_assum `!env vt st res st'. _ ==> _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env vt st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (drule_all_then assume_tac) >>
  (reverse (Cases_on `q`)
  >- (rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
      qpat_x_assum `eval_base_place cx (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
      simp[NoAsms, raise_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `!s'' pv t'. eval_base_place _ _ _ = _ ==> _`
    (qspecl_then [`st`,`x`,`r`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  Cases_on `eval_expr cx e r` >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  qpat_x_assum `eval_base_place cx (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac read_result_state >> gvs[] >>
  Cases_on `res` >> simp[] >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame r r''` by
    (drule eval_expr_immutable_metadata_frame >> simp[]) >>
  `eval_result_typed (env,cx,r'') x vt'` by
    (irule eval_result_typed_transport >> goal_assum (drule_at Any) >> simp[]) >>
  `live_memory_result r'' x` by
    (Cases_on `x` >> simp[live_memory_result_def] >>
     rename1 `PlaceR p` >> Cases_on `p` >> simp[live_memory_result_def] >>
     drule_all live_memory_result_transport >> simp[live_memory_result_def]) >>
  irule extend_typed_result_live >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum drule)
QED

Resume eval_scc_type_sound_results_mutual[Live_IfExp_Selected_Conversion]:
  RESUME_TAC >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> (_ ==> _) /\ _` drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _ ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms] >> strip_tac >>
  imp_res_tac read_result_state >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  rpt (qpat_x_assum `!s'' tv t. eval_expr _ _ s'' = (INL tv,t) ==> _` drule >> strip_tac) >>
  qpat_x_assum `switch_BoolV cx _ _ _ _ = _` mp_tac >>
  simp[NoAsms, switch_BoolV_def, bind_def, return_def, raise_def,
       AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac read_result_state >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  simp[NoAsms, COND_RATOR, raise_def] >> rpt IF_CASES_TAC >>
  simp[NoAsms, raise_def] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  rpt (qpat_x_assum `!env st res st'. (well_typed_expr env e \/ _) /\ _ ==> _` kall_tac) >>
  qpat_x_assum `!env st res st'. _ ==> (_ ==> _) /\ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _ ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms] >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  gvs[] >> drule_all conditional_result_live_typed >> strip_tac >> gvs[] >>
  Cases_on `res` >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[RaiseCustomError]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum
    `call_evaluation_safe cx
       (int_calls_stmt (Raise (RaiseCustomError err)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_raise_reason_def] >>
  strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def, well_typed_custom_error_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  Cases_on `err` >>
  Cases_on `get_module_code cx (FST p)`
  >- gvs[evaluate_def, raise_def, no_type_error_result_def,
          return_exception_typed_def] >>
  rename1 `get_module_code cx (FST p) = SOME tops` >>
  Cases_on `lookup_custom_error_args_in (SND p) tops`
  >- gvs[evaluate_def, raise_def, no_type_error_result_def,
          return_exception_typed_def] >>
  rename1 `lookup_custom_error_args_in (SND p) tops = SOME params` >>
  Cases_on `order_custom_error_args params (CustomError p l l0)`
  >- gvs[evaluate_def, raise_def, no_type_error_result_def,
          return_exception_typed_def] >>
  rename1
    `order_custom_error_args params (CustomError p positional kwargs) =
       SOME es` >>
  qpat_x_assum `!id positional' kwargs' tops params es. _`
    (qspecl_then [`p`, `positional`, `kwargs`, `tops`, `params`, `es`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def] >>
  `PERM (custom_error_exprs (CustomError p positional kwargs)) es` by
    (drule order_custom_error_args_perm >> simp[]) >>
  `well_typed_exprs env es` by
    (drule well_typed_exprs_perm >>
     disch_then (qspec_then `env` mp_tac) >>
     simp[custom_error_exprs_def]) >>
  `call_evaluation_safe cx
      (int_calls_exprs (custom_error_exprs
        (CustomError p positional kwargs)))` by
    simp[custom_error_exprs_def] >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qspecl_then
       [`cx`, `custom_error_exprs (CustomError p positional kwargs)`, `es`]
       mp_tac call_evaluation_safe_exprs_perm >>
     simp[custom_error_exprs_def]) >>
  pure_rewrite_tac[bind_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (exprs_res,st1)` >>
  qpat_x_assum `!env st res st'. _ ==> (state_well_typed st' /\ _)`
    drule_all >>
  strip_tac >>
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  Cases_on `exprs_res`
  >- (
    Cases_on
      `build_custom_error_data (get_tenv cx) (SND p)
         (MAP SND params) x` >>
    gvs[bind_def, no_type_error_result_def, lift_option_def, return_def, raise_def,
        return_exception_typed_def] >>
    rpt strip_tac >>
    gvs[bind_def, no_type_error_result_def, lift_option_def, return_def, raise_def,
        return_exception_typed_def]) >>
  rpt strip_tac >>
  gvs[no_type_error_result_def, bind_def, return_exception_typed_def] >>
  drule_all eval_exprs_exception_return_typed >>
  disch_then (qspecl_then [`ret_ty`, `env`] mp_tac) >>
  simp[return_exception_typed_def]
QED


Resume eval_scc_type_sound_results_mutual[AssertCustomError]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum
    `call_evaluation_safe cx
       (int_calls_stmt (Assert e (AssertCustomError err)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def] >>
  strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_exprs (custom_error_exprs err)` >> simp[]) >>
  `call_evaluation_safe cx
      (int_calls_exprs (custom_error_exprs err))` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())
    [type_stmt_def, well_typed_custom_error_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())
    [evaluate_def, bind_def, return_def, raise_def, AllCaseEqs(),
     PULL_EXISTS] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _`
    (drule_then strip_assume_tac) >>
  Cases_on `expr_res` >> rewrite_tac[no_type_error_result_def]
  >- (
    qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
    qpat_x_assum `!vt. _` kall_tac >>
    qpat_x_assum `case INL x of INL pv => eval_result_typed _ pv _ | INR _ => T` mp_tac >>
    simp_tac (srw_ss()) [] >> strip_tac >>
    `live_memory_result st1 x` by (
      qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
        (qspecl_then [`env`, `st`, `INL x`, `st1`] mp_tac) >> simp[]) >>
    qpat_x_assum `!s tv t id positional kwargs tops params es. _`
      (drule_then (mk_asm "custom_ih")) >>
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (loaded,st2)` >>
    drule_all live_result_read_typed >> strip_tac >> gvs[] >>
    reverse (Cases_on `loaded`)
    >- (drule read_result_no_control >> strip_tac >>
        Cases_on `y` >>
        gvs[switch_BoolV_def, bind_def, raise_def, no_control_exc_def,
            no_type_error_result_def, return_exception_typed_def] >>
        rpt strip_tac >> gvs[]) >>
    gvs[value_runtime_typed_def, evaluate_type_def] >>
    drule value_has_type_BoolTV >> strip_tac >> gvs[] >>
    Cases_on `b` >> simp[switch_BoolV_def, bind_def, return_def]
    >- (rpt strip_tac >> gvs[no_type_error_result_def]) >>
    asm_x "custom_ih" strip_assume_tac >>
    Cases_on `err` >>
    Cases_on `get_module_code cx (FST p)`
    >- (rpt (qpat_x_assum `!x. _` kall_tac) >>
        rpt strip_tac >>
        gvs[raise_def, no_type_error_result_def,
            return_exception_typed_def]) >>
    rename1 `get_module_code cx (FST p) = SOME tops` >>
    Cases_on `lookup_custom_error_args_in (SND p) tops`
    >- (rpt (qpat_x_assum `!x. _` kall_tac) >>
        rpt strip_tac >>
        gvs[raise_def, no_type_error_result_def,
            return_exception_typed_def]) >>
    rename1 `lookup_custom_error_args_in (SND p) tops = SOME params` >>
    Cases_on `order_custom_error_args params (CustomError p l l0)`
    >- (rpt (qpat_x_assum `!x. _` kall_tac) >>
        rpt strip_tac >>
        gvs[raise_def, no_type_error_result_def,
            return_exception_typed_def]) >>
    rename1
      `order_custom_error_args params
         (CustomError p positional kwargs) = SOME es` >>
    qpat_x_assum `!id positional' kwargs' tops params es. _`
      (qspecl_then [`p`, `positional`, `kwargs`, `tops`, `params`, `es`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    `PERM (custom_error_exprs (CustomError p positional kwargs)) es` by
      (drule order_custom_error_args_perm >> simp[]) >>
    `well_typed_exprs env es` by
      (drule well_typed_exprs_perm >>
       disch_then (qspec_then `env` mp_tac) >>
       simp[custom_error_exprs_def]) >>
    `call_evaluation_safe cx
        (int_calls_exprs (custom_error_exprs
          (CustomError p positional kwargs)))` by
      simp[custom_error_exprs_def] >>
    `call_evaluation_safe cx (int_calls_exprs es)` by
      (qspecl_then
         [`cx`, `custom_error_exprs (CustomError p positional kwargs)`, `es`]
         mp_tac call_evaluation_safe_exprs_perm >>
       simp[custom_error_exprs_def]) >>
    Cases_on `eval_exprs cx es st1` >>
    rename1 `eval_exprs cx es st1 = (args_res,st2)` >>
    qpat_x_assum `!env st res st'. _ ==> (state_well_typed st' /\ _)`
      drule_all >> strip_tac >>
    rpt (qpat_x_assum `!x. _` kall_tac) >>
    Cases_on `args_res`
    >- (Cases_on `build_custom_error_data (get_tenv cx) (SND p) (MAP SND params) x'` >>
        gvs[bind_def, no_type_error_result_def, lift_option_def, return_def,
            raise_def, return_exception_typed_def] >>
        rpt strip_tac >> gvs[]) >>
    rpt strip_tac >>
    gvs[no_type_error_result_def, bind_def, return_exception_typed_def] >>
    drule_all eval_exprs_exception_return_typed >>
    disch_then (qspecl_then [`ret_ty`, `env`] mp_tac) >>
    simp[return_exception_typed_def]) >>
  rpt strip_tac >>
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  gvs[no_type_error_result_def] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED


(* ===== ABI evaluator roots ===== *)

Theorem read_result_abi_snapshot_sound[local]:
  state_well_typed st /\ eval_result_typed (env,cx,st) pv (Type (expr_type e)) /\
  live_memory_result st pv /\ read_result cx pv st = (res,rt) ==>
  rt = st /\ no_type_error_result res /\
  case res of INL v => abi_expr_result_valid env rt e (AbiSnapshot v) | INR _ => T
Proof
  strip_tac >> drule_all live_result_read_typed >> strip_tac >>
  Cases_on `res` >> gvs[abi_expr_result_valid_def, abi_operand_valid_def,
    value_runtime_typed_def, no_type_error_result_def] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

Resume eval_scc_type_sound_results_mutual[AbiExprs_nil]:
  rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, return_def, no_type_error_result_def, abi_exprs_result_valid_def]
QED

Resume eval_scc_type_sound_results_mutual[AbiExpr_Name]:
  rpt gen_tac >> strip_tac >> reverse conj_tac >- simp[Once well_typed_expr_def] >>
  strip_tac >> gvs[Once evaluate_def] >>
  drule_all lookup_abi_local_sound >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[AbiExpr_TopLevelName]:
  rpt gen_tac >> strip_tac >> gvs[Once evaluate_def] >> conj_tac
  >- (strip_tac >> drule_all lookup_abi_global_expr_sound >> simp[]) >>
  rpt strip_tac >> drule_all lookup_abi_global_place_sound >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[AbiExpr_Pop]:
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_rename_tac `Pop elem_ty bt` >> reverse conj_tac
  >- simp[Once well_typed_expr_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_target bt)` by gvs[int_calls_expr_def] >>
  drule well_typed_expr_Pop_dynamic_target_assignable >> strip_tac >>
  `well_typed_target env bt (ArrayT elem_ty (Dynamic n))` by simp[well_typed_target_def] >>
  qpat_x_assum `eval_abi_expr _ (Pop _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,target_st)` >>
  qpat_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!env ty st res st'. _ ==> case res of INL p => live_memory_result _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!env ty st res st'. _ ==> case res of INL p => writable_place_result _ _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  rpt (qpat_x_assum `!env ty st res st'. _` kall_tac) >>
  Cases_on `target_res` >> gvs[]
  >- (rename1 `eval_target_place cx bt st = (INL p,target_st)` >>
      `!src id. p <> ImmutablePlace src id []` by
        (irule mutable_target_not_direct_immutable >> goal_assum drule >>
         qexistsl_tac [`env`,`ArrayT elem_ty (Dynamic n)`] >>
         fs[Once well_typed_expr_def]) >>
      gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs(), writable_place_result_def] >>
      rename1 `evaluate_type env.type_defs elem_ty = SOME tv` >>
      Cases_on `abi_place_operand cx p target_st` >>
      rename1 `abi_place_operand cx p target_st = (arg_res,arg_st)` >>
      drule_all abi_place_operand_valid >> strip_tac >>
      drule abi_place_operand_observations >> strip_tac >>
      `typed_scope_transition target_st arg_st` by
        (irule typed_scope_transition_scopes >> simp[]) >>
      `vyperImmutableMetadataFrame$immutable_metadata_frame target_st arg_st` by
        (irule vyperImmutableMetadataFrameTheory.immutable_metadata_frame_eq >> simp[]) >>
      `runtime_place_typed cx arg_st p (ArrayTV tv (Dynamic n))` by
        (drule_all runtime_place_typed_transport >> simp[]) >>
      `writable_place_result cx arg_st (PlaceR p)` by
        (irule writable_place_result_transport >> qexists_tac `target_st` >>
         simp[writable_place_result_def]) >>
      `live_memory_result arg_st (PlaceR p)` by
        (irule live_result_transport >> qexists_tac `target_st` >> simp[]) >>
      Cases_on `arg_res` >> gvs[]
      >- (rename1 `abi_place_operand cx p target_st = (INL arg,arg_st)` >>
          Cases_on `abi_pop_pointer cx arg arg_st` >>
          rename1 `abi_pop_pointer cx arg arg_st = (ptr_res,ptr_st)` >>
          drule_all (SRULE [] abi_pop_pointer_valid) >> strip_tac >> gvs[] >>
          Cases_on `ptr_res` >> gvs[]
          >- (rename1 `abi_pop_pointer cx arg arg_st = (INL ptr,arg_st)` >>
              Cases_on `pop_place cx p arg_st` >>
              rename1 `pop_place cx p arg_st = (pop_res,pop_st)` >>
              `runtime_consistent env cx arg_st` by simp[runtime_consistent_def] >>
              `runtime_place_writable cx arg_st p` by gvs[writable_place_result_def] >>
              `runtime_consistent env cx pop_st /\ no_type_error_result pop_res` by
                (irule pop_place_sound >> goal_assum (drule_at Any) >>
                 Cases_on `p` >> gvs[live_memory_result_def] >> metis_tac[]) >>
              drule (cj 3 arena_extends_assignment |> REWRITE_RULE [arena_extends_result]) >>
              strip_tac >> Cases_on `pop_res` >>
              simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def] >> strip_tac >>
              gvs[runtime_consistent_def, no_type_error_result_def,
                  abi_expr_result_valid_def, expr_type_def] >>
              irule abi_operand_valid_memory_frame >>
              qexists_tac `arg_st` >> simp[]) >>
          strip_tac >> gvs[no_type_error_result_def]) >>
      strip_tac >> gvs[no_type_error_result_def]) >>
  strip_tac >> gvs[no_type_error_result_def]
QED

Resume eval_scc_type_sound_results_mutual[AbiExpr_Subscript]:
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_rename_tac `Subscript result_ty base_expr idx_expr` >>
  `call_evaluation_safe cx (int_calls_expr base_expr)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr (Subscript result_ty base_expr idx_expr)` >> simp[int_calls_expr_def]) >>
  `call_evaluation_safe cx (int_calls_expr idx_expr)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr (Subscript result_ty base_expr idx_expr)` >> simp[int_calls_expr_def]) >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `env_consistent env cx st` mp_tac >>
     simp[NoAsms, env_consistent_def, env_context_consistent_def]) >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  FIRST [
    (qpat_x_assum `well_typed_expr env (Subscript result_ty base_expr idx_expr)` mp_tac >>
     simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac),
    (qpat_x_assum `type_place_expr env (Subscript result_ty base_expr idx_expr) = SOME _` mp_tac >>
     simp_tac(srw_ss())[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac)] >>
  (TRY (qmatch_asmsub_rename_tac `type_place_expr env base_expr = SOME base_vt` >>
       `well_formed_vtype env.type_defs base_vt` by
         (drule_all type_place_expr_well_formed_vtype_stmt >> simp[]) >>
       `vtype_annotation_ok base_vt (expr_type base_expr)` by
         (drule_all type_place_expr_annotation_ok_stmt >> simp[])) >>
  qpat_x_assum `eval_abi_expr _ (Subscript _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_abi_expr cx base_expr st` >>
  rename1 `eval_abi_expr cx base_expr st = (base_res,base_st)` >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` (drule_all_then strip_assume_tac) >>
  FIRST [
    (qpat_x_assum `well_typed_expr env base_expr ==> _` drule_all >> strip_tac),
    (qpat_x_assum `!vt. type_place_expr env base_expr = SOME vt ==> _` drule_all >> strip_tac)] >>
  rpt (qpat_x_assum `!vt. type_place_expr env base_expr = SOME vt ==> _` kall_tac) >>
  rpt (qpat_x_assum `well_typed_expr env base_expr ==> _` kall_tac) >>
  Cases_on `base_res` >> simp_tac(srw_ss())[]
  >- (fs[] >> rename1 `eval_abi_expr cx base_expr st = (INL arg,base_st)` >>
      qpat_x_assum `!s'' arg t. eval_abi_expr cx base_expr s'' = _ ==> _` drule >> strip_tac >>
      Cases_on `eval_expr cx idx_expr base_st` >>
      rename1 `eval_expr cx idx_expr base_st = (index_res,index_st)` >>
      qpat_assum `!env st res st'. _ ==> (_ /\ _)` (drule_all_then strip_assume_tac) >>
      qpat_x_assum `well_typed_expr env idx_expr ==> _` drule_all >> strip_tac >>
      qpat_x_assum `!vt. type_place_expr env idx_expr = SOME vt ==> _` kall_tac >>
      qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
        (qspecl_then [`env`,`base_st`,`index_res`,`index_st`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
      drule eval_expr_abi_memory_length >> strip_tac >>
      drule eval_expr_abi_immutables_length >> strip_tac >>
      TRY (drule_all abi_expr_result_valid_memory_frame >> strip_tac) >>
      TRY (drule_all abi_place_result_valid_memory_frame >> strip_tac) >>
      Cases_on `index_res` >> gvs[no_type_error_result_def]
      >- (rename1 `eval_expr cx idx_expr base_st = (INL tv,index_st)` >>
          Cases_on `read_result cx tv index_st` >>
          rename1 `read_result cx tv index_st = (value_res,value_st)` >>
          drule_all live_result_read_typed >> strip_tac >> gvs[] >>
          Cases_on `value_res`
          >- (rename1 `read_result cx tv index_st = (INL idx,index_st)` >>
              TRY (`subscript_index_matches (expr_type base_expr) idx_expr idx` by
                (drule_all eval_expr_subscript_index_matches_stmt >> simp[])) >>
              `?parent. evaluate_type env.type_defs (expr_type base_expr) = SOME parent` by
                FIRST [gvs[abi_expr_result_valid_def] >> NO_TAC,
                       drule_all abi_place_annotation_evaluates >> simp[]] >>
              gvs[lift_option_type_def, bind_def, return_def] >> strip_tac >>
              TRY (`abi_operand_valid index_st parent arg` by gvs[abi_expr_result_valid_def]) >>
              FIRST [
                (qpat_assum `env.type_defs = get_tenv cx`
                   (fn th => drule_all (SRULE [th] (SPEC_ALL abi_subscript_sound))) >>
                 strip_tac >> Cases_on `res` >>
                 gvs[abi_expr_result_valid_def, expr_type_def, no_type_error_result_def]),
                (qpat_assum `env.type_defs = get_tenv cx`
                   (fn th => drule_all (SRULE [th] (SPEC_ALL abi_subscript_place_sound))) >>
                 strip_tac >> Cases_on `res` >>
                 gvs[abi_expr_result_valid_def, abi_place_result_valid_def,
                     expr_type_def, no_type_error_result_def])]) >>
          strip_tac >> gvs[no_type_error_result_def]) >>
      strip_tac >> gvs[no_type_error_result_def]) >>
  strip_tac >> gvs[no_type_error_result_def])
QED

Resume eval_scc_type_sound_results_mutual[AbiExpr_Attribute]:
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_rename_tac `Attribute ty e id` >> reverse conj_tac
  >- simp[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `well_typed_expr env (Attribute ty e id)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def, attribute_type_ok_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by gvs[int_calls_expr_def] >>
  qpat_x_assum `eval_abi_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_abi_expr cx e st` >>
  rename1 `eval_abi_expr cx e st = (base_res,base_st)` >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `well_typed_expr env e ==> _` drule_all >> strip_tac >>
  Cases_on `base_res` >> gvs[]
  >- (strip_tac >> drule_all abi_attribute_sound >> simp[]) >>
  strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[AbiExpr_IfExp]:
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_rename_tac `IfExp ty e e' e''` >> reverse conj_tac
  >- simp[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `well_typed_expr env (IfExp ty e e' e'')` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (IfExp ty e e' e''))` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  qpat_x_assum `!s pv t. eval_expr cx e s = (INL pv,t) ==> _` (mk_asm "abi_yes") >>
  qpat_x_assum `!s pv t. eval_expr cx e s = (INL pv,t) ==> _` (mk_asm "abi_no") >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (cr,mid)` >>
  qpat_assum `!env st res st'. _ ==> (_ /\ _)` (drule_all_then strip_assume_tac) >>
  qpat_x_assum `well_typed_expr env e ==> _` drule_all >> strip_tac >>
  reverse (Cases_on `cr`)
  >- (qpat_x_assum `eval_abi_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def] >> strip_tac >> gvs[no_type_error_result_def]) >>
  rename1 `eval_expr cx e st = (INL cp,mid)` >>
  qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
    (qspecl_then [`env`,`st`,`INL cp`,`mid`] mp_tac) >>
  (impl_tac >- simp[]) >> simp_tac bool_ss [] >> disch_tac >> fs[] >>
  asm_x "abi_yes" (qspecl_then [`st`,`cp`,`mid`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  asm_x "abi_no" (qspecl_then [`st`,`cp`,`mid`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `switch_BoolV cx cp (eval_abi_expr cx e') (eval_abi_expr cx e'') mid` >>
  rename1 `switch_BoolV _ _ _ _ _ = (br,last)` >>
  `state_well_typed last /\ env_consistent env cx last /\
   accounts_well_typed last.accounts /\ no_type_error_result br /\
   (case br of INL arg => abi_expr_result_valid env last (IfExp ty e e' e'') arg | INR _ => T)` by
    (qho_match_abbrev_tac `P br last` >> irule switch_BoolV_live_post >>
     goal_assum (drule_at (Pat `switch_BoolV`)) >> qexists_tac `env` >>
     simp[expr_type_def] >> rpt strip_tac >> FIRST [first_assum ACCEPT_TAC,
       (qpat_assum `!env st res st'. _ ==> (well_typed_expr env e' ==> _) /\ _`
          (drule_all_then strip_assume_tac) >>
        qpat_x_assum `well_typed_expr env e' ==> _` drule_all >> strip_tac >>
        rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
        Cases_on `r` >> gvs[Abbr `P`, abi_expr_result_valid_def, expr_type_def]),
       (qpat_assum `!env st res st'. _ ==> (well_typed_expr env e'' ==> _) /\ _`
          (drule_all_then strip_assume_tac) >>
        qpat_x_assum `well_typed_expr env e'' ==> _` drule_all >> strip_tac >>
        rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
        Cases_on `r` >> gvs[Abbr `P`, abi_expr_result_valid_def, expr_type_def]),
       (rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
        gvs[Abbr `P`, no_type_error_result_def])]) >>
  rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
  qpat_x_assum `eval_abi_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >> Cases_on `br` >> gvs[]
  >- (strip_tac >> drule_all abi_expr_result_valid_unwrap_no_type_error >> strip_tac >>
      Cases_on `res` >> gvs[] >> drule_all abi_expr_result_valid_unwrap >> simp[]) >>
  strip_tac >> gvs[]
QED

fun ABI_SNAPSHOT_TAC g = (
  rpt gen_tac >> strip_tac >> reverse conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
      simp_tac(srw_ss())[Once well_typed_expr_def]) >>
  strip_tac >> qpat_x_assum `eval_abi_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `eval_expr cx expression st` >>
  Cases_on `eval_expr cx expression st` >>
  rename1 `eval_expr cx expression st = (expr_res,expr_st)` >>
  UNABBREV_TAC "expression" >>
  qpat_assum `!env st res st'. _ ==> (_ /\ _)`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `well_typed_expr env _ ==> _` drule_all >> strip_tac >>
  qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
  Cases_on `expr_res` >> gvs[]
  >- (Cases_on `read_result cx x expr_st` >>
      rename1 `read_result cx x expr_st = (mat_res,mat_st)` >>
      drule_all read_result_abi_snapshot_sound >> strip_tac >> gvs[] >>
      Cases_on `mat_res` >> simp[] >> strip_tac >> gvs[no_type_error_result_def]) >>
  strip_tac >> gvs[no_type_error_result_def]) g;

Resume eval_scc_type_sound_results_mutual[AbiExpr_Literal]:
  ABI_SNAPSHOT_TAC
QED
Resume eval_scc_type_sound_results_mutual[AbiExpr_FlagMember]:
  ABI_SNAPSHOT_TAC
QED
Resume eval_scc_type_sound_results_mutual[AbiExpr_Builtin]:
  ABI_SNAPSHOT_TAC
QED
Resume eval_scc_type_sound_results_mutual[AbiExpr_StructLit]:
  ABI_SNAPSHOT_TAC
QED
Resume eval_scc_type_sound_results_mutual[AbiExpr_TypeBuiltin]:
  ABI_SNAPSHOT_TAC
QED
Resume eval_scc_type_sound_results_mutual[AbiExpr_Call]:
  ABI_SNAPSHOT_TAC
QED

Resume eval_scc_type_sound_results_mutual[AbiExprs_cons]:
  rpt gen_tac >> strip_tac >>
  drule exprs_cons_call_evaluation_safe_head >> strip_tac >>
  drule exprs_cons_call_evaluation_safe_tail >> strip_tac >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_abi_exprs _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_abi_expr cx e st` >>
  rename1 `eval_abi_expr cx e st = (head_res,head_st)` >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` (drule_all_then strip_assume_tac) >>
  qpat_x_assum `well_typed_expr env e ==> _` drule_all >> strip_tac >>
  qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> _` kall_tac >>
  Cases_on `head_res` >> simp_tac(srw_ss())[]
  >- (rename1 `eval_abi_expr cx e st = (INL head_arg,head_st)` >>
      qpat_x_assum `(case INL head_arg of
        INL arg => abi_expr_result_valid env head_st e arg | INR _ => T)`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      Cases_on `unwrap_abi_operand cx head_arg head_st` >>
      rename1 `unwrap_abi_operand cx head_arg head_st = (unwrap_res,unwrap_st)` >>
      drule_all abi_expr_result_valid_unwrap_no_type_error >> strip_tac >> gvs[] >>
      Cases_on `unwrap_res` >> gvs[]
      >- (drule_all abi_expr_result_valid_unwrap >> strip_tac >>
          qpat_x_assum `!s arg t s3 arg' t'. _` (drule_all_then strip_assume_tac) >>
          Cases_on `eval_abi_exprs cx es head_st` >>
          rename1 `eval_abi_exprs cx es head_st = (tail_res,tail_st)` >>
          qpat_assum `!env st res st'. _ ==> state_well_typed _ /\ _`
            (drule_all_then strip_assume_tac) >>
          drule eval_abi_exprs_abi_memory_length >> strip_tac >>
          drule eval_abi_exprs_abi_immutables_length >> strip_tac >>
          Cases_on `tail_res` >> gvs[no_type_error_result_def] >>
          strip_tac >> gvs[] >>
          irule abi_exprs_result_valid_cons >> simp[] >>
          irule abi_expr_result_valid_memory_frame >>
          goal_assum drule >> simp[]) >>
      strip_tac >> gvs[no_type_error_result_def]) >>
  qpat_x_assum `!s'' arg t s3 arg' t'. _` kall_tac >>
  strip_tac >> gvs[no_type_error_result_def]
QED

Resume eval_scc_type_sound_results_mutual[Trace_AbiExprs_cons]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  drule exprs_cons_call_evaluation_safe_head >> strip_tac >>
  drule exprs_cons_call_evaluation_safe_tail >> strip_tac >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_abi_exprs _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_abi_expr cx e st` >>
  rename1 `eval_abi_expr cx e st = (head_res,head_st)` >>
  qpat_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_abi_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` (drule_all_then strip_assume_tac) >>
  qpat_x_assum `well_typed_expr env e ==> _` drule_all >> strip_tac >>
  Cases_on `head_res` >> gvs[]
  >- (Cases_on `unwrap_abi_operand cx x head_st` >>
      rename1 `unwrap_abi_operand cx x head_st = (ur,us)` >>
      drule vyperAbiOperandTypingTheory.unwrap_abi_operand_state >> strip_tac >> gvs[] >>
      Cases_on `ur` >> gvs[]
      >- (qpat_x_assum `!s arg t s3 arg' t'. _` (drule_all_then strip_assume_tac) >>
          Cases_on `eval_abi_exprs cx es head_st` >>
          rename1 `eval_abi_exprs cx es head_st = (tail_res,tail_st)` >>
          qpat_assum `!env st res st'. _ ==> typed_scope_transition _ _`
            (drule_at (Pat `eval_abi_exprs _ _ _ = _`)) >>
          disch_then (qspec_then `env` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
          Cases_on `tail_res` >> simp[] >> strip_tac >> gvs[] >>
          metis_tac[typed_scope_transition_trans]) >>
      strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

fun ABI_TRACE_LEAF_TAC g = (
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_abi_expr _ _ _ = _` mp_tac >>
  rewrite_tac[Once evaluate_def] >> strip_tac >> ABI_SCOPE_TAC >>
  irule typed_scope_transition_scopes >> simp[]) g;

Resume eval_scc_type_sound_results_mutual[Trace_AbiExpr_Name]:
  ABI_TRACE_LEAF_TAC
QED
Resume eval_scc_type_sound_results_mutual[Trace_AbiExpr_TopLevelName]:
  ABI_TRACE_LEAF_TAC
QED
Resume eval_scc_type_sound_results_mutual[Trace_AbiExprs_nil]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, return_def] >> irule typed_scope_transition_refl
QED

fun ABI_TRACE_SNAPSHOT_TAC g = (
  RESUME_TAC >> trace_value_start_tac >>
  qpat_x_assum `eval_abi_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- simp[]) >> simp[]) g;

Resume eval_scc_type_sound_results_mutual[Trace_AbiExpr_Literal]:
  ABI_TRACE_SNAPSHOT_TAC
QED
Resume eval_scc_type_sound_results_mutual[Trace_AbiExpr_FlagMember]:
  ABI_TRACE_SNAPSHOT_TAC
QED
Resume eval_scc_type_sound_results_mutual[Trace_AbiExpr_Builtin]:
  ABI_TRACE_SNAPSHOT_TAC
QED
Resume eval_scc_type_sound_results_mutual[Trace_AbiExpr_StructLit]:
  ABI_TRACE_SNAPSHOT_TAC
QED
Resume eval_scc_type_sound_results_mutual[Trace_AbiExpr_TypeBuiltin]:
  ABI_TRACE_SNAPSHOT_TAC
QED
Resume eval_scc_type_sound_results_mutual[Trace_AbiExpr_Call]:
  ABI_TRACE_SNAPSHOT_TAC
QED

Resume eval_scc_type_sound_results_mutual[Trace_AbiExpr_Attribute]:
  RESUME_TAC >> trace_value_start_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `eval_abi_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >> ABI_SCOPE_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_abi_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- simp[]) >> simp[typed_scope_transition_def]
QED

Resume eval_scc_type_sound_results_mutual[Trace_AbiExpr_IfExp]:
  RESUME_TAC >> trace_value_start_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  imp_res_tac call_evaluation_safe_append_left >> imp_res_tac call_evaluation_safe_append_right >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  qpat_x_assum `eval_abi_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  asm_rewrite_tac[] >>
  qpat_x_assum `!env st res st'. _ ==> (_ ==> _) /\ _` drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _ ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms] >> strip_tac >>
  rpt (qpat_x_assum `!s tv t. eval_expr _ _ s = (INL tv,t) ==> _` drule >> strip_tac) >>
  qpat_x_assum `switch_BoolV cx _ _ _ _ = _` mp_tac >>
  simp[NoAsms, switch_BoolV_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac read_result_state >> rpt BasicProvers.VAR_EQ_TAC >> asm_rewrite_tac[] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  simp[NoAsms, COND_RATOR, raise_def] >> rpt IF_CASES_TAC >>
  simp[NoAsms, raise_def] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> asm_rewrite_tac[] >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_abi_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  ABI_SCOPE_TAC >>
  metis_tac[typed_scope_transition_scopes, typed_scope_transition_trans]
QED

Resume eval_scc_type_sound_results_mutual[Trace_AbiExpr_Subscript]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  IF (qpat_assum `well_typed_expr _ (Subscript _ _ _)` (K all_tac))
    (qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac)
    (qpat_x_assum `type_place_expr _ (Subscript _ _ _) = SOME _` mp_tac) >>
  simp[NoAsms, Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_abi_expr cx e st` >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_abi_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC, disj2_tac >> goal_assum drule])) >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
    (drule_at (Pat `eval_abi_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  FIRST [qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> _` drule >> strip_tac,
    qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac] >>
  (reverse (Cases_on `q`)
  >- (qpat_x_assum `!s res t. _` kall_tac >>
      qpat_x_assum `eval_abi_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
      simp[NoAsms, raise_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `!s res t. eval_abi_expr _ _ _ = _ ==> _`
    (qspecl_then [`st`,`x`,`r`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  Cases_on `eval_expr cx e' r` >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  qpat_x_assum `eval_abi_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >>
  rpt BasicProvers.VAR_EQ_TAC >> ABI_SCOPE_TAC >> gvs[] >>
  metis_tac[typed_scope_transition_scopes, typed_scope_transition_trans])
QED

Resume eval_scc_type_sound_results_mutual[Trace_AbiExpr_Pop]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  rename1 `eval_abi_expr cx (Pop ty bt) st = (res,st')` >>
  FIRST [drule well_typed_expr_Pop_dynamic_target_assignable >> strip_tac,
    qpat_x_assum `type_place_expr env (Pop _ _) = SOME vt` mp_tac >>
      simp[Once well_typed_expr_def]] >>
  `well_typed_target env bt (ArrayT ty (Dynamic n))` by simp[well_typed_target_def] >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Pop _ _))`
    (assume_tac o REWRITE_RULE [int_calls_expr_def]) >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,target_st)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => live_memory_result _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => writable_place_result _ _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> typed_scope_transition _ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `eval_abi_expr cx (Pop _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  reverse (Cases_on `target_res`) >- (simp[] >> strip_tac >> gvs[]) >>
  simp[] >> rename1 `eval_target_place cx bt st = (INL p,target_st)` >>
  `!src id. p <> ImmutablePlace src id []` by
    (irule mutable_target_not_direct_immutable >> goal_assum drule >>
     qexistsl_tac [`env`,`ArrayT ty (Dynamic n)`] >> fs[Once well_typed_expr_def]) >>
  gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs(), writable_place_result_def] >>
  rename1 `evaluate_type env.type_defs ty = SOME tv` >>
  Cases_on `abi_place_operand cx p target_st` >>
  rename1 `abi_place_operand cx p target_st = (arg_res,arg_st)` >>
  drule_all abi_place_operand_valid >> strip_tac >>
  drule abi_place_operand_observations >> strip_tac >>
  `typed_scope_transition target_st arg_st` by (irule typed_scope_transition_scopes >> simp[]) >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame target_st arg_st` by
    (irule vyperImmutableMetadataFrameTheory.immutable_metadata_frame_eq >> simp[]) >>
  `runtime_place_typed cx arg_st p (ArrayTV tv (Dynamic n))` by
    (drule_all runtime_place_typed_transport >> simp[]) >>
  `writable_place_result cx arg_st (PlaceR p)` by
    (irule writable_place_result_transport >> qexists_tac `target_st` >> simp[writable_place_result_def]) >>
  `live_memory_result arg_st (PlaceR p)` by
    (irule live_result_transport >> qexists_tac `target_st` >> simp[]) >>
  suspend "Trace_AbiPop_captured"
QED

Resume eval_scc_type_sound_results_mutual[Trace_AbiPop_captured]:
  Cases_on `arg_res` >> gvs[]
  >- (Cases_on `abi_pop_pointer cx x arg_st` >>
      rename1 `abi_pop_pointer cx x arg_st = (ptr_res,ptr_st)` >>
      drule_all (SRULE [] abi_pop_pointer_valid) >> strip_tac >> gvs[] >>
      Cases_on `ptr_res` >> simp[]
      >- (Cases_on `pop_place cx p arg_st` >>
          rename1 `pop_place cx p arg_st = (pop_res,pop_st)` >>
          `typed_scope_transition arg_st pop_st` by
            (irule pop_place_typed_transition >> goal_assum drule >>
             qexistsl_tac [`env`,`tv`,`n`] >> fs[runtime_consistent_def, writable_place_result_def]) >>
          Cases_on `pop_res` >> simp[bind_def, ignore_bind_def, return_def] >> strip_tac >> gvs[] >>
          metis_tac[typed_scope_transition_trans]) >>
      strip_tac >> gvs[] >> metis_tac[typed_scope_transition_trans]) >>
  strip_tac >> gvs[] >> metis_tac[typed_scope_transition_trans]
QED

Finalise eval_scc_type_sound_results_mutual

Theorem eval_scc_type_sound_mutual =
  LIST_CONJ (List.take (CONJUNCTS eval_scc_type_sound_results_mutual, 10));

val _ = if null (hyp eval_scc_type_sound_mutual) then
  print "Soundness SCC finalised with no suspension hypotheses\n"
  else raise Fail "Soundness SCC retains hypotheses";

(* Forcing is part of the public expression guarantee, not a caller premise. *)
Theorem eval_expr_read_type_sound:
  well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do result <- eval_expr cx e; read_result cx result od) st = (res,st') ==>
  state_well_typed st' /\ no_type_error_result res /\
  (case res of INL v => value_runtime_typed env (expr_type e) v | INR _ => T)
Proof
  rpt strip_tac >>
  qspecl_then [`cx`,`e`] strip_assume_tac (cj 5 eval_scc_type_sound_mutual) >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _ ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  imp_res_tac read_result_state >> gvs[]
  >~ [`no_type_error_result (INR _)`]
  >- gvs[no_type_error_result_def] >>
  drule_all live_result_read_typed >> strip_tac >> simp[]
QED

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      print (name ^ " is closed\n")
    else raise Fail (name ^ " is not closed")
  end)
  [("eval_scc_type_sound_mutual",eval_scc_type_sound_mutual),
   ("eval_expr_read_type_sound",eval_expr_read_type_sound)];
