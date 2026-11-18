(* Typing and frame facts used throughout the mutual evaluator proof. *)

Theory vyperTypeEvalProofs
Ancestors
  list rich_list sorting pred_set prim_rec arithmetic finite_map option pair sum
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperCreate vyperCreateFrame vyperCallFrame vyperInterpreter vyperCallOutcomeFrame vyperState vyperContext vyperStorage vyperTyping vyperLookup
  vyperImmutableMetadataFrame[ignore_grammar]
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeEnvExtension vyperTypeEnvPreservation vyperTypeScopePop
  vyperTypeABI vyperTypeBindArguments vyperTypeExprResult vyperTypeStmtResult
  vyperTypeCallOutcome[ignore_grammar] vyperCallOutcome[ignore_grammar]
  vyperTypeArgFits vyperTypeExtCallSoundness vyperTypeGlobalLookupSoundness vyperTypeAssignContext vyperTypeBuiltins vyperTypeExprSoundness vyperTypeAssignSoundness
  vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
  vyperEvalMisc vyperStatePreservation vyperAssignPreservesType vyperTypeStatePreservation
  vyperTypeCallGraph vyperTypeCallStackSoundness vyperEvalExprPreservesScopesDom vyperPlaceResultTyping vyperPlaceTyping
  vyperPlaceWriteSoundness vyperTargetPlaceWrite vyperPlaceMutationSoundness
  vyperAugAssignWriteSoundness vyperSystemControl
Libs
  wordsLib markerLib intLib

(* ===== Generic exception/result typing helpers ===== *)

Theorem finally_unless_halt_cases[local]:
  finally_unless_halt f g s = (res,t) ==>
  (f s = (INR HaltException,t) /\ res = INR HaltException) \/
  (?r u. f s = (r,u) /\ r <> INR HaltException /\
         finally (\_. (r,u)) g s = (res,t))
Proof
  Cases_on `f s` >> rename1 `f s = (outcome,post)` >>
  Cases_on `outcome` >>
  simp[finally_unless_halt_def, finally_def, bind_def] >>
  TRY (rename1 `f s = (INR error,post)` >> Cases_on `error`) >>
  simp[finally_unless_halt_def, finally_def, bind_def] >>
   metis_tac[]
QED

Theorem finally_pop_function_compose[local]:
  finally (finally f (pop_function prev)) g s =
  finally f (do pop_function prev; g od) s
Proof
  Cases_on `f s` >> rename1 `f s = (outcome,post)` >>
  Cases_on `outcome` >>
  simp[finally_def, bind_def, ignore_bind_def, pop_function_def,
       set_scopes_def, return_def, raise_def]
QED

Theorem finally_unless_halt_pop_cases:
  finally_unless_halt (finally f (pop_function prev)) g s = (res,t) ==>
  finally f (do pop_function prev; g od) s = (res,t) \/
  (res = INR HaltException /\ finally f (pop_function prev) s = (res,t))
Proof
  strip_tac >> drule finally_unless_halt_cases >> strip_tac
  >- simp[] >>
  disj1_tac >> rewrite_tac[GSYM finally_pop_function_compose] >>
  simp[finally_def, bind_def] >>
  qpat_x_assum `finally _ _ _ = (res,t)` mp_tac >>
  simp[finally_def, bind_def]
QED

Theorem finally_unless_halt_pop_success:
  finally_unless_halt (finally f (pop_function prev)) g s = (INL v,t) ==>
  finally f (do pop_function prev; g od) s = (INL v,t)
Proof
  strip_tac >> drule finally_unless_halt_pop_cases >> simp[]
QED

Theorem finally_unless_halt_pop_release_cases:
  finally_unless_halt (finally f (pop_function prev))
    (if nr /\ ~is_view then
       case cx.nonreentrant_slot of
       | NONE => return ()
       | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return ()) s = (res,t) ==>
  ?release. finally f
    (do pop_function prev;
        if release /\ ~is_view then
          case cx.nonreentrant_slot of
          | NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return () od) s = (res,t)
Proof
  strip_tac >> drule finally_unless_halt_pop_cases >> strip_tac
  >- (qexists_tac `nr` >> simp[]) >>
  qexists_tac `F` >>
  `ignore_bind (pop_function prev) (return ()) = pop_function prev` by
    simp[FUN_EQ_THM, ignore_bind_def, bind_def, return_def,
         pop_function_def, set_scopes_def] >>
  gvs[]
QED

Theorem lift_option_type_INL_eq:
  lift_option_type opt msg st = (INL v,st') <=> opt = SOME v /\ st' = st
Proof
  Cases_on `opt`
  >- simp[lift_option_type_def, return_def, raise_def] >>
  simp[lift_option_type_def, return_def, raise_def] >> metis_tac[]

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

Theorem well_typed_exprs_create_operand_order:
  well_typed_exprs env es ==>
  well_typed_exprs env (create_operand_order kind has_salt es)
Proof
  rewrite_tac[well_typed_exprs_EVERY] >>
  Cases_on `kind` >> Cases_on `es` >>
  simp[create_operand_order_def] >>
  TRY (rename1 `_ :: t` >> Cases_on `t` >> simp[create_operand_order_def]) >>
  metis_tac[EVERY_TAKE, EVERY_DROP]
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

Theorem call_evaluation_safe_create_operand_order:
  call_evaluation_safe cx (int_calls_exprs es) ==>
  call_evaluation_safe cx
    (int_calls_exprs (create_operand_order kind has_salt es))
Proof
  strip_tac >> irule call_evaluation_safe_mono >>
  qexists_tac `int_calls_exprs es` >> simp[MEM_int_calls_exprs] >>
  Cases_on `kind` >> Cases_on `es` >>
  simp[create_operand_order_def] >>
  TRY (rename1 `_ :: t` >> Cases_on `t` >> simp[create_operand_order_def]) >>
  metis_tac[MEM_TAKE, MEM_DROP_IMP, MEM]
QED

Theorem fn_sigs_consistent_FLOOKUP:
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

Theorem intcall_lookup_function_not_INR:
  get_module_code cx src_id_opt = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME v /\
  get_module_code cx src_id_opt = SOME ts' ==>
  lift_option_type (lookup_callable_function cx.in_deploy fn ts') msg st <> (INR e,st')
Proof
  rpt strip_tac >> gvs[lift_option_type_def, return_def]
QED

Theorem intcall_args_length_condition:
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

Theorem intcall_call_evaluation_safe_target_not_mem:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (IntCall (src_id_opt,fn)) es extra)) ==>
  ~MEM (src_id_opt,fn) cx.stk
Proof
  simp[int_calls_expr_def] >> strip_tac >>
  irule call_evaluation_safe_target_not_mem >>
  qexists_tac `int_calls_exprs es` >> simp[]
QED

Theorem intcall_call_evaluation_safe_args:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (IntCall callee) es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  strip_tac >> irule call_evaluation_safe_mono >>
  qexists_tac `int_calls_expr (Call loc (IntCall callee) es extra)` >>
  simp[int_calls_expr_def]
QED

Theorem intcall_call_evaluation_safe_needed_defaults:
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

Theorem intcall_call_evaluation_safe_body:
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



Theorem int_calls_exprs_MAP_SND:
  !kes. int_calls_exprs (MAP SND kes) = int_calls_named_exprs kes
Proof
  Induct >> simp[int_calls_expr_def] >> gen_tac >> PairCases_on `h` >>
  simp[int_calls_expr_def]
QED

Theorem call_evaluation_safe_int_calls_exprs_HD:
  es <> [] /\ call_evaluation_safe cx (int_calls_exprs es) ==>
  call_evaluation_safe cx (int_calls_expr (HD es))
Proof
  Cases_on `es` >> simp[int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem extcall_call_evaluation_safe_args:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (ExtCall static skip_check sig opts) es drv)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem send_call_evaluation_safe_args:
  call_evaluation_safe cx (int_calls_expr (Call loc (Send has_gas) es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem rawcall_call_evaluation_safe_args:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (RawCallTarget flags) es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem rawlog_call_evaluation_safe_args:
  call_evaluation_safe cx (int_calls_expr (Call loc RawLog es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem rawrevert_call_evaluation_safe_args:
  call_evaluation_safe cx (int_calls_expr (Call loc RawRevert es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem selfdestruct_call_evaluation_safe_args:
  call_evaluation_safe cx
    (int_calls_expr (Call loc SelfDestructTarget es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem create_call_evaluation_safe_args:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (CreateTarget kind has_salt rof kw_order) es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem exprs_cons_call_evaluation_safe_head:
  call_evaluation_safe cx (int_calls_exprs (e::es)) ==>
  call_evaluation_safe cx (int_calls_expr e)
Proof
  simp[int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem exprs_cons_call_evaluation_safe_tail:
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

Theorem get_tenv_stk_irrelevant:
  !cx f. get_tenv (cx with stk updated_by f) = get_tenv cx
Proof
  simp[get_tenv_def]
QED

Theorem get_module_code_stk_irrelevant:
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

Theorem functions_well_typed_stk_irrelevant:
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

Theorem context_well_typed_stk_irrelevant:
  !cx f. context_well_typed (cx with stk updated_by f) <=>
         context_well_typed cx
Proof
  simp[context_well_typed_def]
QED
Theorem env_scopes_consistent_stk_irrelevant:
  !env cx f st.
    env_scopes_consistent env (cx with stk updated_by f) st <=>
    env_scopes_consistent env cx st
Proof
  simp[env_scopes_consistent_def, get_tenv_stk_irrelevant]
QED

Theorem type_place_expr_Call_ExtCall_NONE:
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
  metis_tac[cj 1 eval_expr_no_control, read_result_no_control,
            array_iterator_results_no_control, no_control_exc_def]
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

Theorem live_result_read_typed:
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
Theorem read_live_result_widens_type:
  state_well_typed st /\ eval_result_typed (env,cx,st) pv (Type src_ty) /\
  live_memory_result st pv /\ read_result cx pv st = (INL v,st') /\
  type_widens_to env.type_defs src_ty dst_ty ==>
  value_runtime_typed env dst_ty v
Proof
  strip_tac >> drule_all live_result_read_typed >> strip_tac >>
  gvs[value_runtime_typed_def] >>
  drule_all type_widens_to_value_has_type >> rw[] >> gvs[]
QED

(* An iteration element is a copied value of the loop variable's type, or a
   storage location of that type read when its iteration starts. *)
Definition iterator_result_typed_def:
  iterator_result_typed tyv res <=>
    case res of
    | Value v => value_has_type tyv v
    | PlaceR (StoragePlace tr slot tv) => tv = tyv /\ well_formed_type_value tyv
    | _ => F
End

Theorem iterator_result_read_typed:
  iterator_result_typed tyv r /\ read_result cx r st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  case res of INL v => value_has_type tyv v | INR _ => T
Proof
  strip_tac >> drule read_result_state >> strip_tac >> gvs[] >>
  Cases_on `r` >> gvs[iterator_result_typed_def]
  >- gvs[read_result_def, return_def, no_type_error_result_def] >>
  rename1 `PlaceR p` >> Cases_on `p` >> gvs[iterator_result_typed_def] >>
  Cases_on `res` >> simp[no_type_error_result_def]
  >- (gvs[read_result_def, read_place_def] >>
      drule_all read_storage_slot_well_typed_value >> simp[]) >>
  gvs[read_result_def, read_place_def, read_storage_slot_def, bind_def] >>
  Cases_on `b` >>
  gvs[get_storage_backend_def, get_transient_storage_def, get_accounts_def,
      bind_def, return_def, lift_option_def, raise_def, option_CASE_rator, AllCaseEqs()]
QED

Theorem switch_BoolV_live_empty_scope_post:
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

Theorem switch_BoolV_live_post:
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

Theorem conditional_result_live_typed:
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

Theorem optional_read_result_live_typed:
  state_well_typed st /\ eval_result_typed (env,cx,st) pv (Type ty) /\
  live_memory_result st pv /\
  (if flag then bind (read_result cx pv) (\v. return (Value v))
   else return pv) st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  (case res of INL out => eval_result_typed (env,cx,st') out (Type ty) /\
                         live_memory_result st' out | INR _ => T)
Proof
  Cases_on `flag`
  >- (strip_tac >> Cases_on `read_result cx pv st` >>
      rename1 `read_result cx pv st = (rr,rs)` >>
      drule_all live_result_read_typed >> strip_tac >> gvs[] >>
      Cases_on `rr` >>
      gvs[bind_def, return_def, eval_result_typed_def,
          value_runtime_typed_def, live_memory_result_def, no_type_error_result_def]) >>
  simp[return_def] >> rpt strip_tac >> gvs[no_type_error_result_def]
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
Theorem annassign_statement_sound_from_expr_ih:
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
       IS_SOME (FLOOKUP env_body.var_assignable id)) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = id) /\
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
  first_x_assum drule_all >> simp[]
  >~ [`stmts_no_control_escape fn_body`]
  >- (strip_tac >> qexistsl [`env_body`, `ret_tv`, `env_after`] >>
      simp[] >> metis_tac[]) >>
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

Theorem intcall_env_body_consistency_for_defaults:
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
  ho_match_mp_tac
    (legacyInduction.mutual_ind_from_ops
       (TypeBase.set_induction_of ``:stmt``)) >>
  rw[stmt_no_fallthrough_def, evaluate_def, bind_def, return_def, raise_def,
     pairTheory.UNCURRY, finally_def, ignore_bind_def, switch_BoolV_def, AllCaseEqs()] >>
  (fn g =>
    if can (find_term (fn t => is_const t andalso #Name (dest_thy_const t) = "Raise")) (snd g)
    then (rename1 `Raise reason` >> Cases_on `reason`) g
    else if can (find_term (fn t => is_const t andalso #Name (dest_thy_const t) = "Return")) (snd g)
    then (rename1 `Return opt_e` >> Cases_on `opt_e`) g
    else all_tac g) >>
  gvs[evaluate_def, bind_def, return_def, raise_def,
      pairTheory.UNCURRY, COND_RATOR, AllCaseEqs()]
  >- metis_tac[expr_no_fallthrough_no_success] >>
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
  imp_res_tac read_result_no_control >> gvs[no_control_exc_def] >>
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
  ho_match_mp_tac
    (legacyInduction.mutual_ind_from_ops
       (TypeBase.set_induction_of ``:stmt``)) >>
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
    st'.accounts = st.accounts /\ st'.outcomes = st.outcomes
Proof
  rw[acquire_nonreentrant_lock_def, ignore_bind_def, record_storage_event_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED
Theorem release_nonreentrant_lock_accounts[local]:
  !addr slot st res st'.
    release_nonreentrant_lock addr slot st = (res, st') ==>
    st'.accounts = st.accounts
Proof
  rw[release_nonreentrant_lock_def, ignore_bind_def, record_storage_event_def, bind_def, ignore_bind_def,
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

Theorem intcall_cleanup_after_pop_preserves_frame:
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

Theorem intcall_lock_state_preserves_frame:
  !cx nr is_view st lock_st.
    (if nr then
       case cx.nonreentrant_slot of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => do
             acquire_nonreentrant_lock cx.txn.target slot
               (is_view \/ cx.txn.is_static);
             if is_view then return () else check_not_static cx
           od
     else return ()) st = (INL (),lock_st) ==>
    lock_st.scopes = st.scopes /\
    lock_st.immutables = st.immutables /\
    lock_st.accounts = st.accounts /\
    lock_st.outcomes = st.outcomes
Proof
  rpt strip_tac >>
  Cases_on `nr` >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  gvs[raise_def, ignore_bind_def, bind_def, return_def, COND_RATOR,
      AllCaseEqs()] >>
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
       | SOME slot => do
             acquire_nonreentrant_lock cx.txn.target slot
               (is_view \/ cx.txn.is_static);
             if is_view then return () else check_not_static cx
           od
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
       | SOME slot => do
             acquire_nonreentrant_lock cx.txn.target slot
               (is_view \/ cx.txn.is_static);
             if is_view then return () else check_not_static cx
           od
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
       | SOME slot => do
             acquire_nonreentrant_lock cx.txn.target slot
               (is_view \/ cx.txn.is_static);
             if is_view then return () else check_not_static cx
           od
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
       | SOME slot => do
             acquire_nonreentrant_lock cx.txn.target slot
               (is_view \/ cx.txn.is_static);
             if is_view then return () else check_not_static cx
           od
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

Theorem for_body_decompose_any:
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
Theorem for_body_decompose_for_cons_pushed:
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


Theorem for_cons_pushed_state_well_typed:
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
      >- (simp[default_value_well_typed]) >>
      metis_tac[ALOOKUP_sparse_has_type])
QED

Theorem array_iterator_results_typed:
  state_well_typed st /\ eval_result_typed (env,cx,st) pv (Type (ArrayT ty bd)) /\
  live_memory_result st pv /\ env.type_defs = get_tenv cx /\
  array_iterator_results cx (ArrayT ty bd) pv st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  case res of
  | INL rs => ?tyv. evaluate_type env.type_defs ty = SOME tyv /\
                    EVERY (iterator_result_typed tyv) rs
  | INR _ => T
Proof
  strip_tac >>
  drule array_iterator_results_state >> strip_tac >> gvs[] >>
  Cases_on `?tr slot etv bd'. pv = PlaceR (StoragePlace tr slot (ArrayTV etv bd'))`
  >- (
    gvs[eval_result_typed_def, runtime_place_typed_def, place_type_value_def,
        return_def] >>
    drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
    qpat_x_assum `array_iterator_results _ _ _ _ = _` mp_tac >>
    simp[array_iterator_results_storage] >>
    Cases_on `bd` >> Cases_on `tr` >>
    simp[bind_def, ignore_bind_def, result_array_length_def,
         get_storage_backend_def, get_transient_storage_def, get_accounts_def,
         check_def, assert_def, return_def, raise_def, LET_THM, AllCaseEqs()] >>
    rw[] >>
    gvs[no_type_error_result_def, EVERY_GENLIST, iterator_result_typed_def,
        well_formed_type_value_def]) >>
  gvs[array_iterator_results_copy] >>
  qpat_x_assum `_ st = (res,st)` mp_tac >>
  simp[bind_def] >>
  Cases_on `read_result cx pv st` >>
  rename1 `read_result cx pv st = (mat_res, st2)` >>
  drule_all live_result_read_typed >> strip_tac >> gvs[] >>
  reverse (Cases_on `mat_res`) >> gvs[no_type_error_result_def]
  >- (strip_tac >> gvs[]) >>
  rename1 `read_result cx pv st = (INL v, st)` >>
  gvs[value_runtime_typed_def] >>
  drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
  simp[lift_option_type_def] >>
  `?eo. extract_elements (ArrayTV elem_tv bd) v = eo` by simp[] >>
  Cases_on `eo` >> simp[raise_def, return_def, no_type_error_result_def] >>
  strip_tac >> gvs[EVERY_MAP, iterator_result_typed_def] >>
  Cases_on `v` >> gvs[extract_elements_def, value_has_type_def] >>
  rename1 `ArrayV av` >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule extract_elements_well_typed >>
  qexists_tac `av` >> qexists_tac `bd` >> simp[] >>
  conj_tac >- metis_tac[evaluate_type_well_formed_type_value] >>
  simp[extract_elements_def]
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
Theorem iterator_range_tail_eval_sound:
  !type_defs expr_ty tyv i1 i2 range_res st st_tail res st_final.
    evaluate_type type_defs expr_ty = SOME tyv /\
    value_has_type tyv (IntV i1) /\
    value_has_type tyv (IntV i2) /\
    lift_sum (get_range_limits (IntV i1) (IntV i2)) st = (range_res, st_tail) /\
    (case range_res of
     | INL rl => return (GENLIST (\n. Value (IntV (FST rl + &n))) (SND rl)) st_tail
     | INR err => raise err st_tail) = (res, st_final) ==>
    st_final = st /\
    no_type_error_result res /\
    (case res of
     | INL vs => ?tyv'. evaluate_type type_defs expr_ty = SOME tyv' /\ EVERY (iterator_result_typed tyv') vs
     | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  drule lift_sum_state >> strip_tac >> gvs[] >>
  Cases_on `range_res` >> gvs[return_def, raise_def]
  >- (
    rename1 `lift_sum (get_range_limits (IntV i1) (IntV i2)) st = (INL rl,st)` >>
    qspecl_then [`tyv`, `i1`, `i2`, `rl`, `st`] mp_tac iterator_range_tail_sound >>
    simp[no_type_error_result_def, EVERY_GENLIST, iterator_result_typed_def]) >>
  qpat_x_assum `lift_sum _ _ = _` mp_tac >>
  simp[lift_sum_def, get_range_limits_def, return_def, raise_def] >>
  Cases_on `i1 <= i2` >> gvs[return_def, raise_def, no_type_error_result_def]
QED


(* The trusted history is only the prefix created while a place is live. *)
Definition typed_scope_transition_def:
  typed_scope_transition st st' <=>
    ?events. scope_pop_trace st.scopes events st'.scopes /\
      EVERY (\ev. entry_pop_event_valid (SND ev)) events
End

Theorem lookup_global_live:
  lookup_global cx src id st = (res,st') ==>
  (case res of INL pv => live_memory_result st' pv | INR _ => T)
Proof
  simp[lookup_global_def, ignore_bind_def, record_storage_event_def, bind_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
      var_decl_info_CASE_rator, bind_def, lift_option_type_def, return_def,
      raise_def, AllCaseEqs(), live_memory_result_def]
QED

Theorem live_memory_result_fresh:
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

Theorem typed_scope_transition_scopes:
  st'.scopes = st.scopes ==> typed_scope_transition st st'
Proof
  simp[typed_scope_transition_def] >> strip_tac >>
  qexists_tac `[]` >> simp[scope_pop_trace_def]
QED

Theorem typed_scope_transition_refl:
  typed_scope_transition st st
Proof
  simp[typed_scope_transition_def] >> qexists_tac `[]` >>
  simp[scope_pop_trace_def]
QED

Theorem typed_scope_transition_trans:
  typed_scope_transition st middle /\ typed_scope_transition middle st' ==>
  typed_scope_transition st st'
Proof
  simp[typed_scope_transition_def] >> rpt strip_tac >>
  drule_all typed_scope_trace_append >> metis_tac[]
QED

Theorem pop_place_typed_transition:
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

Theorem eval_result_typed_transport:
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

Theorem writable_place_result_transport:
  typed_scope_transition st st' /\
  vyperImmutableMetadataFrame$immutable_metadata_frame st st' /\
  writable_place_result cx st pv ==> writable_place_result cx st' pv
Proof
  simp[typed_scope_transition_def] >> rpt strip_tac >>
  drule_all writable_place_result_frame >> simp[]
QED

Theorem live_memory_result_transport:
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

Theorem exprs_runtime_typed_slices:
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

Theorem read_live_place_success_type:
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
  simp[live_memory_result_def, extend_place_def, ignore_bind_def, record_storage_event_def, bind_def, ignore_bind_def,
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
    (gvs[extend_place_def, ignore_bind_def, record_storage_event_def, bind_def, ignore_bind_def, lift_sum_def,
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
  >- (gvs[extend_place_def, ignore_bind_def, record_storage_event_def, bind_def, return_def, AllCaseEqs()] >>
      drule extend_storage_place_live >> simp[])
  >- metis_tac[extend_live_memory_typed_success] >>
  gvs[extend_place_def, ignore_bind_def, record_storage_event_def, bind_def, ignore_bind_def, return_def,
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

Theorem transported_typed_result_extend_live:
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
  gvs[select_result_def, extend_place_def, ignore_bind_def, record_storage_event_def, bind_def, lift_option_type_def,
      return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  Cases_on `sb` >> gvs[extend_place_def, ignore_bind_def, record_storage_event_def, bind_def, lift_option_type_def,
      return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  rename1 `HashMapRef tr slot kt value_ty` >> Cases_on `value_ty` >>
  gvs[bind_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def]
QED

Theorem extend_typed_result_live:
  state_well_typed st /\ eval_result_typed (env,cx,st) bp vt /\
  live_memory_result st bp /\
  extend_place cx bp sb st = (INL pv,u) ==>
  live_memory_result u pv
Proof
  rpt strip_tac >> Cases_on `bp`
  >- gvs[extend_place_def, ignore_bind_def, record_storage_event_def, raise_def]
  >- (Cases_on `vt` >> gvs[eval_result_typed_def] >>
      drule_all extend_live_place_typed_success >> simp[]) >>
  Cases_on `sb` >> gvs[extend_place_def, ignore_bind_def, record_storage_event_def, raise_def] >>
  rename1 `HashMapRef tr slot kt value_ty` >> Cases_on `value_ty` >>
  gvs[extend_place_def, ignore_bind_def, record_storage_event_def, bind_def, lift_option_type_def, return_def,
      raise_def, AllCaseEqs(), live_memory_result_def]
QED

Theorem extend_live_place_attribute_no_type_error:
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
  >- (gvs[runtime_place_typed_storage, extend_place_def, ignore_bind_def, record_storage_event_def] >>
      drule extend_storage_place_attribute_ready >>
      disch_then (qspecl_then [`b`, `st`, `c`, `cx`] strip_assume_tac) >>
      gvs[bind_def, return_def, no_type_error_result_def]) >>
  gvs[extend_place_def, ignore_bind_def, record_storage_event_def, bind_def, ignore_bind_def, AllCaseEqs(),
      return_def, no_type_error_result_def] >>
  TRY (rename1 `read_place cx loc st = (INR err,st')` >>
       drule_all read_place_typed_error >> simp[] >> NO_TAC) >>
  drule_all read_live_place_success_type >> strip_tac >>
  drule_all evaluate_subscripts_attribute_ready >> strip_tac >>
  gvs[lift_sum_def, return_def]
QED

Theorem array_subscript_place_check:
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
  rpt strip_tac >> gvs[] >>
  fs[no_type_error_result_def, Once well_formed_type_value_def] >>
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

Theorem extend_live_array_place_sound:
  state_well_typed st /\ runtime_place_typed cx st p (ArrayTV etv bd) /\
  live_memory_result st (PlaceR p) /\
  extend_place cx (PlaceR p) (ValueSubscript (IntV i)) st = (res,st') ==>
  no_type_error_result res /\
  case res of INL pv => ?q. pv = PlaceR q /\ runtime_place_typed cx st' q etv | INR err => T
Proof
  rpt gen_tac >> strip_tac >>
  `place_type_value cx p st = (INL (ArrayTV etv bd),st)` by
    gvs[runtime_place_typed_def] >>
  Cases_on `p`
  >- (gvs[runtime_place_typed_storage, extend_place_def, ignore_bind_def, record_storage_event_def, bind_def, AllCaseEqs()] >>
      drule_all extend_storage_array_place_sound >>
      gvs[return_def, no_type_error_result_def] >> metis_tac[]) >>
  gvs[extend_place_def, ignore_bind_def, record_storage_event_def, bind_def, ignore_bind_def, return_def,
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

Theorem extend_live_tuple_place_sound:
  state_well_typed st /\ runtime_place_typed cx st p (TupleTV tvs) /\
  live_memory_result st (PlaceR p) /\
  subscript_type (TupleTV tvs) (ValueSubscript (IntV i)) = SOME etv /\
  extend_place cx (PlaceR p) (ValueSubscript (IntV i)) st = (res,st') ==>
  no_type_error_result res /\
  case res of INL pv => ?q. pv = PlaceR q /\ runtime_place_typed cx st' q etv | INR err => T
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (`place_type_value cx p st = (INL (TupleTV tvs),st)` by
        gvs[runtime_place_typed_def] >>
      Cases_on `p`
      >- (gvs[runtime_place_typed_storage, extend_place_def, ignore_bind_def, record_storage_event_def, bind_def, AllCaseEqs()] >>
          drule_all extend_storage_tuple_place_sound >>
          gvs[return_def, no_type_error_result_def]) >>
      gvs[extend_place_def, ignore_bind_def, record_storage_event_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()] >>
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

Theorem subscript_vtype_well_formed_stmt:
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

Theorem type_place_target_well_formed_vtype_stmt:
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
  (* drop the non-integer index types before unfolding the rest *)
  Cases_on `expr_type e` >> gvs[is_int_type_def] >>
  gvs[evaluate_type_def, AllCaseEqs(), value_result_typed_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  drule_all extend_live_array_place_sound >> strip_tac >> simp[] >>
  Cases_on `res` >> gvs[] >> simp[eval_result_typed_def] >> metis_tac[]
QED

Theorem extend_target_hashmap_place_sound:
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
      extend_place_def, ignore_bind_def, record_storage_event_def, bind_def, lift_option_type_def, return_def, raise_def,
      AllCaseEqs()] >>
  simp[no_type_error_result_def, eval_result_typed_def, runtime_place_typed_def,
       place_type_value_def, return_def] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

Theorem extend_target_subscript_place_sound:
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
