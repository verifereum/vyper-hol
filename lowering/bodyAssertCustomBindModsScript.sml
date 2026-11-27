(* Use the RaiseCustom rule only after the condition reads false. *)
Theory bodyAssertCustomBindMods
Ancestors
  bodyAssertConditionPreMods bodyAssertPayloadBindMods
  bodyAssertPayloadSourceMods bodyAssertPayloadFalseActionMods
  bodyFullCustomErrorSource bodyFullIfExpReach bodyFullPredsMods
  bodyQualifiedStmtSupport vyperTypeContract vyperSubscriptOverlap
  vyperInterpreter vyperState vyperStorageFootprint finite_map
Libs
  markerLib

val assert_err = ``Assert e (AssertCustomError err)``;
val raise_err = ``Raise (RaiseCustomError err)``;
val resolve = ``!ctx cenv src tops env es bindings s ret_ty env'.
   contract_inv mods exps ctx cenv cx /\
   module_body_inv mods src tops cenv cx /\
   expr_sim_inv_mods mods cenv cx env es /\
   body_const_cells_agree_mods mods cx env es /\
   supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
   EVERY (source_body_call_supported cx) (int_calls_stmt s)``;

(* The universal contract of compile_raise_custom_frag_full_mods. *)
val raise_frag = ``
  !mods exps cx err ctx cenv src tops env es bindings ret_ty env'
    DF lo d shadow_ctx PG func shadow_func RetQ lctx.
  (!id pos kw error_tops params args.
     err = CustomError id pos kw /\
     get_module_code cx (FST id) = SOME error_tops /\
     lookup_custom_error_args_in (SND id) error_tops = SOME params /\
     order_custom_error_args params err = SOME args ==>
     body_exprs_full_ok_mods mods exps cx args) /\
  ^resolve /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
  qualified_stmt_decls_ok mods ^raise_err /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings ^raise_err /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target) ^raise_err ==>
     EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_const_cells_agree_mods mods cx env es /\
  expr_sim_inv_mods mods cenv cx env es /\
  type_stmt env ret_ty ^raise_err = SOME env' /\ stmt_exprs_ok cenv ^raise_err /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) ^raise_err /\
  call_evaluation_safe cx (int_calls_stmt ^raise_err) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty ^raise_err)
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt ^raise_err))
    (eval_stmt cx ^raise_err) es``;

Theorem compile_assert_custom_frag_full_from_raise_mods:
  ^raise_frag ==>
  !mods exps cx e err ctx cenv src tops env es bindings ret_ty env'
    DF lo d shadow_ctx PG func shadow_func RetQ lctx.
    (!s tv st id pos kw error_tops params args.
       eval_expr cx e s = (INL tv,st) /\
       err = CustomError id pos kw /\
       get_module_code cx (FST id) = SOME error_tops /\
       lookup_custom_error_args_in (SND id) error_tops = SOME params /\
       order_custom_error_args params err = SOME args ==>
       body_exprs_full_ok_mods mods exps cx args) /\
    body_expr_full_ok_mods mods exps cx e /\
    ^resolve /\
    exports_ok cx.layouts cx.txn.target mods exps /\
    IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
    qualified_stmt_decls_ok mods ^assert_err /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    supported_stmt tops bindings ^assert_err /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target) ^assert_err ==>
       EXISTS (occurs_abi_decode_target target o SND) mods) /\
    body_const_cells_agree_mods mods cx env es /\
    expr_sim_inv_mods mods cenv cx env es /\
    type_stmt env ret_ty ^assert_err = SOME env' /\ stmt_exprs_ok cenv ^assert_err /\
    ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) ^assert_err /\
    (!key. MEM (WriteAcc (StateRef key)) (accesses_stmt ^assert_err) /\
       IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
       IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
    call_evaluation_safe cx (int_calls_stmt ^assert_err) /\
    frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty ^assert_err)
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt ^assert_err))
      (eval_stmt cx ^assert_err) es
Proof
  disch_then (mk_asm "raise_frag") >> rpt gen_tac >> strip_tac >>
  `expr_type e = BaseT BoolT /\ expr_body_pre_mods mods cenv cx env e es` by
    (mp_tac (Q.INST [`reason` |-> `AssertCustomError err`]
       assert_condition_pre_active_mods) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then irule >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (BaseT BoolT) e es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
                   _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
       (FIRST o map irule o CONJUNCTS o
        SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
     simp[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> first_assum ACCEPT_TAC) >>
     qexists_tac `env` >> simp[]) >>
  irule (Q.INST [`rr` |-> `RaiseCustomError err`]
    (SPEC_ALL compile_assert_payload_frag_full_from_false_action_mods)) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac
    (SIMP_RULE (srw_ss()) [listTheory.EVERY_MEM, combinTheory.K_THM]
      (Q.INST [`ak` |-> `AssertCustomError err`, `rr` |-> `RaiseCustomError err`,
               `P` |-> `K T`] assert_payload_false_source_ready_mods)) >>
  `qualified_stmt_decls_ok mods (Raise (RaiseCustomError err))` by fs[] >>
  `stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
     (stmt_env cenv lctx ret_ty ^raise_err)
     (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt ^raise_err))
     (eval_stmt cx ^raise_err) mid` by
    (asm "raise_frag" irule >> simp[] >>
     qexistsl_tac [`bindings`,`env`,`env`,`exps`,`mods`,`src`,`tops`] >> simp[] >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!s tv st id pos kw error_tops params args. _`
           (drule_all_then ACCEPT_TAC)) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `qualified_stmt_decls_ok _ (Raise _)`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
       mid.storage_trace` by fs[storage_trace_domain_def] >>
  `alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
     s0.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  irule assert_payload_false_action_mods >> simp[] >>
  conj_tac >- (rpt strip_tac >> drule_all_then ACCEPT_TAC body_inv_no_phi_mods) >>
  conj_tac >- (rpt gen_tac >> disch_tac >> drule_then ACCEPT_TAC eval_raise_custom_non_normal) >>
  rpt (goal_assum (drule_at Any)) >>
  qexistsl_tac [`s1`,`op`] >> conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED
