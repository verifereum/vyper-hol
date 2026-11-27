(* Simulate a reason-bearing assertion using its actual false-edge Raise. *)
Theory bodyAssertReasonBindMods
Ancestors
  bodyAssertConditionPreMods bodyAssertPayloadBindMods bodyAssertPayloadSourceMods
  bodyAssertPayloadFalseActionMods bodyAssertTerminalMods bodyFullPredsMods
  bodyFullPostsMods bodyFullIfExpReach reasonSourceProps vyperSubscriptOverlap

val assert_reason = ``Assert e (AssertReason r)``;
val resolve_stmt = ``!ctx cenv src tops env es bindings s ret_ty env'.
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    expr_sim_inv_mods mods cenv cx env es /\
    body_const_cells_agree_mods mods cx env es /\
    supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
    EVERY (source_body_call_supported cx) (int_calls_stmt s)``;

Theorem compile_assert_reason_frag_full_mods:
  ^resolve_stmt /\
  (!st tv st'. eval_expr cx e st = (INL tv,st') ==> body_expr_full_ok_mods mods exps cx r) /\
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings ^assert_reason /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target) ^assert_reason ==>
     EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_const_cells_agree_mods mods cx env es /\
  expr_sim_inv_mods mods cenv cx env es /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty ^assert_reason = SOME env' /\ stmt_exprs_ok cenv ^assert_reason /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) ^assert_reason /\
  (!key. MEM (WriteAcc (StateRef key)) (accesses_stmt ^assert_reason) /\
         IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
         IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt ^assert_reason) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty ^assert_reason)
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt ^assert_reason))
    (eval_stmt cx ^assert_reason) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type e = BaseT BoolT /\ expr_body_pre_mods mods cenv cx env e es` by
    (drule assert_condition_pre_active_mods >> disch_then irule >> simp[] >>
     conj_tac >- (qexists_tac `ctx` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`bindings`,`env'`,`AssertReason r`,`ret_ty`,`src`,`tops`] >> simp[]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (BaseT BoolT) e es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
       (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM] o
        ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     qpat_assum `!df lo d pg src tops ctx sh fn shfn ce env ty es. _ ==>
                   expr_sim_full_mods _ _ _ _ _ _` irule >> simp[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  irule compile_assert_payload_frag_full_from_false_action_mods >>
  simp[] >>
  qx_genl_tac [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`s0`,`G0`,`tn0`,`op`,`s1`,
               `t1`,`entry`,`last`,`sentry`,`slast`,`marks`,`mid`,`G1`,`tn1`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac
    (SRULE [listTheory.EVERY_MEM] (Q.INST [`ak` |-> `AssertReason r`, `rr` |-> `RaiseReason r`,
                                `P` |-> `\k. T`] assert_payload_false_source_ready_mods)) >>
  `body_expr_full_ok_mods mods exps cx r` by
    (qpat_assum `!st tv st'. eval_expr cx e st = _ ==> _` (drule_then ACCEPT_TAC)) >>
  drule_all_then assume_tac compile_raise_reason_frag_full_mods >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next` by
    (rpt conj_tac >> first_assum (drule_then ACCEPT_TAC)) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa s1 s0 mid (BoolV F) op t /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> disch_tac >> conj_tac >> first_assum (drule_then ACCEPT_TAC)) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all body_inv_no_phi_mods >> simp[]) >>
  qpat_assum `!lc. stmt_frag_full_mods _ _ lc _ _ _ _ _ mid`
    (qspec_then `lctx` assume_tac) >>
  `!ee res ee'. eval_stmt cx (Raise (RaiseReason r)) ee = (res,ee') ==>
     res <> INL () /\ res <> INR BreakException /\ res <> INR ContinueException` by
    (rpt gen_tac >> disch_tac >> drule eval_raise_reason_non_normal >> simp[]) >>
  drule_all_then (irule_at Any) assert_payload_false_action_mods
QED
