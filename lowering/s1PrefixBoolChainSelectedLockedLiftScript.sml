(* Transport a local observation from the actual locked callee body. *)
Theory s1PrefixBoolChainSelectedLockedLift
Ancestors
  bodyFullIntCallCallee s1PrefixDefs s1PrefixIntCallCalleeLocked
  s1PrefixIntCallNoLockedRequest s1PrefixIntCallReturnPrefix

Theorem bool_chain_selected_locked_lift:
  !DF lo d ctx shadow_ctx func tops cenv cx tenv name es st0 sa sb vv s0 es0
   G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn callee entered rc
   rbs pvs dflts bb inst lbl arg_ops argv PG.
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  LENGTH args - LENGTH dflts <= LENGTH es /\
  LENGTH es <= LENGTH args /\
  ((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
     body_stmts_full_ok (cx with stk updated_by CONS (NONE,name))
       (subst_consts_stmts (module_consts_env tops []) ss)) /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  MEM func ctx.ctx_functions /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!i. active_inst func i t ==> frag_reachable ctx func s0 func i t) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
     intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
       sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn) /\
  body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
  gas_invoke_entry (ctx,func) t callee entered /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  (!H. ptr_inst_ok (DF H) lo 0 ctx func G tn inst t) /\
  (!pushed compiled body_pg dret RetQ body_ce bindings env env_after locked sf
     body_start body_end shadow_start shadow_end env_end at_body Gbody tnbody.
     pushed = cx with stk updated_by CONS (NONE,name) /\
     compiled = subst_consts_stmts (module_consts_env tops []) ss /\
     body_pg = MAP (op_prov G) arg_ops /\
     body_stmts_full_ok pushed compiled /\
     body_inv tops ctx body_ce pushed /\
     shadow_body_inv tops ctx shadow_ctx /\
     supported_stmts tops bindings compiled /\
     (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target)
        compiled ==> occurs_abi_decode_target target tops) /\
     body_const_cells_agree [(NONE,tops)] pushed env locked /\
     expr_sim_inv body_ce pushed env locked /\
     ce_locals_declared body_ce env /\ locals_alloc_ok body_ce env /\
     type_stmts env ret compiled = SOME env_after /\
     stmts_exprs_ok body_ce compiled /\
     call_evaluation_safe pushed (int_calls_stmts compiled) /\
     frame_ret_ok_full (DF,lo,dret,ctx,shadow_ctx,body_pg,callee,sf)
       pushed RetQ body_ce ret /\
     stmt_frag_full_pre (DF,lo,dret,ctx,shadow_ctx,body_pg,callee,sf)
       pushed NoLoop RetQ body_ce
       (stmts_env body_ce NoLoop ret compiled)
       (stmts_env (gas_shadow_env T body_ce) NoLoop ret (MAP gas_shadow_stmt compiled))
       (eval_stmts pushed compiled) locked
       (st0,body_start,body_end,shadow_start,shadow_end,at_body,Gbody,tnbody,env_end) ==>
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,body_pg)
       pushed st0 (eval_stmts pushed compiled) (locked,at_body,Gbody,tnbody)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (intcall_rest cx name mut nr ss prev rtv) (es1,t,G,tn)
Proof
  rpt gen_tac >> strip_tac >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
      MAP (op_prov G) arg_ops) cx st0 (intcall_callee_src cx name mut nr ss)
      (es1,entered,FEMPTY,tn with t_var := FEMPTY)` suffices_by
    (strip_tac >> irule intcall_return_request_prefix >>
     qhdtm_assum `gas_prefix_full` (irule_at Any) >>
     qpat_assum `decode_invoke _ = SOME _` (irule_at Any) >>
     qpat_assum `lookup_block _ _ = SOME _` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qspecl_then [`body_stmts_full_ok`,`gas_prefix_full`,`gas_prefix_full`]
    drule_all intcall_callee_full_with_prefix_singleton >>
  disch_then (irule o cj 2) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (rpt strip_tac >> drule_all intcall_callee_locked_request_prefix >> simp[NoAsms])
  >- suspend "body" >>
  strip_tac >> irule intcall_callee_no_locked_request_prefix >> fs[oneTheory.one]
QED

Resume bool_chain_selected_locked_lift[body]:
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `eval_stmts pushed ss` >>
  qabbrev_tac `compiled = subst_consts_stmts (module_consts_env tops []) ss` >>
  qabbrev_tac `body_pg = MAP (op_prov G) arg_ops` >>
  `gas_admissible (eval_stmts pushed compiled) (stmt_res_ok NoLoop) locked` by
    (qpat_assum `gas_admissible _ _ _` mp_tac >>
     pure_rewrite_tac[gasContextTheory.gas_admissible_def] >>
     qpat_assum `!gs. eval_stmts _ ss _ = _` (pure_rewrite_tac o single) >> simp[NoAsms]) >>
  `stmt_frag_full_pre (DF,lo,dret,ctx,shadow_ctx,body_pg,callee,sf)
     pushed NoLoop RetQ body_ce
     (stmts_env body_ce NoLoop ret compiled)
     (stmts_env (gas_shadow_env T body_ce) NoLoop ret (MAP gas_shadow_stmt compiled))
     (eval_stmts pushed compiled) locked
     (st0,body_start,body_end,shadow_start,shadow_end,at_body,Gbody,tnbody,env_end)` by
    (asm_simp_tac bool_ss [stmt_frag_full_pre_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,body_pg)
     pushed st0 (eval_stmts pushed compiled) (locked,at_body,Gbody,tnbody)` by
    qpat_assum `!pushed compiled body_pg dret. _`
      (qspecl_then [`pushed`,`compiled`,`body_pg`]
        (drule_all_then ACCEPT_TAC o SIMP_RULE bool_ss [])) >>
  qpat_x_assum `gas_prefix_full _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[gas_prefix_full_def] >>
  qpat_assum `!gs. eval_stmts _ ss _ = _` (pure_rewrite_tac o single) >> simp[NoAsms]
QED

Finalise bool_chain_selected_locked_lift
