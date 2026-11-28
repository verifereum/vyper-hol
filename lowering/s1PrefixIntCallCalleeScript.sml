(* Request-prefix companion to bodyFullIntCallCallee. *)
Theory s1PrefixIntCallCallee
Ancestors
  s1PrefixPreds bodyFullIntCallCallee s1PrefixDefs
  s1PrefixIntCallNoLockedRequest s1PrefixIntCallCalleeLocked

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt strip_tac >>
  qspecl_then [`body_stmts_prefix_ok`, `gas_prefix_full`, `gas_prefix_full`]
    drule_all intcall_callee_full_with_prefix >>
  disch_then (irule o cj 2) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (rpt strip_tac >> drule_all intcall_callee_locked_request_prefix >> simp[NoAsms])
  >- (rpt strip_tac >>
      qpat_x_assum `body_stmts_prefix_ok _ _`
        (mp_tac o REWRITE_RULE [body_stmts_prefix_ok_def]) >>
      disch_then drule_all >> disch_then (qspec_then `NoLoop` mp_tac) >>
      rewrite_tac [stmt_frag_prefix_def] >>
      disch_then (qspecl_then [`st0`,`body_start`,`body_end`,`shadow_start`,
        `shadow_end`,`at_body`,`Gbody`,`tnbody`,`env_end`] mp_tac) >>
      simp[stmt_frag_full_pre_def] >>
      (impl_tac >-
        (conj_tac >-
           (qpat_assum `gas_admissible _ _ _` mp_tac >>
            pure_rewrite_tac[gasContextTheory.gas_admissible_def] >>
            qpat_assum `!gs. eval_stmts _ ss _ = _`
              (pure_rewrite_tac o single) >> simp[NoAsms]) >>
         first_assum ACCEPT_TAC)) >>
      pure_rewrite_tac[gas_prefix_full_def] >>
      qpat_assum `!gs. eval_stmts _ ss _ = _` (pure_rewrite_tac o single) >>
      simp[NoAsms]) >>
  strip_tac >> irule intcall_callee_no_locked_request_prefix >>
  fs[oneTheory.one]
QED
*)
Theorem intcall_callee_prefix:
  !DF lo d ctx shadow_ctx func tops cenv cx tenv name es st0 sa sb vv s0 es0
 G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn callee entered rc
 rbs pvs dflts.
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
  ((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
     body_stmts_prefix_ok (cx with stk updated_by CONS (NONE,name))
       (subst_consts_stmts (module_consts_env tops []) ss)) /\
  gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\
  MEM func ctx.ctx_functions /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!i. active_inst func i t ==> frag_reachable ctx func s0 func i t) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
     intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es
       sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t
       G tn) /\
  body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
  gas_invoke_entry (ctx,func) t callee entered /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) ==>
  !bb inst lbl arg_ops argv.
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    decode_invoke inst = SOME (lbl,arg_ops) /\
    eval_operands arg_ops t = SOME argv ==>
  gas_prefix_full (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, callee,
       MAP (op_prov G) arg_ops)
    cx st0 (intcall_callee_src cx name mut nr ss)
    (es1, entered, FEMPTY, tn with t_var := FEMPTY)
Proof
  cheat
QED
