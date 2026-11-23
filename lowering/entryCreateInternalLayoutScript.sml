Theory entryCreateInternalLayout
Ancestors
  bodyFullIntCallCallee bodyFullShadowBodyInv entryCreateIntervalLayout
  bodyFullIntCallDefs bodyFullPreds bodySimFull gasOutcomeFull fragGasOriginPtr
  bodyInvSplit bodyPtrDefs gasStorage gasContext vyperInterpreter
  compileEnv venomInst venomExecSemantics finite_map

Theorem create_layout_restriction[local]:
  !entry a b final.
    cs_extends entry a /\ cs_extends a b /\ cs_extends b final /\
    create_layout entry final ==> create_layout a b
Proof
  rpt gen_tac >> MATCH_ACCEPT_TAC create_layout_subinterval
QED

(* The success continuation sees layout at the actual body compile cursors.
   Entry-domain and lock-abort continuations are unchanged. *)
Theorem selected_internal_body_layout_at:
  !P DF lo d ctx shadow_ctx func tops cenv cx tenv name es st0 sa sb vv s0 es0
   G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn callee entered rc
   rbs pvs dflts.
    body_inv tops ctx cenv cx /\
    shadow_body_inv_with create_layout tops ctx shadow_ctx /\
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
      intcall_callee_selected_callbacks_with create_layout P (DF,lo,ctx,shadow_ctx,callee)
        (tops,cx,st0,name,mut,nr,ret,ss,es1) (entered,G,tn,arg_ops) ==>
      P /\ gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, callee,
         MAP (op_prov G) arg_ops)
        (cx_tops cx) cx st0 (intcall_callee_src cx name mut nr ss)
        (es1, entered, FEMPTY, tn with t_var := FEMPTY)
        (\H res ee G' tn' t'. F)
        (\H res ee gt r.
           intcall_callee_exit_full (DF, lo) H func cenv cx mut nr rtv rc
             (if rc = 0 /\ 0 < rbs then SOME (HD argv) else NONE)
             sa.cs_next_id sb.cs_next_id t tn res ee gt r)
Proof
  qspecl_then [`create_layout`, `create_layout`]
    (MATCH_ACCEPT_TAC o SIMP_RULE bool_ss [EQT_INTRO create_layout_restriction])
    intcall_callee_selected_landing_with
QED
