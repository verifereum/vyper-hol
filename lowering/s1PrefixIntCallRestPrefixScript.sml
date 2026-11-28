(* The request-prefix continuation at a successful internal-call entry. *)
Theory s1PrefixIntCallRestPrefix
Ancestors
  s1PrefixIntCallCallee s1PrefixIntCallReturnPrefix bodyFullIntCall
  bodyFullIntCallDefs bodyFullIntCallReturnSource bodyInvCodeProps
  contractInvContextProps fragGasFocus ptrSafeRun

Theorem intcall_entry_rest_prefix:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  LENGTH args - LENGTH dflts <= LENGTH es /\
  LENGTH es <= LENGTH args /\
  (!s1 vs t1 sd dvs td p rt.
     ~MEM (NONE,name) cx.stk /\
     eval_exprs cx es s1 = (INL vs,t1) /\
     eval_exprs (cx with stk updated_by CONS (NONE,name))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
       (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
     bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME p /\
     evaluate_type (get_tenv cx) ret = SOME rt /\
     (nr ==> IS_SOME cx.nonreentrant_slot) /\
     (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
     body_stmts_full_ok (cx with stk updated_by CONS (NONE,name))
       (subst_consts_stmts (module_consts_env tops []) ss)) /\
  (!s1 vs t1 sd dvs td p rt.
     ~MEM (NONE,name) cx.stk /\
     eval_exprs cx es s1 = (INL vs,t1) /\
     eval_exprs (cx with stk updated_by CONS (NONE,name))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
       (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
     bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME p /\
     evaluate_type (get_tenv cx) ret = SOME rt /\
     (nr ==> IS_SOME cx.nonreentrant_slot) /\
     (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
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
     intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
       sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn) /\
  body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
  (?H. valid_horizon cx st0 H es1.storage_trace) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (intcall_rest cx name mut nr ss prev rtv) (es1,t,G,tn)
Proof
  strip_tac >>
  `intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
      sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn` by
    (first_assum MATCH_MP_TAC >> first_assum ACCEPT_TAC) >>
  drule_then assume_tac bodySimTheory.body_inv_contract >>
  drule_then assume_tac contract_inv_singleton_source_modules >>
  drule_then strip_assume_tac body_inv_module_locations >>
  drule_then assume_tac bodyInvSplitTheory.contract_inv_immutable_section_layout >>
  `intcall_entry_full_mods (DF,lo,d) H [(NONE,tops)] NONE tops
      ctx func cenv cx tenv name es sa sb vv s0 es0 G0 tn0
      (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn` by
    asm_simp_tac bool_ss [intcall_entry_full_mods_singleton] >>
  `((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
     body_stmts_full_ok (cx with stk updated_by CONS (NONE,name))
       (subst_consts_stmts (module_consts_env tops []) ss)) /\
   ((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
     body_stmts_prefix_ok (cx with stk updated_by CONS (NONE,name))
       (subst_consts_stmts (module_consts_env tops []) ss))` by
    (conj_tac >> strip_tac >> drule_all_then ACCEPT_TAC intcall_entry_after_arguments) >>
  pop_assum strip_assume_tac >>
  `?callee entered. gas_invoke_entry (ctx,func) t callee entered` by
    (qhdtm_assum `intcall_entry_full` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[intcall_entry_full_def] >> metis_tac[]) >>
  `?bb inst lbl arg_ops argv.
     lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
     get_instruction bb t.vs_inst_idx = SOME inst /\
     inst.inst_opcode = INVOKE /\
     decode_invoke inst = SOME (lbl,arg_ops) /\
     eval_operands arg_ops t = SOME argv` by
    (qhdtm_assum `gas_invoke_entry` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[gas_invoke_entry_def] >> metis_tac[]) >>
  `!h. ptr_inst_ok (DF h) lo 0 ctx func G tn inst t` by
    (`ptr_inst_ok (DF H) lo 0 ctx func G tn inst t` by
       (drule_all_then ACCEPT_TAC intcall_entry_invoke_ptr) >>
     pop_assum mp_tac >> asm_simp_tac bool_ss [ptr_inst_ok_def]) >>
  `?rc rbs pvs. cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[pairTheory.ABS_PAIR_THM]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
      MAP (op_prov G) arg_ops) cx st0 (intcall_callee_src cx name mut nr ss)
      (es1,entered,FEMPTY,tn with t_var := FEMPTY)` by
    (drule_all_then ACCEPT_TAC intcall_callee_prefix) >>
  irule intcall_return_request_prefix >>
  qhdtm_assum `gas_prefix_full` (irule_at Any) >>
  qpat_assum `decode_invoke _ = SOME _` (irule_at Any) >>
  qpat_assum `lookup_block _ _ = SOME _` (irule_at Any) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
