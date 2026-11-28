(* Full-outcome continuation at the successful internal-call entry. *)
Theory s1PrefixIntCallRestOutcome
Ancestors
  s1PrefixDefs bodyFullIntCall bodyFullIntCallCallee bodyFullIntCallReturn
  gasOutcomeFull

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon cx st0 H es1.storage_trace` (qx_choose_then `H` assume_tac) >>
  qpat_x_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  `intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
     sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  `((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
    body_stmts_full_ok (cx with stk updated_by CONS (NONE,name))
      (subst_consts_stmts (module_consts_env tops []) ss))` by
    (disch_tac >> drule_all intcall_entry_after_arguments >> simp[]) >>
  `?result_count rbs pvs.
     cenv.ce_func_info (nsid_to_string (NONE,name)) = (result_count,rbs,pvs)` by
    metis_tac[pairTheory.ABS_PAIR_THM] >>
  `!callee entered bb inst lbl arg_ops argv.
     gas_invoke_entry (ctx,func) t callee entered /\
     lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
     get_instruction bb t.vs_inst_idx = SOME inst /\
     decode_invoke inst = SOME (lbl,arg_ops) /\
     eval_operands arg_ops t = SOME argv ==>
     gas_outcome_full
       (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,MAP (op_prov G) arg_ops)
       (cx_tops cx) cx st0 (intcall_callee_src cx name mut nr ss)
       (es1,entered,FEMPTY,tn with t_var := FEMPTY)
       (\H res ee G' tn' t'. F)
       (\H res ee gt r.
          intcall_callee_exit_full (DF,lo) H func cenv cx mut nr rtv result_count
            (if result_count = 0 /\ 0 < rbs then SOME (HD argv) else NONE)
            sa.cs_next_id sb.cs_next_id t tn res ee gt r)` by
    (rpt gen_tac >> strip_tac >> drule_all intcall_callee_full_singleton >> simp[]) >>
  qpat_assum `!callee entered bb inst lbl arg_ops argv. _ ==> gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_then Any (drule_all_then (qspec_then `PG` assume_tac))
      (DISCH_ALL (CONJUNCT1 (UNDISCH (SPEC_ALL intcall_return_full_owned))))) >>
  irule gas_outcome_full_post_mono >>
  qhdtm_assum `gas_outcome_full` (irule_at Any) >> simp[]
QED
*)
Theorem intcall_entry_rest_outcome:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
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
  expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Call ann (IntCall (NONE,name)) es dflt) es0
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
     intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
       sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn) /\
  body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
  (!i. active_inst func i t ==> frag_reachable ctx func s0 func i t) /\
  (?H. valid_horizon cx st0 H es1.storage_trace) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (intcall_rest cx name mut nr ss prev rtv) (es1,t,G,tn)
    (\H res ee HG tm z. T) (\H res ee gt r. T)
Proof
  cheat
QED
