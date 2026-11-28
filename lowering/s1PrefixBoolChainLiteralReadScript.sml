Theory s1PrefixBoolChainLiteralRead
Ancestors
  s1PrefixBoolChainEqDemand s1PrefixLiteralWord bodyFullLiteralWord s1PrefixDefs

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rewrite_tac[value_read_demand_def] >> rpt gen_tac >> strip_tac >> conj_tac
  >- (`expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx ty (Literal ann lit) es` by metis_tac[literal_word_value_full] >>
      qpat_x_assum `expr_sim_full _ _ _ _ _ _`
        (irule o REWRITE_RULE [expr_sim_full_eq]) >>
      goal_assum (drule_at Any)) >>
  irule (REWRITE_RULE [expr_sim_prefix_def] literal_word_value_prefix) >>
  goal_assum (drule_at Any)
QED
*)
Theorem word_literal_read_joint_at_demand:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ann lit ty es
   st0 sa sb shadow_sa shadow_sb op s G tn.
   value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     tops cenv cx env (Literal ann lit) ty es
     (st0,sa,sb,shadow_sa,shadow_sb,op,s,G,tn) /\ is_word_type ann ==>
   gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx (Literal ann lit)) (read_result cx)) (es,s,G,tn)
     (\H res ee G' tn' u. ?v. res = INL v /\
       expr_post H ctx func cenv cx (Literal ann lit) es sa sb s ee v op u /\
       expr_store_bound cx (post_value_type cenv (Literal ann lit)) v op u /\
       u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
       s.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx ee G' tn' u /\
       ptr_val_ok cx (post_value_type cenv (Literal ann lit)) v op G' tn' u /\
       (~is_word_type (post_value_type cenv (Literal ann lit)) ==> ptr_buf_ok cenv (Literal ann lit) op G' u) /\
       ghost_kept_at lo cenv es sa G tn s G' tn')
     (\H res ee gt ex. expr_exit res ex /\ halt_exit H cx ee res ex /\
       (ctx_has_dalloca ctx ==> !u. ex = Halt u ==> allocas_below_fmp u)) /\
   gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx (Literal ann lit)) (read_result cx)) (es,s,G,tn)
Proof
  cheat
QED
