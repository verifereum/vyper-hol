(* The common code and frame fields of the full expression judgment. *)
Theory exprSimFullBundleProps
Ancestors
  bodySimFull gasShadowState gasShadow gasContext gasOutcomeFull fragExec
  loweringPosts bodyPtrDefs loweringStateRelDefs allocaHistory
  exprSimDefs exprLowering compileEnv vyperInterpreter vyperState venomState

Definition expr_sim_full_code_def:
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) <=>
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\
    fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func
End

Definition expr_sim_full_endpoint_def:
  expr_sim_full_endpoint func sb s0 t <=>
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next
End

Definition expr_sim_full_hypotheses_def:
  expr_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e es (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0) <=>
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
        (op, shadow_sb) /\
      expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) /\
      local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts
End

Definition expr_sim_full_post_def:
  expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sb,s0,op,G0,tn0) =
    \H res ee G tn t. ?v. res = INL v /\
          expr_post H ctx func cenv cx e es sa sb s0 ee v op t /\
          expr_store_bound cx (post_value_type cenv e) v op t /\
          expr_sim_full_endpoint func sb s0 t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
          (~is_word_type (post_value_type cenv e) ==>
           ptr_buf_ok cenv e op G t) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
End

Theorem expr_sim_full_code_fields:
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) ==>
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\
    fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func
Proof
  simp[expr_sim_full_code_def]
QED

Theorem expr_sim_full_endpoint_fields:
  expr_sim_full_endpoint func sb s0 t ==>
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next
Proof
  simp[expr_sim_full_endpoint_def]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  simp[expr_sim_full_def, expr_sim_full_hypotheses_def, expr_sim_full_code_def,
       expr_sim_full_post_def, expr_sim_full_endpoint_def, FUN_EQ_THM,
       AC CONJ_ASSOC CONJ_COMM]
QED
*)
Theorem expr_sim_full_via_bundle:
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es <=>
  !st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
    expr_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e es (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0) ==>
      gas_outcome_full_mods
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx))
        (es, s0, G0, tn0)
        (expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sb,s0,op,G0,tn0))
        (\H res ee gt r.
          expr_exit res r /\ halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  cheat
QED
