(* Request-prefix companion to bodyFullTargetSubscript. *)
Theory s1PrefixTargetSubscript
Ancestors
  s1PrefixPreds bodyFullTargetSubscript s1PrefixDefs

Theorem target_subscript_sim_prefix:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_base_target_full_ok cx (SubscriptTarget bt e) /\
  body_base_target_prefix_ok cx (SubscriptTarget bt e) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  target_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt es /\
  subscript_tail_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt e es /\
  (!st0 vt sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env bt = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target bt)
        shadow_sa = (r, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_base_place cx bt) target_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_prefix_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cx st0 (eval_base_place cx bt) (es, s0, G0, tn0)) /\
  (!st0 vt bvt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
     mid1 t1 G1 tn1 mid2 t2 G2 tn2.
      type_place_target env bt = SOME bvt /\
      type_place_target env (SubscriptTarget bt e) = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (rb, sm) /\
      lower_value compile_expr cenv (expr_type e) e sm = (iop, sn) /\
      compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa =
        (r, sb) /\
      fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t2) /\
      local_ptrs_reserved cenv sa /\
      sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      expr_sim_inv cenv cx env mid1 /\ mid1.gas_obs = [] /\
      eval_base_place cx bt (es with gas_obs := base_gas) =
        (INL pv, mid1) /\
      bind (eval_expr cx e) (read_result cx)
        (mid1 with gas_obs := index_gas) = (INL v, mid2) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
      gas_admissible (extend_place cx pv (ValueSubscript v))
        target_res_ok mid2 /\
      storage_trace_domain cx st0 mid2.storage_trace /\ mid2.gas_obs = [] /\
      ~t1.vs_halted /\ ~t2.vs_halted /\
      t1.vs_current_bb = sm.cs_current_bb /\
      t1.vs_inst_idx = LENGTH sm.cs_current_insts /\
      t2.vs_current_bb = sn.cs_current_bb /\
      t2.vs_inst_idx = LENGTH sn.cs_current_insts /\
      alloca_history func t1 /\ alloca_history func t2 /\
      s0.vs_alloca_next <= t1.vs_alloca_next /\
      t1.vs_alloca_next <= t2.vs_alloca_next /\
      (!H. valid_horizon cx st0 H mid2.storage_trace ==>
        target_post H ctx func cenv cx es sa sm s0 mid1 pv bvt rb t1 /\
        ghost_inv_at (DF H) lo d cenv cx mid1 G1 tn1 t1 /\
        target_ptr_ok cenv pv rb G1 tn1 t1 /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
        expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\
        expr_store_bound cx (expr_type e) v iop t2 /\
        ghost_inv_at (DF H) lo d cenv cx mid2 G2 tn2 t2 /\
        ptr_val_ok cx (post_value_type cenv e) v iop G2 tn2 t2 /\
        (~is_word_type (post_value_type cenv e) ==>
         ptr_buf_ok cenv e iop G2 t2) /\
        ghost_kept_at lo cenv mid1 sm G1 tn1 t1 G2 tn2) ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (extend_place cx pv (ValueSubscript v)) (mid2,t2,G2,tn2)) ==>
    !st0 vt sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env (SubscriptTarget bt e) = SOME vt /\
      compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (r, sb) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target (SubscriptTarget bt e))
        shadow_sa = (r, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_prefix_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cx st0 (eval_base_place cx (SubscriptTarget bt e)) (es, s0, G0, tn0)
Proof
  cheat
QED
