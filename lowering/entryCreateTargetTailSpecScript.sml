Theory entryCreateTargetTailSpec
Ancestors
  bodyFullTargetSubscript

(* The base and index have returned at sm and sn. The outcome's slice
   starts at sn and its execution seed at t2, even though the normal
   post relates the whole subscript (sa to sb) to its starting state s0.
   In a scoped-and-cut specialization, the cut thus concerns sn to sb
   with the source/target seed (mid2,t2). *)
Definition target_subscript_tail_judgment_def:
  target_subscript_tail_judgment outcome
    (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx env bt e es <=>
    !st0 vt bvt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
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
      outcome
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0 sn sb (extend_place cx pv (ValueSubscript v))
        (mid2, t2, G2, tn2)
        (\H res ee G tn t. ?pv'. res = INL pv' /\
          target_post H ctx func cenv cx es sa sb s0 ee pv' vt r t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          target_ptr_ok cenv pv' r G tn t /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt q. expr_exit res q)
End

Theorem target_subscript_tail_judgment_full:
  target_subscript_tail_judgment (\K tops cx st0 a b. gas_outcome_full K tops cx st0)
    B ce cx env bt e es <=> subscript_tail_full B ce cx env bt e es
Proof
  PairCases_on `B` >> simp[target_subscript_tail_judgment_def, subscript_tail_full_def]
QED
