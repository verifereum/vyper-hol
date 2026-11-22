(* Request-prefix companion to bodyFullLogArgs. *)
Theory s1PrefixLogArgs
Ancestors
  s1PrefixPreds bodyFullLogArgs s1PrefixDefs

Theorem compile_log_eval_all_prefix:
  !DF lo d PG ctx shadow_ctx func shadow_func cenv cx st0 R env.
    (!e tail es. R (e::tail) es ==>
       expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx (expr_type e) e es /\
       !v es1. bind (eval_expr cx e) (read_result cx) es = (INL v, es1) ==>
         R tail es1 /\
         ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
              value_has_type tv v) /\
    (!e tail es. R (e::tail) es ==>
       expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx (expr_type e) e es) /\
    (!tail es gs. R tail es ==> R tail (es with gas_obs := gs)) /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
    !args es sa sb shadow_sa shadow_sb ops s0 G0 tn0.
      R args es /\ ~exprs_can_mutate cenv args /\
      EVERY (\e. ~expr_has_effect e) args /\
      EVERY (\e. post_value_type cenv e = expr_type e) args /\
      well_typed_exprs env args /\
      compile_log_eval_all cenv args sa = (ops, sb) /\
      compile_log_eval_all (gas_shadow_env T cenv)
        (MAP gas_shadow_expr args) shadow_sa =
        (ops, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0 /\
        !bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_exprs cx args)
        (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception))
        es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_prefix_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cx st0 (eval_exprs cx args) (es, s0, G0, tn0)
Proof
  cheat
QED
