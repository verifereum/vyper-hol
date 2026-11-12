(* The value judgment of the full family from its vv judgment: lower_value
   is compile_expr then unwrap_value, whose code reads no GAS.  The full
   twin of exprPtrUnwrap's expr_sim_ptr_of_vv.  Admitted until the shared
   joint unwrap step on finite horizons (bodyFullUnwrap) lands.
 *
 * TOP-LEVEL: expr_sim_full_of_vv
 *)
Theory bodyFullOfVV
Ancestors
  bodySimFull loweringPosts compileEnv valueEncoding vyperTyping
  vyperInterpreter vyperState vyperAST

Theorem expr_sim_full_of_vv:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es rty.
    post_value_type cenv e = expr_type e /\
    (!rt. evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
          ~is_word_type (expr_type e) ==>
          type_memory_bytes cenv (expr_type e) = type_memory_size rt /\
          type_memory_size rt < 2**64) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
    (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
       read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty e es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty e es
Proof
  cheat
QED
