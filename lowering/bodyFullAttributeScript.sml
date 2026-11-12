(* The attribute read over the finite-horizon joint judgments: the base's
   value judgment, then one ADD of the field offset, with the source GAS
   marks, memory posts and pointer ghosts on one witness at (DF H, lo).
   The value judgment comes from the vv one through the shared unwrap step,
   taken here as the premise expr_sim_full_of_vv until bodyFullExprGeneric
   states it.
 *
 * TOP-LEVEL:
 *   attribute_vv_sim_full -- the vv judgment of e.fld from that of e
 *   attribute_expr_full_ok -- body_expr_full_ok of e.fld from that of e
 *)
Theory bodyFullAttribute
Ancestors
  bodyFullPreds bodySimFull exprSimAttribute exprSimHypsDefs gasShadow
  loweringPosts compileEnv valueEncoding vyperTyping
  vyperInterpreter vyperState vyperAST

val _ = Parse.hide "body";

Theorem attribute_vv_sim_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann obj fld es.
    expr_body_pre cenv cx env (Attribute ann obj fld) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty obj es ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Attribute ann obj fld) es
Proof
  cheat
QED

(* The premise is the construct-free vv-to-value step (the full twin of
   expr_sim_ptr_of_vv); it lands in bodyFullExprGeneric. *)
Theorem attribute_expr_full_ok:
  (!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es rty.
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
       cenv cx ty e es) ==>
  !cx v9 e id. body_expr_full_ok cx e ==> body_expr_full_ok cx (Attribute v9 e id)
Proof
  cheat
QED
