(* The attribute read over the finite-horizon joint judgments: the base's
   value judgment, then one ADD of the field offset, with the source GAS
   marks, memory posts and pointer ghosts on one witness at (DF H, lo).
   The value judgment comes from the vv one by bodyFullOfVV.
 *
 * TOP-LEVEL:
 *   attribute_vv_sim_full -- the vv judgment of e.fld from that of e
 *   attribute_expr_full_ok -- body_expr_full_ok of e.fld from that of e
 *)
Theory bodyFullAttribute
Ancestors
  bodyFullOfVV bodyFullPreds bodySimFull exprSimAttribute exprSimHypsDefs gasShadow
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

Theorem attribute_expr_full_ok:
  !cx v9 e id. body_expr_full_ok cx e ==> body_expr_full_ok cx (Attribute v9 e id)
Proof
  cheat
QED
