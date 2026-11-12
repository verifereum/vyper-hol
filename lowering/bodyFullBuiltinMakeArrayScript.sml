(*
 * The joint (full) judgments of an array or tuple literal, laid out in a
 * fresh memory buffer, at every horizon (DF H, lo): source GAS origins,
 * memory posts and pointer ghosts share one witness.  bodyFullCases'
 * make_array_expr_full_ok is this, with body_expr_full_ok unfolded.
 *
 * TOP-LEVEL:
 *   make_array_sim_full
 *)
Theory bodyFullBuiltinMakeArray
Ancestors
  bodyFullPreds bodySimFull exprSimHypsDefs exprLowering vyperAST list

val _ = Parse.hide "body";

Theorem make_array_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (?t n. bt = MakeArray t n) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  cheat
QED
