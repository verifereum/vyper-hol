(*
 * The joint (full) judgments of slice, concat, calldata slices and
 * uint2str, each into a fresh memory buffer, at every horizon (DF H,
 * lo): source GAS origins, memory posts and pointer ghosts share one
 * witness.  bodyFullCases' bytestring_builtin_expr_full_ok is this, with
 * body_expr_full_ok unfolded.
 *
 * TOP-LEVEL:
 *   bytestring_builtin_sim_full
 *)
Theory bodyFullBuiltinBytestring
Ancestors
  bodyFullPreds bodySimFull exprSimHypsDefs exprLowering vyperAST list

val _ = Parse.hide "body";

Theorem bytestring_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    ((?n. bt = CalldataSlice n) \/ (?n. bt = Concat n) \/ (?n. bt = Slice n) \/
     (?n. bt = Uint2Str n)) /\
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
