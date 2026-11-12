(*
 * The joint (full) judgments of len, calldata length, the environment
 * items but msg.gas, the account accessors, blockhash, blobhash and
 * method_id, at every horizon (DF H, lo): source GAS origins, memory
 * posts and pointer ghosts share one witness.  bodyFullCases'
 * env_builtin_expr_full_ok is this, with body_expr_full_ok unfolded.
 *
 * TOP-LEVEL:
 *   env_builtin_sim_full
 *)
Theory bodyFullBuiltinEnv
Ancestors
  bodyFullExprGeneric bodyFullPreds bodySimFull exprSimHypsDefs exprLowering
  vyperAST list

val _ = Parse.hide "body";

Theorem env_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i /\ i <> MsgGas) \/
     (?i. bt = Acc i) \/ bt = BlockHash \/ bt = BlobHash \/ bt = MethodId) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt <> Len ==>
     body_exprs_full_ok cx args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt = Len ==>
     body_expr_full_ok cx (HD args)) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  cheat
QED
