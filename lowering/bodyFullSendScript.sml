(*
 * send over the finite-horizon joint judgment: the word arguments, the
 * CALL and the success ASSERT share one origin/memory/pointer witness.
 *
 * TOP-LEVEL:
 *   send_expr_sim_full    -- the value judgment of a send call
 *   send_expr_vv_sim_full -- its vv judgment
 *)
Theory bodyFullSend
Ancestors
  bodyFullExprGeneric bodyFullShared bodyFullPreds bodySimFull
  gasOutcomeFullCompose gasOutcomeFull fragGasSeqPtr fragGasEmitCtrl
  gasShadowCompile gasShadowState gasShadow
  exprSendPtr bodyMemSend exprSimSend exprSimHypsDefs bodySim
  exprLowering vyperAST vyperInterpreter list

val _ = Parse.hide "body";

Theorem send_expr_sim_full:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ty ann
   has_gas args dflt es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
    body_exprs_full_ok cx args ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (Send has_gas) args dflt) es
Proof
  cheat
QED

Theorem send_expr_vv_sim_full:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ty ann
   has_gas args dflt es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
    body_exprs_full_ok cx args ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (Send has_gas) args dflt) es
Proof
  cheat
QED
