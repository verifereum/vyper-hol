Theory createSizeRawSourceMods
Ancestors
  createSizeRawSource createExprSizeExitDefsMods
  exprBodyPreProps exprSimHypsDefs exprSimHyps exprSimSource allocLimits supportedExprTraverse
  exprSimMemorySource vyperState vyperValue vyperTyping vyperAST
  vyperStatePreservation
  vyperTypeSystem vyperTypeCallGraph vyperInterpreter vyperStorageTrace
  vyperCreate gasOutcomeFull loweringPosts list rich_list

Theorem create_raw_read_bytes_mods:
  expr_body_pre_mods mods ce cx env e es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,p) /\
  vv_post_mods H ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u ==>
  ?code. LENGTH code <= n /\
    read_result cx tv p = (INL (BytesV code),p) /\
    read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := [])
Proof
  cheat
QED
