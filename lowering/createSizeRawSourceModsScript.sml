Theory createSizeRawSourceMods
Ancestors
  createSizeRawSource createExprSizeExitDefsMods
  exprBodyPreProps exprSimHypsDefs exprSimHyps exprSimSource allocLimits supportedExprTraverse
  exprSimMemorySource vyperState vyperValue vyperTyping vyperAST
  vyperStatePreservation
  vyperTypeSystem vyperTypeCallGraph vyperInterpreter vyperStorageTrace
  vyperCreate gasOutcomeFull loweringPosts list rich_list
  bodyFullPostsMods bodySimStmtFacts createCtorSnapshotTypingMods vyperTypeExprSoundness valueLoadProps

Theorem create_raw_read_bytes_mods:
  expr_body_pre_mods mods ce cx env e es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,p) /\
  vv_post_mods H ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u ==>
  ?code. LENGTH code <= n /\
    read_result cx tv p = (INL (BytesV code),p) /\
    read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := [])
Proof
  strip_tac >>
  `?v. read_result cx tv (p with gas_obs := []) = (INL v,p with gas_obs := [])` by
    (fs[vv_post_mods_def] >> Cases_on `vv` >> fs[vv_holds_mods_def, vv_holds_def] >>
     Cases_on `p'.ptr_location` >>
     fs[vv_holds_def, storage_holds_def, immutable_holds_mods_def, immutable_holds_def]) >>
  `read_result cx tv p = (INL v,p)` by
    (drule read_result_gas_obs >> disch_then (qspec_then `p.gas_obs` mp_tac) >> simp[]) >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  `vyperState$bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,p)` by
    simp[vyperStateTheory.bind_def] >>
  `value_runtime_typed env (expr_type e) v` by
    (drule_all (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >> simp[]) >>
  gvs[value_runtime_typed_def] >>
  drule evaluate_type_base_identity >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def]
QED
