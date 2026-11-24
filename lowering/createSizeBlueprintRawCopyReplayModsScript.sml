Theory createSizeBlueprintRawCopyReplayMods
Ancestors
  createSizeBlueprintRawCopyReplay createExprSizeExitDefsMods
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps fragExec fragGasOrigin fragGasOriginPtr gasExplicitSites
  gasSummary s1PrefixDefs venomExecSemantics venomInst venomState vyperState relation list
  words createMarkedPath pair bodyFullIfExpReach arithmetic exprLowering stmtLoweringMono
  vfmConstants compileEnv exprLoweringProps exprSimSource bodySimStmtFacts vyperStorageTrace
  bodyMemoryDefs exprOperandVar freshWrites rich_list exprSimHypsDefs exprSimHyps
  bodyPtrDefs loweringPosts context createSizeRawSourceMods fragGasPath vyperAST
  vyperStorageFootprint vyperValue integer_word valueEncoding createCtorSegmentArrival
  exprSimSubscriptArrayCompose loweringStateRelDefs exprSimMemDefs ptrDiscipline
  createBlueprintRawCopyLayoutMods createCtorObservedSilence bodyPtrMakeArrayEmission bodySim
  loweringShapeDefs createExprSizeExitDefs createSizePrefixReplayMods
  createSizeBlueprintKeywordReplayMods createSizeRawReplayMods createSizeCtorValueRowMods

Theorem blueprint_raw_copied_at_cut_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env e p /\ create_operand_completed_ok_mods mods exps cx e /\
  expr_type e = BaseT (BytesT (Dynamic k)) /\ exprs_can_mutate ce later /\
  eval_operand target_op s = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at ca x) /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok_mods h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca s /\ alloca_history fnc s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx fnc s f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p s /\
    immutable_frame_mods fnc ce cx p s /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at_mods (DF h) lo d ce cx p Gi ti s) /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\ s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (vv,scm) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cm,sca,scm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  emit_op MLOAD [raw_op] cu = (len,cl) /\
  fn_has_code cm cs fnc /\ fn_has_code cu cl fnc /\
  create_expr_prefix ca cm (gas_explicit_sites ctx shctx) ctx fnc s mc t /\
  t.vs_current_bb = cm.cs_current_bb /\ t.vs_inst_idx = LENGTH cm.cs_current_insts /\
  create_expr_prefix cm cs (gas_explicit_sites ctx shctx) ctx fnc t ms r /\
  r.vs_current_bb = cs.cs_current_bb /\ r.vs_inst_idx = LENGTH cs.cs_current_insts /\
  create_expr_prefix cs cu (gas_explicit_sites ctx shctx) ctx fnc r mu u /\
  u.vs_current_bb = cu.cs_current_bb /\ u.vs_inst_idx = LENGTH cu.cs_current_insts /\
  (!v. storage_trace_frame (kcont v)) /\
  bind (bind (eval_expr cx e) (read_result cx)) kcont p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (mc ++ (ms ++ (mu ++ rest))) s.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?bs q G tn.
    bind (eval_expr cx e) (read_result cx) p = (INL (BytesV bs),q) /\
    kcont (BytesV bs) q = (res,out) /\ valid_horizon cx st0 H q.storage_trace /\
    q.gas_obs = gas_explicit rest u.vs_gas_readings ++ tail /\
    expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bs) raw_op u /\
    eval_operand target_op u = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at cu x) /\
    expr_sim_inv_mods mods ce cx env q /\ local_ptrs_reserved ce cu /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
    return_buf_frame d ce cu u /\ alloca_history fnc u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q u /\
      immutable_frame_mods fnc ce cx q u /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at_mods (DF h) lo d ce cx q G tn u) /\ ~u.vs_halted
Proof
  cheat
QED
