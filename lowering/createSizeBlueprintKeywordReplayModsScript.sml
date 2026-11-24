Theory createSizeBlueprintKeywordReplayMods
Ancestors
  createSizeBlueprintKeywordReplay createExprSizeExitDefsMods
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps fragGasOrigin gasExplicitSites gasSummary s1PrefixDefs
  venomExecSemantics venomState vyperCreate vyperState relation list words createMarkedPath
  pair bodyFullIfExpReach arithmetic exprLowering vfmConstants compileEnv exprLoweringProps
  exprBodyPreProps exprSimSource bodySimStmtFacts vyperStorageTrace gasSummaryCompose
  bodyMemoryDefs exprOperandVar freshWrites rich_list exprSimHypsDefs
  createSizeBlueprintOffsetMods vyperTypeSystem vyperTypeExprSoundness exprSimWordArgs
  accountsRelProps bodyPtrDefs loweringPosts fragGasPath vyperAST vyperStorageFootprint
  vyperTyping vyperValue integer_word valueEncoding loweringStateRelDefs ptrDiscipline
  bodySim loweringShapeDefs createExprSizeExitDefs createSizePrefixReplayMods
  createSizeCopyReplayMods createSizeOperandPreMods

Theorem blueprint_read_at_cut_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env e p /\ create_operand_completed_ok_mods mods exps cx e /\
  lower_value compile_expr ce (expr_type e) e ca = (op,cb) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (op,scb) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cb,sca,scb) /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok_mods h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p u /\
    immutable_frame_mods fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at_mods (DF h) lo d ce cx p G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\
  u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  create_expr_prefix ca cb (gas_explicit_sites ctx shctx) ctx fnc u chunk t /\
  t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts /\
  (!v. storage_trace_frame (k v)) /\
  bind (bind (eval_expr cx e) (read_result cx)) k p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ rest) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?v q G' tn'.
    bind (eval_expr cx e) (read_result cx) p = (INL v,q) /\ k v q = (res,out) /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    valid_horizon cx st0 H q.storage_trace /\
    expr_sim_inv_mods mods ce cx env q /\ value_runtime_typed env (expr_type e) v /\
    expr_val_rel cx (post_value_type ce e) v op t /\
    ca.cs_next_var <= cb.cs_next_var /\
    (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w) /\
    return_buf_frame d ce cb t /\ alloca_history fnc t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q t /\
      immutable_frame_mods fnc ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at_mods (DF h) lo d ce cx q G' tn' t) /\ ~t.vs_halted
Proof
  cheat
QED

Theorem blueprint_offset_at_cut_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  create_operand_completed_ok_mods mods exps cx off /\
  expr_sim_inv_mods mods ce cx env p /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok_mods h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p u /\
    immutable_frame_mods fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at_mods (DF h) lo d ce cx p G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\
  u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  ((?oty i. origin_fold_value off = Literal oty (IntL i) /\
     op = Lit (i2w i) /\ cb = ca /\ scb = sca /\ t = u /\ chunk = []) \/
   (lower_value compile_expr ce (expr_type off) off ca = (op,cb) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type off) (gas_shadow_expr off) sca = (op,scb) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cb,sca,scb) /\
    create_expr_prefix ca cb (gas_explicit_sites ctx shctx) ctx fnc u chunk t /\
    t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts)) /\
  (!v. storage_trace_frame (k v)) /\
  bind (bind (eval_expr cx off) (read_result cx)) k p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ rest) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?v q w.
    bind (eval_expr cx off) (read_result cx) p = (INL v,q) /\ k v q = (res,out) /\
    dest_NumV v = SOME (w2n w) /\ eval_operand op t = SOME w /\
    stmt_state_rel H ctx fnc ce cx q t /\
    immutable_frame_mods fnc ce cx q t /\
    (!x. op = Var x ==> not_fresh_at cb x) /\
    (!x k. not_fresh_at ca x /\ lookup_var x u = SOME k ==> lookup_var x t = SOME k)
Proof
  cheat
QED

Theorem blueprint_optional_salt_at_cut_mods:
  (hs ==> expr_body_pre_mods mods ce cx env salt p /\ create_operand_completed_ok_mods mods exps cx salt /\
      expr_type salt = BaseT (BytesT (Fixed 32))) /\
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_sim_inv_mods mods ce cx env p /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok_mods h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p u /\
    immutable_frame_mods fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at_mods (DF h) lo d ce cx p G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\
  u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  (if hs then
      lower_value compile_expr ce (expr_type salt) salt ca = (op,cb) /\
      lower_value compile_expr (gas_shadow_env T ce) (expr_type salt) (gas_shadow_expr salt) sca = (op,scb) /\
      expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cb,sca,scb) /\
      create_expr_prefix ca cb (gas_explicit_sites ctx shctx) ctx fnc u chunk t /\
      t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts
   else cb = ca /\ scb = sca /\ t = u /\ chunk = []) /\
  (!vs. storage_trace_frame (k vs)) /\
  bind (eval_exprs cx (if hs then [salt] else [])) k p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ rest) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?svs q G' tn'.
    eval_exprs cx (if hs then [salt] else []) p = (INL svs,q) /\ k svs q = (res,out) /\
    (if hs then ?sv w. svs = [sv] /\ dest_create_salt sv = SOME w else svs = []) /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    expr_sim_inv_mods mods ce cx env q /\ ca.cs_next_var <= cb.cs_next_var /\
    (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w) /\
    return_buf_frame d ce cb t /\ alloca_history fnc t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q t /\
      immutable_frame_mods fnc ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at_mods (DF h) lo d ce cx q G' tn' t) /\ ~t.vs_halted
Proof
  cheat
QED
