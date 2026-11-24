Theory createSizeCtorWordRowMods
Ancestors
  createSizeCtorWordRow createExprSizeExitDefsMods
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps gasExplicitSites gasSummary s1PrefixDefs venomExecSemantics
  vyperState relation list words pair bodyFullIfExpReach arithmetic exprLowering
  vfmConstants compileEnv exprLoweringProps exprBodyPreProps exprSimSource bodySimStmtFacts
  gasSummaryCompose bodyMemoryDefs rich_list exprSimHypsDefs vyperTypeSystem
  vyperTypeExprSoundness createCtorSavedSimpleMods exprSimHyps bodyPtrDefs loweringPosts context
  fragGasPath vyperAST vyperStorageFootprint vyperTyping vyperValue integer_word
  abiEncodeArgsSim aggregateEvaluatedLayout loweringStateRelDefs ptrDiscipline bodySim
  createExprSizeExitDefs createSizePrefixReplayMods createSizeBlueprintKeywordReplayMods
  createSizeCtorValueRowMods

(* A word constructor completes at the snapshot cut, which includes its
   unwrap. Keep the full scalar post for the payload-length proof. *)

Theorem blueprint_ctor_word_row_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env e p /\ create_operand_completed_ok_mods mods exps cx e /\
  is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) m = (sv,b) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  compile_snapshot_vv ce shcopy (ext_call_arg_value (lowered_value_type ce e) vv) shm = (sv,shb) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (a,b,sha,shb) /\
  local_ptrs_reserved ce a /\ (!K. dead_lo_ok_mods K (DF K) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history fnc s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx fnc s f i z ==> dalloca_fmp_headroom i z) /\
  (!K. valid_horizon cx st0 K p.storage_trace ==>
    stmt_state_rel K ctx fnc ce cx p s /\
    immutable_frame_mods fnc ce cx p s /\ storage_well_formed_on cx p (FST K) /\
    ghost_inv_at_mods (DF K) lo d ce cx p G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  create_expr_prefix a b (gas_explicit_sites ctx shctx) ctx fnc s chunk t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  bind (eval_expr cx e) (read_result cx) p = (rr,q) /\
  valid_horizon cx st0 H q.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ rest) s.vs_gas_readings ++ tail ==>
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?v G' tn'. rr = INL v /\ q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    (!K op. valid_horizon cx st0 K q.storage_trace /\
      lower_value compile_expr ce (expr_type e) e a = (op,b) ==>
      expr_sim_full_post_mods (DF,lo,d,ctx,fnc) ce cx e (p,a,b,s,op,G,tn)
        K (INL v : value + exception) (q with gas_obs := []) G' tn' t) /\
    expr_sim_inv_mods mods ce cx env q /\
    (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME ann /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) /\
      value_has_type tv v /\ value_has_type ann v) /\
    return_buf_frame d ce b t /\ alloca_history fnc t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!K. valid_horizon cx st0 K q.storage_trace ==>
      stmt_state_rel K ctx fnc ce cx q t /\
      immutable_frame_mods fnc ce cx q t /\ storage_well_formed_on cx q (FST K) /\
      ghost_inv_at_mods (DF K) lo d ce cx q G' tn' t)
Proof
  cheat
QED
