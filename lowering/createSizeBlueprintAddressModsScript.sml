Theory createSizeBlueprintAddressMods
Ancestors
  createSizeBlueprintAddress createExprSizeExitDefsMods
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps gasExplicitSites gasSummary s1PrefixDefs venomState
  vyperCreate vyperInterpreter vyperState relation list words pair arithmetic exprLowering
  vfmConstants compileEnv exprLoweringProps exprBodyPreProps vyperStorageTrace
  exprOperandVar rich_list exprSimHypsDefs vyperTypeSystem vyperTypeExprSoundness
  bodyPtrDefs loweringPosts vyperAST vyperStorageFootprint vyperTyping vyperValue
  integer_word valueEncoding loweringStateRelDefs ptrDiscipline bodySim
  createExprSizeExitDefs createSizeCopyReplayMods createSizeBlueprintKeywordReplayMods
  createSizeOperandPreMods

(* Replay the first operand on the observed address cut. The returned source
   state still carries the marks of the unexecuted payload and keywords. *)

Theorem create_blueprint_address_at_cut_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es /\
  expr_vv_sim_full_pre_mods (DF,lo,d,ctx,shctx,(PG : (num # num) option list),fnc,shfnc)
    ce cx ty (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
  EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order (CreateFromBlueprint raw) hs args) /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  later = amount::((if hs then [salt] else []) ++ [off]) /\
  lower_value compile_expr ce (expr_type target) target sa = (target_op,ca) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type target) (gas_shadow_expr target) shadow_sa = (target_op,sca) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (sa,ca,shadow_sa,sca) /\
  create_expr_prefix sa ca (gas_explicit_sites ctx shctx) ctx fnc s0 chunk u /\
  u.vs_current_bb = ca.cs_current_bb /\ u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  eval_expr cx (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df)
    (es with gas_obs := gas_explicit (chunk ++ rest) s0.vs_gas_readings ++ tail) = (res,out) /\
  valid_horizon cx st0 H out.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?av aw p G tn.
    dest_AddressV av = SOME (w2w aw) /\ eval_operand target_op u = SOME aw /\
    (!x. target_op = Var x ==> not_fresh_at ca x) /\
    bind (eval_exprs cx (ctors ++ later))
      (\vs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs)) p = (res,out) /\
    p.gas_obs = gas_explicit rest u.vs_gas_readings ++ tail /\
    valid_horizon cx st0 H p.storage_trace /\
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
    ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\ u.vs_inst_idx = LENGTH ca.cs_current_insts
Proof
  cheat
QED
