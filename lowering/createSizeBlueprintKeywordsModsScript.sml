Theory createSizeBlueprintKeywordsMods
Ancestors
  createSizeBlueprintKeywords createExprSizeExitDefsMods
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps gasExplicitSites gasSummary venomState vyperCreate
  vyperState relation list words pair arithmetic exprLowering vfmConstants exprLoweringProps
  exprBodyPreProps vyperStorageTrace freshWrites rich_list exprSimHypsDefs vyperTypeSystem
  vyperTypeExprSoundness exprSimWordArgs bodyPtrDefs loweringPosts vyperAST
  vyperStorageFootprint vyperValue integer_word loweringStateRelDefs ptrDiscipline bodySim
  loweringShapeDefs createExprSizeExitDefs createSizeCopyReplayMods
  createSizeBlueprintKeywordReplayMods createSizeOperandPreMods createSizePrefixReplayMods

Theorem create_blueprint_keywords_at_cuts_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order (CreateFromBlueprint raw) hs args) /\
  LENGTH cvs = LENGTH ctors /\ dest_AddressV av = SOME (w2w aw) /\
  eval_operand target_op u = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at ca x) /\
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
  lower_value compile_expr ce (expr_type amount) amount ca = (amount_op,cm) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type amount) (gas_shadow_expr amount) sca = (amount_op,scm) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cm,sca,scm) /\
  create_expr_prefix ca cm (gas_explicit_sites ctx shctx) ctx fnc u ma m /\
  m.vs_current_bb = cm.cs_current_bb /\ m.vs_inst_idx = LENGTH cm.cs_current_insts /\
  (if hs then
      lower_value compile_expr ce (expr_type salt) salt cm = (salt_op,cn) /\
      lower_value compile_expr (gas_shadow_env T ce) (expr_type salt) (gas_shadow_expr salt) scm = (salt_op,scn) /\
      expr_sim_full_code (ctx,shctx,fnc,shfnc) (cm,cn,scm,scn) /\
      create_expr_prefix cm cn (gas_explicit_sites ctx shctx) ctx fnc m ms n /\
      n.vs_current_bb = cn.cs_current_bb /\ n.vs_inst_idx = LENGTH cn.cs_current_insts
   else cn = cm /\ scn = scm /\ n = m /\ ms = []) /\
  ((?oty i. origin_fold_value off = Literal oty (IntL i) /\
     offset_op = Lit (i2w i) /\ cb = cn /\ scb = scn /\ t = n /\ mo = []) \/
   (lower_value compile_expr ce (expr_type off) off cn = (offset_op,cb) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type off) (gas_shadow_expr off) scn = (offset_op,scb) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (cn,cb,scn,scb) /\
    create_expr_prefix cn cb (gas_explicit_sites ctx shctx) ctx fnc n mo t /\
    t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts)) /\
  bind (eval_exprs cx (amount::((if hs then [salt] else []) ++ [off])))
    (\kvs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (ma ++ (ms ++ (mo ++ rest))) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?kvs q ops ow.
    eval_exprs cx (amount::((if hs then [salt] else []) ++ [off])) p = (INL kvs,q) /\
    eval_create_operands cx (CreateFromBlueprint raw) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs)) q = (res,out) /\
    dest_create_args (CreateFromBlueprint raw) hs
      (create_operand_layout (CreateFromBlueprint raw) hs (av::(cvs ++ kvs))) = SOME ops /\
    ops.co_code_src = AddressCodeSource (w2w aw) /\ ops.co_ctor_args = cvs /\
    ops.co_code_offset = SOME (w2n ow) /\
    eval_operand target_op t = SOME aw /\ eval_operand offset_op t = SOME ow /\
    (!x. offset_op = Var x ==> not_fresh_at cb x) /\
    (lookup_account (w2w aw) q.accounts).code = (lookup_account (w2w aw) t.vs_accounts).code /\
    (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w)
Proof
  cheat
QED
