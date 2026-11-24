Theory createSizeCopyReplayMods
Ancestors
  createSizeCopyReplay createExprSizeExitDefsMods
  gasShadowCompileBase
  abiEncoderProps e2eDefs exprSimFullBundleProps fragExec gasExplicitSites gasSummary
  s1PrefixDefs venomExecSemantics vyperCreate vyperInterpreter vyperState relation list
  words createMarkedPath pair bodyFullIfExpReach arithmetic exprLowering vfmConstants
  compileEnv exprLoweringProps exprBodyPreProps exprSimSource bodySimStmtFacts
  vyperStorageTrace fragGasOriginPtrExec gasSummaryCompose bodyMemoryDefs exprOperandVar
  freshWrites rich_list exprSimHypsDefs exprSimWordArgs accountsRelProps gasOutcomeFull
  loweringPosts vyperAST vyperStorageFootprint integer_word loweringStateRelDefs bodySim
  loweringShapeDefs createExprSizeExitDefs createSizePrefixReplayMods createSizeOperandPreMods

Theorem create_copy_first_scalar_pre_mods[local]:
  expr_vv_sim_full_pre_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty call es (st0,sa,sb,sha,shb,vv,s,G,tn) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,a) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha = (op,b) /\
  gas_shadow_state a b /\ fn_has_code sa a func /\ fn_has_code sha b shadow_func /\
  expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_pre_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es (st0,sa,a,sha,b,op,s,G,tn)
Proof
  cheat
QED

Theorem create_copy_next_scalar_pre_mods[local]:
  expr_sim_full_pre_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es (st0,sa,sb,sha,shb,op,s,G,tn) /\
  lower_value compile_expr cenv (expr_type f) f sb = (operand,sc) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type f) (gas_shadow_expr f) shb = (operand,shc) /\
  gas_shadow_state sc shc /\ fn_has_code sb sc func /\ fn_has_code shb shc shadow_func /\
  expr_body_pre_mods mods cenv cx env f (em with gas_obs := []) /\
  valid_horizon cx st0 H em.storage_trace /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK t,G1,tn1) /\
    expr_sim_full_post_mods (DF,lo,d,ctx,func) cenv cx e
      (es,sa,sb,s,op,G,tn) H (res : value + vyperState$exception)
      (em with gas_obs := []) G1 tn1 t) ==>
  expr_sim_full_pre_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type f) f (em with gas_obs := []) (st0,sb,sc,shb,shc,operand,t,G1,tn1)
Proof
  cheat
QED

Theorem create_copy_scalar_cut_mods[local]:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_body_pre_mods mods cenv cx env e es /\ create_operand_completed_ok_mods mods exps cx e /\
  expr_sim_full_pre_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es (st0,sa,sb,sha,shb,op,s,G,tn) /\
  create_expr_prefix sa sb (gas_explicit_sites ctx shadow_ctx) ctx func s marks t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!v. storage_trace_frame (k v)) /\
  bind (bind (eval_expr cx e) (read_result cx)) k
    (es with gas_obs := gas_explicit (marks ++ rest) s.vs_gas_readings ++ tail) = (res,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  (?v em G1 tn1.
    k v ((em with gas_obs := []) with gas_obs := gas_explicit rest t.vs_gas_readings ++ tail) = (res,ee) /\
    expr_sim_inv_mods mods cenv cx env em /\ valid_horizon cx st0 H em.storage_trace /\
    accounts_agree H cx.txn.target em.accounts t.vs_accounts /\ accounts_well_typed em.accounts /\
    !h. valid_horizon cx st0 h em.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1) /\
      expr_sim_full_post_mods (DF,lo,d,ctx,func) cenv cx e
        (es,sa,sb,s,op,G,tn) h (INL v : value + vyperState$exception)
        (em with gas_obs := []) G1 tn1 t)
Proof
  cheat
QED

Theorem create_copy_list_cut_mods[local]:
  bind (eval_exprs cx (e::args)) k
    (es with gas_obs := gas_explicit whole s.vs_gas_readings ++ tail) = (res,ee) ==>
  expr_sim_full_pre_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es (st0,sa,sb,sha,shb,op,s,G,tn) ==>
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_body_pre_mods mods cenv cx env e es /\ create_operand_completed_ok_mods mods exps cx e /\
  create_expr_prefix sa sb (gas_explicit_sites ctx shadow_ctx) ctx func s marks t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!vs. storage_trace_frame (k vs)) /\ valid_horizon cx st0 H ee.storage_trace /\
  whole = marks ++ rest ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  (?v em G1 tn1.
    bind (eval_exprs cx args) (\vs. k (v::vs))
      ((em with gas_obs := []) with gas_obs := gas_explicit rest t.vs_gas_readings ++ tail) = (res,ee) /\
    expr_sim_inv_mods mods cenv cx env em /\ valid_horizon cx st0 H em.storage_trace /\
    accounts_agree H cx.txn.target em.accounts t.vs_accounts /\ accounts_well_typed em.accounts /\
    !h. valid_horizon cx st0 h em.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1) /\
      expr_sim_full_post_mods (DF,lo,d,ctx,func) cenv cx e
        (es,sa,sb,s,op,G,tn) h (INL v : value + vyperState$exception)
        (em with gas_obs := []) G1 tn1 t)
Proof
  cheat
QED

Theorem create_copy_last_accounts_mods[local]:
  bind (eval_exprs cx [e]) k
    (es with gas_obs := gas_explicit (marks ++ rest) s.vs_gas_readings ++ tail) = (res,ee) ==>
  expr_sim_full_pre_mods (DF,lo,d,ctx,shadow_ctx,(PG : (num # num) option list),func,shadow_func)
    cenv cx (expr_type e) e es (st0,sa,sb,sha,shb,op,s,G,tn) ==>
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_body_pre_mods mods cenv cx env e es /\ create_operand_completed_ok_mods mods exps cx e /\
  create_expr_prefix sa sb (gas_explicit_sites ctx shadow_ctx) ctx func s marks t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!vs. storage_trace_frame (k vs)) /\ valid_horizon cx st0 H ee.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  (?acc. accounts_agree H cx.txn.target acc t.vs_accounts /\ accounts_well_typed acc)
Proof
  cheat
QED

Theorem create_copy_replay_accounts_at_cuts_mods:
  has_salt = IS_SOME salt_e /\
  args = target_e::value_e::(case salt_e of NONE => [] | SOME e => [e]) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_body_pre_mods mods cenv cx env (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt) es /\
  expr_vv_sim_full_pre_mods (DF,lo,d,ctx,shadow_ctx,(PG : (num # num) option list),func,shadow_func)
    cenv cx ty (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt) es
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
  EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order CreateCopyOf has_salt args) /\
  lower_value compile_expr cenv (expr_type target_e) target_e sa = (target,a1) /\
  lower_value compile_expr cenv (expr_type value_e) value_e a1 = (value,a2) /\
  compile_create_salt compile_expr cenv salt_e a2 = (salt,a3) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type target_e) (gas_shadow_expr target_e) shadow_sa = (target,b1) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type value_e) (gas_shadow_expr value_e) b1 = (value,b2) /\
  compile_create_salt compile_expr (gas_shadow_env T cenv) (OPTION_MAP gas_shadow_expr salt_e) b2 = (salt,b3) /\
  gas_shadow_state a1 b1 /\ gas_shadow_state a2 b2 /\ gas_shadow_state a3 b3 /\
  fn_has_code sa a1 func /\ fn_has_code a1 a2 func /\ fn_has_code a2 a3 func /\
  fn_has_code shadow_sa b1 shadow_func /\ fn_has_code b1 b2 shadow_func /\ fn_has_code b2 b3 shadow_func /\
  create_expr_prefix sa a1 (gas_explicit_sites ctx shadow_ctx) ctx func s0 m1 u1 /\
  create_expr_prefix a1 a2 (gas_explicit_sites ctx shadow_ctx) ctx func u1 m2 u2 /\
  create_expr_prefix a2 a3 (gas_explicit_sites ctx shadow_ctx) ctx func u2 m3 u3 /\
  u1.vs_current_bb = a1.cs_current_bb /\ u1.vs_inst_idx = LENGTH a1.cs_current_insts /\
  u2.vs_current_bb = a2.cs_current_bb /\ u2.vs_inst_idx = LENGTH a2.cs_current_insts /\
  u3.vs_current_bb = a3.cs_current_bb /\ u3.vs_inst_idx = LENGTH a3.cs_current_insts /\
  eval_expr cx (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt)
    (es with gas_obs := gas_explicit (m1 ++ (m2 ++ (m3 ++ mr))) s0.vs_gas_readings ++ tail) = (res,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  (?acc. accounts_agree H cx.txn.target acc u3.vs_accounts /\ accounts_well_typed acc)
Proof
  cheat
QED
