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
  exprBodyPreTypingProps exprBodyPreCallSafetyProps vyperTypeEvalSoundness
  vyperTypeExprSoundness vyperExprNoControl exprSimDefs gasContext
  vyperTypeInvariants bodyFullPostsMods

Theorem create_copy_gas_admissible_mods[local]:
  expr_body_pre_mods mods cenv cx env e es ==>
  gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  rw[gas_admissible_def] >>
  `no_type_error_result res` by
    (drule_at (Pat `vyperState$bind _ _ _ = _`)
       (REWRITE_RULE[ETA_THM] eval_expr_read_type_sound) >>
     disch_then (qspec_then `env` mp_tac) >>
     fs[runtime_consistent_def, env_consistent_def, state_well_typed_def]) >>
  Cases_on `res` >> simp[expr_res_ok_def] >> rename1 `INR exc` >>
  `no_control_exc exc` by
    (qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[NoAsms, vyperStateTheory.bind_def, AllCaseEqs()] >> strip_tac >>
     metis_tac[cj 1 eval_expr_no_control, read_result_no_control]) >>
  Cases_on `exc` >> gvs[no_control_exc_def, no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

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
  strip_tac >> drule_then assume_tac create_copy_gas_admissible_mods >>
  fs[expr_vv_sim_full_pre_mods_def, expr_sim_full_pre_mods_def,
     expr_sim_full_code_def] >> metis_tac[]
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
  strip_tac >> drule_then assume_tac create_copy_gas_admissible_mods >>
  qpat_x_assum `expr_sim_full_pre_mods _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[expr_sim_full_pre_mods_def]) >>
  drule_then strip_assume_tac expr_sim_full_code_fields >>
  `ci_mono sa sb` by (metis_tac[ci_mono_lower_value_compile_expr, SND]) >>
  `sa.cs_next_var <= sb.cs_next_var` by fs[ci_mono_def] >>
  qpat_assum `!h. valid_horizon _ _ h em.storage_trace ==> _`
    (qspec_then `H` (fn th => drule_then strip_assume_tac th)) >>
  qpat_x_assum `expr_sim_full_post_mods _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss())
       [expr_sim_full_post_mods_def, expr_post_mods_def, expr_post_def]) >>
  drule_then strip_assume_tac expr_sim_full_endpoint_fields >>
  `~t.vs_halted` by
    (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `!fn inst s'. frag_reachable ctx func t fn inst s' ==> dalloca_fmp_headroom inst s'` by
    (drule gas_origin_ptr_path_dalloca_fmp_headroom >> simp[] >>
     disch_then (fn th => rpt gen_tac >> strip_tac >> irule th) >>
     conj_tac >- first_assum ACCEPT_TAC >> goal_assum drule) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s` (irule_at Any) >> simp[]) >>
  `local_ptrs_reserved cenv sb` by (drule_all compiler_ci_mono_reserved >> simp[]) >>
  simp[expr_sim_full_pre_mods_def, expr_sim_full_code_def] >>
  conj_tac >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!h. valid_horizon _ _ h em.storage_trace ==> _`
    (fn th => first_x_assum (fn h => assume_tac (MATCH_MP th h))) >>
  qpat_x_assum `_ /\ expr_sim_full_post_mods _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [expr_sim_full_post_mods_def, expr_post_mods_def, expr_post_def]) >> simp[]
QED

Theorem create_copy_gas_obs_mods[local,simp]:
  (expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs) <=>
   expr_sim_inv_mods mods cenv cx env es) /\
  (expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs) <=>
   expr_body_pre_mods mods cenv cx env e es)
Proof
  simp[expr_body_pre_mods_def, expr_sim_inv_mods_def]
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
  strip_tac >> drule_all_then assume_tac create_size_replay_value_cut_mods >>
  qabbrev_tac `inp = es with gas_obs := gas_explicit (marks ++ rest) s.vs_gas_readings ++ tail` >>
  namedCases_on `vyperState$bind (eval_expr cx e) (read_result cx) inp` ["r em"] >>
  `valid_horizon cx st0 H em.storage_trace` by
    (Cases_on `r` >> fs[vyperStateTheory.bind_def] >>
     qpat_assum `!v. storage_trace_frame (k v)` (qspec_then `x` assume_tac) >>
     drule_all_then strip_assume_tac storage_trace_frame_prefix >>
     metis_tac[valid_horizon_append]) >>
  qpat_x_assum `gas_completed_operand_mods _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[gas_completed_operand_mods_def]) >>
  disch_then (qspecl_then [`H`,`marks`,`t`,
    `gas_explicit rest (DROP (LENGTH marks) s.vs_gas_readings) ++ tail`,`r`,`em`] mp_tac) >>
  impl_tac
  >- (simp[] >> metis_tac[Abbr `inp`, gas_explicit_append, APPEND_ASSOC]) >>
  strip_tac
  >- (qpat_assum `!h. valid_horizon _ _ h em.storage_trace ==> _`
        (qspec_then `H` (fn th => drule_then strip_assume_tac th)) >>
      qpat_assum `expr_sim_full_post_mods _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o SIMP_RULE (srw_ss())
           [expr_sim_full_post_mods_def, expr_post_mods_def]) >>
      drule_then assume_tac gas_origin_ptr_path_erase >>
      `gas_explicit rest (DROP (LENGTH marks) s.vs_gas_readings) =
       gas_explicit rest t.vs_gas_readings` by
        (drule_then (qspec_then `rest` mp_tac) gas_explicit_append_path >>
         simp[gas_explicit_append]) >>
      `expr_sim_inv_mods mods cenv cx env em` by
        (`expr_body_pre_mods mods cenv cx env e inp` by
           simp[Abbr `inp`, create_copy_gas_obs_mods] >>
         drule_all (REWRITE_RULE[ETA_THM] expr_body_pre_eval_mods) >> simp[]) >>
      disj2_tac >> map_every qexists_tac [`v`,`em`,`G'`,`tn'`] >>
      `em with gas_obs := gas_explicit rest t.vs_gas_readings ++ tail = em` by
        simp[evaluation_state_component_equality] >>
      `k v em = (res,ee)` by fs[vyperStateTheory.bind_def] >>
      simp[] >>
      conj_tac >- (drule expr_post_state >> simp[stmt_state_rel_def] >>
                   strip_tac >> drule state_rel_accounts >> simp[]) >>
      conj_tac >- fs[expr_sim_inv_mods_def] >>
      qpat_x_assum `!h. valid_horizon _ _ h em.storage_trace ==> _` mp_tac >>
      qpat_x_assum `r = INL _` SUBST_ALL_TAC >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  fs[vyperStateTheory.bind_def] >> metis_tac[]
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
  rpt strip_tac >> qpat_x_assum `whole = _` SUBST_ALL_TAC >>
  qpat_x_assum `vyperState$bind (eval_exprs _ _) _ _ = _`
    (assume_tac o REWRITE_RULE[create_copy_source_cons]) >>
  `!v. storage_trace_frame (vyperState$bind (eval_exprs cx args) (\vs. k (v::vs)))` by
    (gen_tac >> irule storage_trace_frame_bind_all >> simp[evaluate_storage_trace_frame]) >>
  drule_at (Pat `vyperState$bind (vyperState$bind _ _) _ _ = _`) create_copy_scalar_cut_mods >>
  disch_then (irule o BETA_RULE) >>
  qpat_assum `expr_sim_full_pre_mods _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
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
  rpt strip_tac >>
  drule_at (Pat `vyperState$bind (eval_exprs _ _) _ _ = _`) create_copy_list_cut_mods >>
  disch_then (drule_then mp_tac) >>
  disch_then (drule_at (Pat `create_expr_prefix _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_body_pre_mods _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `contract_inv _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `module_body_inv _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `valid_horizon _ _ _ _`)) >>
  disch_then (qspec_then `rest` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem create_copy_source_call_mods[local]:
  eval_expr cx (Call ann (CreateTarget CreateCopyOf hs rof ks) args dflt) =
  vyperState$bind (eval_exprs cx args)
    (eval_create_operands cx CreateCopyOf hs rof (MAP expr_type args)
      (blueprint_literal_offset cx hs args))
Proof
  PURE_ONCE_REWRITE_TAC [evaluate_def] >> Cases_on `args` >>
  simp[create_operand_order_def, FUN_EQ_THM, vyperStateTheory.bind_def]
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
  strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (drule body_inv_no_phi_mods >>
     fs[expr_vv_sim_full_pre_mods_def, expr_sim_full_code_def] >>
     disch_then (qspec_then `func` mp_tac) >> simp[]) >>
  `!e em. MEM e args /\ expr_sim_inv_mods mods cenv cx env em ==>
          expr_body_pre_mods mods cenv cx env e em` by
    (rpt strip_tac >> irule create_call_operand_body_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  `expr_body_pre_mods mods cenv cx env target_e es` by
    (qpat_assum `!e em. MEM e args /\ _ ==> _` irule >> simp[] >>
     drule expr_body_pre_mods_inv >> simp[]) >>
  drule_all_then assume_tac create_copy_first_scalar_pre_mods >>
  qpat_x_assum `eval_expr _ _ _ = _` (assume_tac o REWRITE_RULE[create_copy_source_call_mods]) >>
  gvs[create_operand_order_def] >>
  qmatch_asmsub_abbrev_tac `vyperState$bind (eval_exprs cx _) k _` >>
  `!vs. storage_trace_frame (k vs)` by simp[Abbr `k`,storage_trace_frame_create_operands] >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
   (?v em G1 tn1.
     vyperState$bind (eval_exprs cx (value_e::(case salt_e of NONE => [] | SOME e => [e])))
       (\vs. k (v::vs))
       ((em with gas_obs := []) with gas_obs := gas_explicit (m2 ++ (m3 ++ mr)) u1.vs_gas_readings ++ tail) = (res,ee) /\
     expr_sim_inv_mods mods cenv cx env em /\ valid_horizon cx st0 H em.storage_trace /\
     accounts_agree H cx.txn.target em.accounts u1.vs_accounts /\ accounts_well_typed em.accounts /\
     !h. valid_horizon cx st0 h em.storage_trace ==>
       gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) m1 (OK u1,G1,tn1) /\
       expr_sim_full_post_mods (DF,lo,d,ctx,func) cenv cx target_e
         (es,sa,a1,s0,target,G0,tn0) h (INL v : value + vyperState$exception)
         (em with gas_obs := []) G1 tn1 u1)` by
    (irule create_copy_list_cut_mods >>
     qpat_assum `expr_sim_full_pre_mods _ _ _ _ target_e _ _` (irule_at Any) >>
     simp[] >> rpt (goal_assum (drule_at Any)) >> simp[APPEND_ASSOC])
  >- (disj1_tac >> goal_assum drule >> simp[]) >>
  rename1 `expr_sim_inv_mods mods cenv cx env em1` >>
  `expr_body_pre_mods mods cenv cx env value_e (em1 with gas_obs := [])` by
    (simp[create_copy_gas_obs_mods] >>
     qpat_assum `!e em. _ /\ expr_sim_inv_mods _ _ _ _ em ==> _` irule >> simp[]) >>
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (s0,G0,tn0) m1 (OK u1,Ga,tna)` >>
  `expr_sim_full_pre_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type value_e) value_e (em1 with gas_obs := [])
     (st0,a1,a2,b1,b2,value,u1,Ga,tna)` by
    (irule create_copy_next_scalar_pre_mods >>
     qpat_assum `expr_sim_full_pre_mods _ _ _ _ target_e _ _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `vyperState$bind (eval_exprs cx (target_e::_)) _ _ = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `vyperState$bind (eval_exprs cx (value_e::_)) k1 _` >>
  `!vs. storage_trace_frame (k1 vs)` by simp[Abbr `k1`] >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
   (?v2 em G2 tn2.
     vyperState$bind (eval_exprs cx (case salt_e of NONE => [] | SOME e => [e]))
       (\vs. k1 (v2::vs))
       ((em with gas_obs := []) with gas_obs := gas_explicit (m3 ++ mr) u2.vs_gas_readings ++ tail) = (res,ee) /\
     expr_sim_inv_mods mods cenv cx env em /\ valid_horizon cx st0 H em.storage_trace /\
     accounts_agree H cx.txn.target em.accounts u2.vs_accounts /\ accounts_well_typed em.accounts /\
     !h. valid_horizon cx st0 h em.storage_trace ==>
       gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (u1,Ga,tna) m2 (OK u2,G2,tn2) /\
       expr_sim_full_post_mods (DF,lo,d,ctx,func) cenv cx value_e
         ((em1 with gas_obs := []),a1,a2,u1,value,Ga,tna) h (INL v2 : value + vyperState$exception)
         (em with gas_obs := []) G2 tn2 u2)` by
    (irule create_copy_list_cut_mods >>
     qpat_assum `expr_sim_full_pre_mods _ _ _ _ value_e _ _` (irule_at Any) >>
     simp[] >> rpt (goal_assum (drule_at Any)) >> simp[APPEND_ASSOC])
  >- (disj1_tac >> goal_assum drule >> simp[]) >>
  rename1 `accounts_agree H cx.txn.target em2.accounts u2.vs_accounts` >>
  Cases_on `salt_e`
  >- (gvs[compile_create_salt_def,compileEnvTheory.comp_return_def] >>
      drule_all create_copy_empty_cut >> strip_tac >>
      disj2_tac >> qexists_tac `em2.accounts` >> simp[]) >>
  rename1 `compile_create_salt _ _ (SOME salt_e) a2 = _` >>
  Cases_on `lower_value compile_expr cenv (expr_type salt_e) salt_e a2` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type salt_e) (gas_shadow_expr salt_e) b2` >>
  gvs[compile_create_salt_def,compileEnvTheory.comp_bind_def,compileEnvTheory.comp_return_def] >>
  `expr_body_pre_mods mods cenv cx env salt_e (em2 with gas_obs := [])` by
    (simp[create_copy_gas_obs_mods] >>
     qpat_assum `!e em. _ /\ expr_sim_inv_mods _ _ _ _ em ==> _` irule >> simp[]) >>
  rename1 `lower_value compile_expr cenv (expr_type salt_e) salt_e a2 = (salt_op,a3)` >>
  `expr_sim_full_pre_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type salt_e) salt_e (em2 with gas_obs := [])
     (st0,a2,a3,b2,b3,salt_op,u2,G2,tn2)` by
    (irule create_copy_next_scalar_pre_mods >>
     qpat_assum `expr_sim_full_pre_mods _ _ _ _ value_e _ _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `vyperState$bind (eval_exprs cx (value_e::_)) _ _ = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `vyperState$bind (eval_exprs cx [salt_e]) k2 _` >>
  `!vs. storage_trace_frame (k2 vs)` by simp[Abbr `k2`] >>
  irule create_copy_last_accounts_mods >>
  qpat_assum `expr_sim_full_pre_mods _ _ _ _ salt_e _ _` (irule_at Any) >>
  simp[create_copy_gas_obs_mods] >>
  goal_assum (drule_at (Pat `vyperState$bind (eval_exprs _ _) _ _ = _`)) >>
  rpt (goal_assum (drule_at Any)) >>
  qexists_tac `env` >> fs[create_copy_gas_obs_mods]
QED
