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
  createSizeCopyReplayMods createSizeOperandPreMods createSizePrefixReplay
  vyperTypeInvariants exprSimDefs vyperExprNoControl bodyFullPostsMods bodyFullShadowBodyInv
  createSizeCopyReplay vyperInterpreter

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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok p` by
    suspend "admissible" >>
  `gas_completed_operand_mods (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
     mods cx st0 ca cb (bind (eval_expr cx e) (read_result cx)) (p,u,G,tn)
     (expr_sim_full_post_mods (DF,lo,d,ctx,fnc) ce cx e (p,ca,cb,u,op,G,tn))` by
    (irule create_size_replay_value_cut_mods >> simp[] >>
     conj_tac >- (qexists_tac `exps` >> simp[]) >>
     conj_tac >- (qexistsl [`src`,`tops`] >> simp[]) >>
     conj_tac >- (qexists_tac `env` >> simp[]) >>
     qexistsl [`shfnc`, `sca`, `scb`, `expr_type e`] >>
     simp[expr_sim_full_pre_mods_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qx_gen_tac `h` >> disch_tac >>
     qpat_assum `!h. valid_horizon _ _ h p.storage_trace ==> _`
       (qspec_then `h` (fn th => drule_then strip_assume_tac th)) >> simp[]) >>
  `gas_path ctx fnc u (LENGTH chunk) (OK t)` by
    (qpat_assum `create_expr_prefix ca cb _ _ _ _ _ _`
       (mp_then Any mp_tac create_prefix_gas_path) >> simp[]) >>
  `p.gas_obs = gas_explicit chunk u.vs_gas_readings ++
               (gas_explicit rest t.vs_gas_readings ++ tail)` by
    (drule gas_explicit_append_path >> simp[APPEND_ASSOC]) >>
  `p with gas_obs := gas_explicit chunk u.vs_gas_readings ++
                      (gas_explicit rest t.vs_gas_readings ++ tail) = p` by
    (qpat_assum `p.gas_obs = gas_explicit chunk _ ++ _`
       (once_rewrite_tac o single o SYM) >> simp[]) >>
  namedCases_on `bind (eval_expr cx e) (read_result cx) p` ["rr mid"] >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (Cases_on `rr` >> fs[vyperStateTheory.bind_def] >> metis_tac[valid_horizon_frame]) >>
  qhdtm_x_assum `gas_completed_operand_mods` mp_tac >>
  simp[gas_completed_operand_mods_def] >>
  disch_then (qspecl_then [`H`,`chunk`,`t`,
    `gas_explicit rest t.vs_gas_readings ++ tail`,`rr`,`mid`] mp_tac) >>
  simp[] >> strip_tac
  >- suspend "success" >>
  disj1_tac >> qexists_tac `err` >> fs[vyperStateTheory.bind_def]
QED

Resume blueprint_read_at_cut_mods[admissible]:
  drule_then strip_assume_tac exprBodyPreTypingPropsTheory.expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac exprBodyPreCallSafetyPropsTheory.expr_body_pre_mods_call_evaluation_safe >>
  rw[gasContextTheory.gas_admissible_def] >>
  `no_type_error_result res'` by
    (drule_at (Pat `vyperState$bind _ _ _ = _`)
       (REWRITE_RULE[ETA_THM] vyperTypeEvalSoundnessTheory.eval_expr_read_type_sound) >>
     disch_then (qspec_then `env` mp_tac) >>
     fs[runtime_consistent_def, env_consistent_def, state_well_typed_def]) >>
  Cases_on `res'` >> simp[expr_res_ok_def] >> rename1 `INR exc` >>
  `no_control_exc exc` by
    (qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[NoAsms, vyperStateTheory.bind_def, AllCaseEqs()] >> strip_tac >>
     metis_tac[cj 1 eval_expr_no_control, read_result_no_control]) >>
  Cases_on `exc` >> gvs[no_control_exc_def, no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Resume blueprint_read_at_cut_mods[success]:
  qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> _`
    (qspec_then `H` (fn th => drule_then strip_assume_tac th)) >>
  qpat_x_assum `expr_sim_full_post_mods _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[expr_sim_full_post_mods_def,
       expr_post_mods_def,expr_post_def]) >>
  gvs[] >>
  `k v mid = (res,out)` by fs[vyperStateTheory.bind_def] >>
  drule_all (REWRITE_RULE[ETA_THM] expr_body_pre_eval_mods) >> simp[] >> strip_tac >>
  `ci_mono ca cb` by metis_tac[ci_mono_lower_value_compile_expr,SND] >>
  `ca.cs_next_var <= cb.cs_next_var` by fs[ci_mono_def] >>
  drule_then strip_assume_tac expr_sim_full_endpoint_fields >>
  `return_buf_frame d ce cb t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d ce ca u` (irule_at Any) >> simp[]) >>
  `MEM fnc ctx.ctx_functions` by fs[expr_sim_full_code_def] >>
  `!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (drule body_inv_no_phi_mods >> disch_then (qspec_then `fnc` mp_tac) >> simp[]) >>
  `!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> _`
       (qspec_then `H` (fn th => drule_then strip_assume_tac th)) >>
     drule gas_origin_ptr_path_dalloca_fmp_headroom >> simp[] >>
     disch_then (fn th => rpt gen_tac >> strip_tac >> irule th) >>
     conj_tac >- first_assum ACCEPT_TAC >> goal_assum drule) >>
  `~t.vs_halted` by (drule gas_path_normal >> simp[]) >>
  disj2_tac >> qexistsl [`G'`,`tn'`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `h` >> disch_tac >>
  qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> _`
    (qspec_then `h` (fn th => drule_then strip_assume_tac th)) >>
  qpat_x_assum `expr_sim_full_post_mods _ _ _ _ _ h _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[expr_sim_full_post_mods_def,
       expr_post_mods_def,expr_post_def]) >>
  `immutable_frame_mods fnc ce cx (mid with gas_obs := []) t <=>
   immutable_frame_mods fnc ce cx mid t` by
    simp[NoAsms,immutable_frame_mods_def,
      bodyInvSplitTheory.immutables_rel_mods_def,immutables_rel_def,
      bodyInvSplitTheory.immutable_alloca_sep_mods_def,immutable_alloca_sep_def] >>
  `ghost_inv_at_mods (DF h) lo d ce cx (mid with gas_obs := []) G' tn' t <=>
   ghost_inv_at_mods (DF h) lo d ce cx mid G' tn' t` by simp[NoAsms,ghost_inv_at_mods_def] >>
  `storage_well_formed_on cx (mid with gas_obs := []) (FST h) <=>
   storage_well_formed_on cx mid (FST h)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  fs[]
QED
Finalise blueprint_read_at_cut_mods

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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM off args /\ expr_type off = BaseT (UintT 256)` by
    (drule expr_body_pre_mods_well_typed >>
     Cases_on `hs` >> gvs[well_typed_expr_def,create_arg_types_ok_def]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `(?oty i. _) \/ _` strip_assume_tac
  >- (drule_all create_blueprint_offset_bridge_mods >> strip_tac >>
      qpat_assum `!oty i. origin_fold_value off = _ ==> _` (drule_then strip_assume_tac) >>
      gvs[eval_operand_def,vyperStateTheory.bind_def] >>
      `valid_horizon cx st0 H p.storage_trace` by
        (qpat_assum `!v. storage_trace_frame (k v)` (qspec_then `IntV i` assume_tac) >>
         drule_all valid_horizon_frame >> simp[]) >>
      disj2_tac >>
      qpat_assum `!h. valid_horizon _ _ h p.storage_trace ==> _`
        (qspec_then `H` (fn th => drule_then strip_assume_tac th)) >> simp[]) >>
  `expr_body_pre_mods mods ce cx env off p` by
    (irule create_call_operand_body_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  drule_all blueprint_read_at_cut_mods >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  `post_value_type ce off = BaseT (UintT 256)` by simp[is_word_type_def] >>
  `?w. dest_NumV v = SOME (w2n w) /\ eval_operand op t = SOME w` by
    (`value_runtime_typed env (BaseT (UintT 256)) v` by
       (qpat_assum `value_runtime_typed _ (expr_type off) _` mp_tac >>
        qpat_assum `expr_type off = _` (pure_rewrite_tac o single) >>
        disch_then ACCEPT_TAC) >>
     drule blueprint_keyword_uint >> strip_tac >>
     gvs[expr_val_rel_def,evaluate_type_def,is_word_type_def,
         typed_val_to_w256_def,val_to_w256_def]) >>
  `!x. op = Var x ==> not_fresh_at cb x` by
    (qpat_assum `lower_value compile_expr ce _ off ca = _`
       (mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] compile_lower_value_var)) >> simp[]) >>
  disj2_tac >> qexistsl [`v`,`q`,`w`] >> simp[] >>
  qpat_assum `!h. valid_horizon _ _ h q.storage_trace ==> _`
    (qspec_then `H` (fn th => drule_then strip_assume_tac th)) >> simp[]
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
  reverse (Cases_on `hs`) >> simp[cj 49 evaluate_def,return_def,bind_return] >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (disj2_tac >> qexistsl [`G`,`tn`] >> simp[] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qx_gen_tac `h` >> disch_tac >>
      qpat_assum `!h. valid_horizon _ _ h p.storage_trace ==> _`
        (qspec_then `h` (fn th => drule_then strip_assume_tac th)) >> simp[]) >>
  `bind (bind (eval_expr cx salt) (read_result cx)) (\v. k [v]) p = (res,out)` by
    fs[create_copy_source_cons,cj 49 evaluate_def,bind_return] >>
  `!v. storage_trace_frame ((\v. k [v]) v)` by simp[] >>
  drule_all blueprint_read_at_cut_mods >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  `?w. dest_create_salt v = SOME w` by
    (qpat_assum `value_runtime_typed _ _ v` mp_tac >>
     qpat_assum `expr_type salt = _` (pure_rewrite_tac o single) >>
     Cases_on `v` >> simp[value_runtime_typed_def,evaluate_type_def,value_has_type_def,
       dest_create_salt_def,dest_BytesV_def]) >>
  `eval_exprs cx [salt] p = (INL [v],q)` by
    (irule blueprint_eval_join_cons >> simp[eval_exprs_nil]) >>
  disj2_tac >> qexistsl [`[v]`,`q`,`G'`,`tn'`] >> fs[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `h` >> disch_tac >>
  qpat_assum `!h. valid_horizon _ _ h q.storage_trace ==> _`
    (qspec_then `h` (fn th => drule_then strip_assume_tac th)) >> simp[]
QED
