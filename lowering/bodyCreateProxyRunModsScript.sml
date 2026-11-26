(* The proxy buffer is prepared after amount evaluation and before the optional salt. *)
Theory bodyCreateProxyRunMods
Ancestors
  bodyCreateProxyLayoutMods bodyCreateProxyOperandsMods bodyCreateProxyWindowRebaseMods
  bodyCreateProxySaltCutMods bodyCreateProxySaltWindowMods bodyCreateProxyDispatchMods
  bodyFullPredsMods bodyFullPostsMods bodyFullIfExpReach gasOutcomeFullZeroPrefixMods
  builtinCreate exprLowering exprLoweringProps loweringShapeDefs loweringPosts
  supportedExprTraverse compileEnv gasShadow gasShadowCompile
  vyperInterpreter vyperCreate vyperStorageTrace vyperStorageFootprint vyperAST vyperState
  vyperTypeSystem list option

Triviality proxy_salt_some:
  compile_create_salt f cenv (SOME salt) cs = (sop,ds) <=>
  ?q. sop = SOME q /\ lower_value f cenv (expr_type salt) salt cs = (q,ds)
Proof
  Cases_on `lower_value f cenv (expr_type salt) salt cs` >>
  simp[compile_create_salt_def,comp_bind_def,comp_return_def,EQ_SYM_EQ]
QED

Theorem create_proxy_forced_mods:
  body_exprs_full_ok_mods mods exps cx (create_operand_order CreateMinimalProxy salted args) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env
    (Call ann (CreateTarget CreateMinimalProxy salted rof ks) args dflt) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Call ann (CreateTarget CreateMinimalProxy salted rof ks) args dflt) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_sim_full_mods_def] >>
  map_every qx_gen_tac [`st0`,`sa`,`sb`,`sha`,`shb`,`result`,`s0`,`G0`,`tn0`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac create_proxy_layout_mods >>
  qpat_x_assum `ann = _` SUBST_ALL_TAC >>
  qpat_assum `create_operand_order _ _ _ = _` (RULE_ASSUM_TAC o PURE_REWRITE_RULE o single) >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  qabbrev_tac `next = \vs. bind (eval_create_operands cx CreateMinimalProxy salted rof
    (MAP expr_type (target::amount::salts))
    (blueprint_literal_offset cx salted (target::amount::salts)) vs) (read_result cx)` >>
  `!vs. storage_trace_frame (next vs)` by
    simp[Abbr `next`,storage_trace_frame_bind_all,storage_trace_frame_read_result,
         storage_trace_frame_create_operands] >>
  rewrite_tac[CONJUNCT2 create_proxy_read_order_mods] >>
  qpat_assum `Abbrev (next = _)`
    (PURE_ONCE_REWRITE_TAC o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  simp[post_value_type_def,expr_type_def,is_word_type_def] >>
  irule create_proxy_target_amount_cut_mods >> BETA_TAC >>
  suspend "operands"
QED

Resume create_proxy_forced_mods[operands]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`a`,`ah`,`BaseT AddressT`,`b`,`bh`,`d`,`dflt`,`env`,`exps`,
                `ks`,`mods`,`rof`,`sa`,`salted`,`sha`,`shadow_func`,`src`,`tops`,`x`,`y`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qx_genl_tac [`tv`,`av`,`tw`,`aw`,`ea`,`Gm`,`tm`,`m`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "window"
QED

Resume create_proxy_forced_mods[window]:
  rename1 `compile_create_dispatch buf (Lit 54w) y sop rof sd = (result,sb)` >>
  `ci_mono sa b` by drule_all_then ACCEPT_TAC ci_mono_trans >>
  `sa.cs_next_var <= b.cs_next_var /\ sa.cs_next_id <= b.cs_next_id` by fs[ci_mono_def] >>
  `!z n. cenv.ce_return_buf = SOME (PtrVar (Var z) n) ==> not_fresh_at b z` by
    metis_tac[not_fresh_at_mono] >>
  `!z n. cenv.ce_return_pc = SOME (PtrVar (Var z) n) ==> not_fresh_at b z` by
    metis_tac[not_fresh_at_mono] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qexistsl_tac [`cenv`,`ctx`,`cx`,`exps`,`func`,`mods`] >> simp[]) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [IMP_CONJ_THM,FORALL_AND_THM]) >>
  qpat_assum `!H. valid_horizon cx st0 H ea.storage_trace ==> _`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [IMP_CONJ_THM,FORALL_AND_THM]) >>
  `!H. valid_horizon cx st0 H ea.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ea m /\ immutable_frame_mods func cenv cx ea m /\
    storage_well_formed_on cx ea (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ea Gm tm m` by
    (gen_tac >> disch_tac >> rpt conj_tac >> first_assum (drule_then ACCEPT_TAC)) >>
  qpat_assum `compile_create_proxy_buf x b = (buf,c)`
    (mp_then Any drule_all create_proxy_window_rebase_mods) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`p`,`w`,`u`,`Gu`,`tu`] strip_assume_tac)) >>
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl_tac [`Gu`,`u`,`tu`] >> conj_tac
  >- (gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_x_assum `buf = Var p` SUBST_ALL_TAC >>
  Cases_on `salted` >> RULE_ASSUM_TAC (REWRITE_RULE [COND_CLAUSES])
  >- (qpat_x_assum `?salt. salts = [salt] /\ _` strip_assume_tac >>
      qpat_x_assum `salts = [salt]` SUBST_ALL_TAC >> suspend "salted") >>
  qpat_x_assum `salts = []` SUBST_ALL_TAC >> suspend "unsalted"
QED

Resume create_proxy_forced_mods[unsalted]:
  qpat_x_assum `compile_create_salt compile_expr cenv NONE c = _`
    (strip_assume_tac o SIMP_RULE bool_ss [compile_create_salt_def,comp_return_def,pairTheory.PAIR_EQ]) >>
  qpat_x_assum `NONE = sop` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `c = sd` (SUBST_ALL_TAC o SYM) >>
  `w2n w + 54 <= u.vs_alloca_next` by decide_tac >>
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM,exprSimWordArgsTheory.eval_exprs_nil,return_def] >>
  simp[Abbr `next`,bind_return] >>
  irule (SIMP_RULE (srw_ss()) [] (Q.INST [`salt` |-> `NONE`] create_proxy_dispatch_prepared_mods)) >>
  simp[NoAsms,dest_optional_salt_def,post_value_type_def,expr_type_def,
       expr_has_effect_def,supported_expr_exists_def,expr_effect_root_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexistsl_tac [`env`,`mods`] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`w2w tw`,`y`,`aw`,`p`,`c`,`NONE`,`w`] >>
  simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_proxy_forced_mods[salted]:
  map_every (fn pat => qpat_x_assum pat
    (strip_assume_tac o SIMP_RULE (srw_ss()) [proxy_salt_some,gas_shadow_expr_type]))
    [`compile_create_salt compile_expr cenv _ c = _`,
     `compile_create_salt compile_expr (gas_shadow_env T cenv) _ ch = _`] >>
  qpat_x_assum `sop = SOME _` SUBST_ALL_TAC >>
  qpat_x_assum `SOME _ = SOME _` (SUBST_ALL_TAC o REWRITE_RULE [SOME_11]) >>
  irule create_proxy_salt_cut_mods >> BETA_TAC >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qexistsl_tac [`G0`,`BaseT AddressT`,`[target;amount;salt]`,`c`,`ch`,`d`,`dflt`,
                `env`,`es`,`exps`,`ks`,`mods`,`q`,`rof`,`s0`,`sa`,`sd`,`dh`,
                `shadow_func`,`src`,`tn0`,`tops`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- simp[] >>
  qx_genl_tac [`sv`,`sw`,`ew`,`Gend`,`tt`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "salted_dispatch"
QED

Resume create_proxy_forced_mods[salted_dispatch]:
  qpat_assum `wb_frame cenv ea ew c u t`
    (mp_then Any (drule_all_then strip_assume_tac) create_proxy_salt_window_kept_mods) >>
  `!H. valid_horizon cx st0 H ew.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ew t /\ immutable_frame_mods func cenv cx ew t /\
    storage_well_formed_on cx ew (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ew Gend tt t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ew.storage_trace ==> _`
       (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[NoAsms,Abbr `next`] >>
  irule (SIMP_RULE (srw_ss()) [] (Q.INST [`salt` |-> `SOME sv`] create_proxy_dispatch_prepared_mods)) >>
  simp[NoAsms,dest_optional_salt_def,post_value_type_def,expr_type_def,
       expr_has_effect_def,supported_expr_exists_def,expr_effect_root_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexistsl_tac [`env`,`mods`] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`w2w tw`,`y`,`aw`,`p`,`sd`,`SOME q`,`SOME sw`,`w`] >>
  simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise create_proxy_forced_mods
