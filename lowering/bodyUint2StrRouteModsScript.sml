(* Linked Uint2Str: run the forced word, then materialize its decimal string. *)
Theory bodyUint2StrRouteMods
Ancestors
  bodyUint2StrInputMods bodyUint2StrCodeMods bodyUint2StrReachedBindMods
  bodyUint2StrSuffixMods bodyFullPredsMods bodyFullPostsMods
  bodyAggregateReadMods bodyAggregateReadPostMods bodyFullShared
  exprSimUint2Str exprSimSliceCompose exprSimHash exprLoweringProps
  gasShadowCompileStmtHelpers exprLowering context vyperInterpreter vyperState vyperContext
  exprSimDefs gasSummary fragExec compileEnv vyperAST
Libs monadsyntax

val ann = ``BaseT (StringT n)``;
val E = ``Builtin ^ann (Uint2Str n) [e]``;
val action = ``\v (u:evaluation_state). ((case builtin_result cx u.accounts ^ann (Uint2Str n)
  [expr_type e] [v] of INL w => INL (Value w) | INR exc => INR exc),u)``;

Theorem uint2str_eval_action[local]:
  eval_expr cx ^E = bind (bind (eval_expr cx e) (read_result cx)) ^action
Proof
  irule eval_expr_unary_builtin_action >>
  simp[precompile_builtin_def,builtin_args_length_ok_def,is_self_codesize_def]
QED

Theorem uint2str_eval_value[local]:
  eval_expr cx ^E es = (INL raw,ee) ==> ?v. raw = Value v
Proof
  simp[uint2str_eval_action,bind_def,AllCaseEqs()] >> metis_tac[]
QED

Theorem uint2str_vv_route_mods[local]:
  expr_body_pre_mods mods ce cx env ^E es /\
  expr_body_pre_mods mods ce cx env e es /\ expr_type e = BaseT (UintT k) /\
  LENGTH (num_to_dec_string (2 ** k - 1)) <= n /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty ^E es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`op`,`sm`,`shm`] strip_assume_tac)
    uint2str_code_cuts_mods >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (qpat_assum `gas_admissible (eval_expr _ _) _ _` mp_tac >>
     rewrite_tac[uint2str_eval_action] >> MATCH_ACCEPT_TAC slice_gas_admissible_expr_head) >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _`
    (drule_all_then assume_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  irule uint2str_reached_bind_mods >>
  qexists_tac `\H v ee G tn t.
    expr_post_mods H ctx func ce cx e es sa sm s0 ee v op t /\
    expr_store_bound cx (post_value_type ce e) v op t /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn t /\
    ptr_val_ok cx (post_value_type ce e) v op G tn t /\
    (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G t) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn` >>
  BETA_TAC >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qx_genl_tac [`marks`,`v`,`mid`,`G`,`tn`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >> BETA_TAC >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  irule (CONV_RULE (DEPTH_CONV BETA_CONV) uint2str_reached_suffix_mods) >>
  rpt (goal_assum (drule_at Any)) >>
  conj_tac >- (qexists_tac `marks` >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists_tac `k` >> asm_rewrite_tac[]) >>
  conj_tac >- (map_every qexists_tac [`op`,`sm`,`ty`] >> asm_rewrite_tac[]) >>
  map_every qexists_tac [`env`,`mods`] >> asm_rewrite_tac[]
QED

Theorem uint2str_read_cut[local]:
  lower_value compile_expr ce ty ^E sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr ^E) sha = (op,shb) /\
  gas_shadow_state sa sha ==>
  compile_expr ce ty ^E sa = (LocatedValue ^ann (mk_ptr op LocMemory),sb) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr ^E) sha =
    (LocatedValue ^ann (mk_ptr op LocMemory),shb)
Proof
  strip_tac >> Cases_on `compile_expr ce ty ^E sa` >>
  drule_then (qx_choosel_then [`x`,`sm`] strip_assume_tac) uint2str_compile_cut >>
  Cases_on `compile_uint2str x n (type_memory_bytes ce ^ann) sm` >>
  gvs[as_ptr_val_def] >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr ^E) sha` >>
  `gas_shadow_compiles (compile_expr ce ty ^E)
     (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr ^E))` by
    MATCH_ACCEPT_TAC gas_shadow_stmt_compile_expr_env >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  gvs[lower_value_def,comp_bind_def,unwrap_value_def,mk_ptr_def,is_word_type_def,comp_return_def]
QED

Theorem uint2str_value_route_mods[local]:
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty ^E es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty ^E es
Proof
  strip_tac >> irule materialized_value_from_vv_mods >>
  qpat_assum `expr_vv_sim_full_mods _ _ _ _ _ _` (irule_at Any) >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_then ACCEPT_TAC uint2str_eval_value) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac uint2str_read_cut >>
  qexists_tac `LocatedValue ^ann (mk_ptr op LocMemory)` >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `raw = Value v` SUBST_ALL_TAC >>
  `~is_word_type ^ann /\ (mk_ptr op LocMemory).ptr_location = LocMemory` by
    simp[is_word_type_def,mk_ptr_def] >>
  `ptr_buf_ok ce ^E (mk_ptr op LocMemory).ptr_operand G t` by
    (qpat_assum `!b p. LocatedValue _ _ = LocatedValue b p /\ _ ==> ptr_buf_ok _ _ _ _ _`
       (qspecl_then [`^ann`,`mk_ptr op LocMemory`] mp_tac) >> simp[]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) memory_buffer_read_post_mods >>
  fs[mk_ptr_def]
QED

Theorem uint2str_route_mods:
  (builtin_args_length_ok (Uint2Str n) (LENGTH args) ==>
    body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods ce cx env (Builtin ann (Uint2Str n) args) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Builtin ann (Uint2Str n) args) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Builtin ann (Uint2Str n) args) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (qx_choosel_then [`e`,`k`] strip_assume_tac) uint2str_input_mods >>
  qpat_x_assum `args = [e]` SUBST_ALL_TAC >>
  qpat_x_assum `ann = BaseT (StringT n)` SUBST_ALL_TAC >>
  `body_expr_full_ok_mods mods exps cx e` by
    (qpat_x_assum `builtin_args_length_ok _ _ ==> _` mp_tac >>
     simp[builtin_args_length_ok_def,Once body_exprs_full_ok_mods_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     qpat_assum `!df l0 d0 pg src tops ctx shctx f shf ce env ty ee.
                  _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
       (irule o GEN_ALL o cj 1 o SPEC_ALL o REWRITE_RULE [IMP_CONJ_THM]) >>
     rpt (goal_assum (drule_at Any)) >>
     conj_tac >- (map_every qexists_tac [`src`,`tops`] >> asm_rewrite_tac[]) >>
     qexists_tac `env` >> asm_rewrite_tac[]) >>
  reverse conj_asm2_tac
  >- (irule uint2str_vv_route_mods >> rpt (goal_assum (drule_at Any)) >>
      conj_tac >- (qexists_tac `k` >> asm_rewrite_tac[]) >>
      map_every qexists_tac [`env`,`mods`] >> asm_rewrite_tac[]) >>
  drule_then ACCEPT_TAC uint2str_value_route_mods
QED
