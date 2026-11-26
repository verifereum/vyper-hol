(* The forced decimal prefix and source bind for linked Ceil and Floor. *)
Theory bodyWordRoundPrefixMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv exprBodyPreProps
  bodyScalarStackVVMods
  exprSimWordBuiltins exprWordOperand exprSimUnopProps exprSimUnopComposeProps exprSimSource
  gasShadowCompileStmtHelpers gasShadowState gasShadow gasExemptCertMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods vyperStorageTrace
  vyperTypeInvariants vyperTypeSystem vyperInterpreter vyperContext vyperAST
  vyperTypeCallGraph vyperStorageFootprint gasContext exprSimDefs loweringStateRelDefs
  supportedExprTraverse allocLimits exprSimHypsDefs exprSimMemDefs
  bodyPtrDefs loweringPosts exprLoweringProps compileEnv fragExec list finite_map

Theorem round_child[local]:
  (bt = Ceil \/ bt = Floor) /\
  (builtin_args_length_ok bt (LENGTH args) ==>
     body_exprs_full_ok_mods mods exps cx args) /\
  expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
  ?e. args = [e] /\ a = BaseT (IntT 256) /\ expr_type e = BaseT DecimalT /\
      expr_body_pre_mods mods cenv cx env e es /\ body_expr_full_ok_mods mods exps cx e
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `a = BaseT (IntT 256) /\ MAP expr_type args = [BaseT DecimalT]` by
    (drule expr_body_pre_mods_well_typed >> rewrite_tac[Once well_typed_expr_def] >>
     strip_tac >> Cases_on `bt = Ceil` >>
     gvs[well_typed_builtin_app_def, LENGTH_EQ_NUM_compute]) >>
  `builtin_args_length_ok bt 1` by
    (Cases_on `bt = Ceil` >> gvs[builtin_args_length_ok_def]) >>
  qpat_x_assum `bt = Ceil \/ bt = Floor` (mk_asm "rounding") >>
  Cases_on `args` >> gvs[] >>
  `body_expr_full_ok_mods mods exps cx h` by
    ((qpat_assum `body_exprs_full_ok_mods _ _ _ [_]` mp_tac >>
     simp[Once body_exprs_full_ok_mods_def] >> (gvs[Once body_exprs_full_ok_mods_def]))) >>
  simp[] >>
  asm "rounding" strip_assume_tac >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Builtin _ _ _) _` mp_tac >>
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def, DISJ_IMP_THM,
       FORALL_AND_THM, constSubstCorrectTheory.frame_well_typed_exprs_cons]
QED

Theorem round_lower[local]:
  (bt = Ceil \/ bt = Floor) /\
  lower_value compile_expr cenv ty (Builtin ann bt [e]) sa = (op,sb) ==>
  ?x s1. lower_value compile_expr cenv ty e sa = (x,s1) /\
    (if bt = Ceil then compile_ceil x 10000000000 else compile_floor x 10000000000)
      s1 = (op,sb)
Proof
  Cases_on `bt = Ceil` >> simp[] >> metis_tac[lower_value_ceil, lower_value_floor]
QED

Theorem round_extends[local]:
  (bt = Ceil \/ bt = Floor) /\
  (if bt = Ceil then compile_ceil x 10000000000 else compile_floor x 10000000000)
    s1 = (op,sb) ==> cs_extends s1 sb
Proof
  Cases_on `bt = Ceil` >> simp[] >>
  metis_tac[straight_fresh_cs_extends, straight_fresh_ceil, straight_fresh_floor]
QED

Theorem round_cuts[local]:
  (bt = Ceil \/ bt = Floor) /\
  lower_value compile_expr cenv ty (Builtin ann bt [e]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann bt [e])) shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?x s1 shadow_s1. lower_value compile_expr cenv ty e sa = (x,s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
      (x,shadow_s1) /\ gas_shadow_state s1 shadow_s1 /\
    (if bt = Ceil then compile_ceil x 10000000000 else compile_floor x 10000000000)
      s1 = (op,sb) /\
    fn_has_code sa s1 func /\ fn_has_code s1 sb func /\
    fn_has_code shadow_sa shadow_s1 shadow_func
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `lower_value _ cenv _ (Builtin _ _ _) _ = _`
    (mp_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac round_lower) >>
  disch_then (drule_then strip_assume_tac) >>
  `lower_value compile_expr (gas_shadow_env T cenv) ty
    (Builtin ann bt [gas_shadow_expr e]) shadow_sa = (op,shadow_sb)` by
    (Cases_on `bt = Ceil` >> gvs[gas_shadow_expr_def, gas_shadow_builtin_def]) >>
  pop_assum (mp_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac round_lower) >>
  disch_then (drule_then strip_assume_tac) >>
  rename1 `lower_value _ _ _ (gas_shadow_expr _) shadow_sa = (shadow_x,shadow_s1)` >>
  `shadow_x = x /\ gas_shadow_state s1 shadow_s1` by
    (`gas_shadow_compiles (lower_value compile_expr cenv ty e)
        (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
       irule gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[]) >>
  qpat_x_assum `shadow_x = x` SUBST_ALL_TAC >>
  `cs_extends sa s1 /\ cs_extends shadow_sa shadow_s1` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends s1 sb /\ cs_extends shadow_s1 shadow_sb` by metis_tac[round_extends] >>
  qexistsl_tac [`x`,`s1`,`shadow_s1`] >> simp[] >> metis_tac[fn_has_code_split]
QED

Theorem round_operand_shape[local]:
  expr_body_pre_mods mods cenv cx env e es /\ expr_type e = BaseT DecimalT /\
  lower_value compile_expr cenv ty e sa = (x,s1) ==>
  cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
    (simp[well_formed_type_def] >> rpt strip_tac >>
     drule_all env_consistent_var_type_evaluates >> simp[]) >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all lower_value_word_shape >> simp[]
QED

Theorem round_stack[local]:
  (bt = Ceil \/ bt = Floor) /\
  compile_expr cenv ty (Builtin ann bt [e]) sa = (vv,sb) ==>
  ?op. vv = StackValue ann op
Proof
  Cases_on `bt = Ceil` >> simp[] >> strip_tac
  >- (drule compile_ceil_stack >> simp[]) >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) compile_word_builtin_stack >> simp[]
QED

Theorem round_arity[local]:
  bt = Ceil \/ bt = Floor ==>
  bt <> Len /\ ~precompile_builtin bt /\ builtin_args_length_ok bt 1 /\
  ~is_self_codesize bt [e]
Proof
  strip_tac >> gvs[builtin_args_length_ok_def, precompile_builtin_def,
                  is_self_codesize_def]
QED

(* These templates expand to the ordinary word success and exit posts. *)
fun round_q exp k p a =
  ``\(H:(bool # 256 word # type_value) list # num list) (res:value + exception) ee G tn t.
     ?v. res = INL v /\
     expr_post_mods H ctx func cenv cx ^exp es sa ^k s0 ee v ^p t /\
     expr_store_bound cx ^a v ^p t /\
     t.vs_current_bb = ^k.cs_current_bb /\ t.vs_inst_idx = LENGTH ^k.cs_current_insts /\
     alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
     s0.vs_alloca_next <= t.vs_alloca_next /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
     ptr_val_ok cx ^a v ^p G tn t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

val round_r = ``\(H:(bool # 256 word # type_value) list # num list) (res:value + exception) ee (gt:(string |-> num # num) # taint) r. expr_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;
val round_parent = ``Builtin (BaseT (IntT 256)) bt [e]``;
val round_next = ``\v ee. (unop_result cx (BaseT (IntT 256)) bt [expr_type e] v ee,ee)``;
val round_k = ``!mods cenv cx env e es bt x s1 op sb sa s0 G0 tn0 DF lo d ctx func PG
                 explicit st0 marks res mid G1 tn1 t.
    (bt = Ceil \/ bt = Floor) /\ expr_type e = BaseT DecimalT /\
    expr_body_pre_mods mods cenv cx env e es /\ body_const_cells_agree_mods mods cx env es /\
    (if bt = Ceil then compile_ceil x 10000000000 else compile_floor x 10000000000)
      s1 = (op,sb) /\
    (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
    cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
    fn_has_code s1 sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       ^(round_q ``e:expr`` ``s1:compile_state`` ``x:operand`` ``BaseT DecimalT``) H res mid G1 tn1 t /\
       ~t.vs_halted /\ mid.gas_obs = []) ==>
    ?v. res = INL v /\ gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG)
      cenv.ce_modules cx st0 (^round_next v) (mid,t,G1,tn1)
      ^(round_q round_parent ``sb:compile_state`` ``op:operand`` ``BaseT (IntT 256)``) ^round_r``;

Theorem round_sim_value[local]:
  ^round_k ==>
  !mods cenv cx env e es bt DF lo d ctx shadow_ctx PG func shadow_func ty.
    (bt = Ceil \/ bt = Floor) /\ expr_type e = BaseT DecimalT /\
    expr_body_pre_mods mods cenv cx env e es /\ body_const_cells_agree_mods mods cx env es /\
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty ^round_parent es
Proof
  disch_then (mk_asm "continue") >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac round_cuts >>
  drule_all_then strip_assume_tac round_operand_shape >>
  drule_then (qspec_then `e` strip_assume_tac) round_arity >>
  qpat_x_assum `bt = Ceil \/ bt = Floor` (mk_asm "rounding") >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >> qexistsl_tac [`BaseT (IntT 256)`,`bt`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ e es` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`shadow_s1`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  drule_all_then (rewrite_tac o single) eval_expr_unop_action_general >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> gvs[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_read_result]
  >~ [`storage_trace_frame _`]
  >- (Cases_on `bt = Ceil` >> gvs[storage_trace_frame_def, unop_result_def, is_self_codesize_def]) >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[Abbr `childR`] >> gen_tac >> Cases >> simp[expr_exit_def]) >>
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >> disj1_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qunabbrev_tac `childQ` >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> BETA_TAC >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `post_value_type cenv e = BaseT DecimalT` by
    (qpat_assum `expr_type e = BaseT DecimalT` (fn th => once_rewrite_tac[GSYM th]) >>
     irule post_value_type_word >> first_assum ACCEPT_TAC) >>
  qunabbrev_tac `childR` >> simp[NoAsms, expr_type_def, is_word_type_def] >>
  asm "continue" (match_mp_tac o CONV_RULE (DEPTH_CONV BETA_CONV)) >>
  qexistsl_tac [`mods`,`env`,`x`,`s1`,`marks`] >>
  conj_tac >- asm "rounding" ACCEPT_TAC >>
  simp[] >> qx_gen_tac `H` >> strip_tac >> qunabbrev_tac `childQ` >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> BETA_TAC >>
  qpat_assum `post_value_type cenv e = BaseT DecimalT`
    (fn ty_eq => disch_then (strip_assume_tac o REWRITE_RULE [ty_eq])) >>
  simp[]
QED

Theorem word_rounding_prefix_mods:
  ^round_k ==>
  !mods exps DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env cx ty a bt args es.
    (bt = Ceil \/ bt = Floor) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  disch_then (mk_asm "continue") >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac round_child >>
  qpat_x_assum `args = [_]` SUBST_ALL_TAC >>
  qpat_x_assum `a = BaseT _` SUBST_ALL_TAC >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (qpat_assum `body_expr_full_ok_mods _ _ _ e` mp_tac >>
     rewrite_tac[Once body_expr_full_ok_mods_def, IMP_CONJ_THM, FORALL_AND_THM] >>
     strip_tac >> qpat_assum `!DF lo d PG src tops ctx sh f sf ce en ty es.
       (_ ==> expr_sim_full_mods _ _ _ _ _ _) /\ _`
       (irule o CONJUNCT1 o SPEC_ALL) >>
     simp[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  conj_asm1_tac
  >- (asm "continue" (mp_tac o MATCH_MP round_sim_value) >>
      disch_then irule >> simp[] >> qexistsl_tac [`env`,`mods`] >> simp[]) >>
  `is_word_type (post_value_type cenv (Builtin (BaseT (IntT 256)) bt [e]))` by
    (dep_rewrite.DEP_REWRITE_TAC [post_value_type_word] >>
     simp[expr_type_def, is_word_type_def]) >>
  irule scalar_stack_vv_sim_full_mods >> simp[] >>
  conj_tac
  >- (gen_tac >> Cases_on `compile_expr cenv ty (Builtin (BaseT (IntT 256)) bt [e]) sa` >>
      drule_all_then strip_assume_tac round_stack >> simp[]) >>
  rpt strip_tac >> drule_then ACCEPT_TAC eval_expr_builtin_value
QED
