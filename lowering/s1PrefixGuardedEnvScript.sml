(* Lower guarded environment builtin prefix case below the dispatcher. *)
Theory s1PrefixGuardedEnv
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixOfVV s1PrefixBuiltinLeaves
  s1PrefixBuiltinEnvHashCompose s1PrefixBuiltinEnvAccountCompose
  bodyFullBuiltinEnvAccountRun bodyFullBuiltinEnvBlockHashSuffix
  bodyFullBuiltinEnvBlobHashSuffix exprSimLen exprSimHash exprSimAccounts
  exprBodyPreProps exprLoweringProps exprBopLowering exprSimUnwrap
  gasShadowCompileStmtHelpers bodyFullShared gasShadowCompile gasShadow gasShadowState fragExec
  vyperStorageTrace vyperStatePreservation allocLimits bodyFullPreds
  builtinSystem compileEnv exprLowering exprSimSource exprSimBuiltins
  exprSimHyps exprSimHypsDefs vyperAST vyperInterpreter vyperTypeSystem
  vyperTypeBuiltins vyperState vyperContext
Libs
  pairLib

Theorem env_builtin_expr_prefix_ok:
  !cx ty bt es.
  (bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i /\ i <> MsgGas) \/
     (?i. bt = Acc i) \/ bt = BlockHash \/ bt = BlobHash \/ bt = MethodId) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len ==>
       body_exprs_full_ok cx es) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len ==>
       body_exprs_prefix_ok cx es) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_full_ok cx (HD es)) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_prefix_ok cx (HD es)) ==>
  body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  ONCE_REWRITE_TAC [body_expr_prefix_ok_def] >>
  reverse conj_tac
  >- (qpat_x_assum `bt = Len \/ _` strip_assume_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `builtin_args_length_ok bt (LENGTH es)`)
  >- metis_tac[builtin_bad_arity_sim_prefix] >>
  Cases_on `bt = BlockHash \/ bt = BlobHash` >- suspend "hash" >>
  qpat_x_assum `bt = Len \/ _` strip_assume_tac >> gvs[]
  >- suspend "len"
  >- metis_tac[calldatalen_sim_prefix]
  >- metis_tac[env_item_sim_prefix]
  >- suspend "account" >>
  suspend "method"
QED

Resume env_builtin_expr_prefix_ok[len]:
  drule len_pre_args >> strip_tac >> gvs[] >>
  `body_expr_prefix_ok cx e` by (fs[type_check_def, assert_def] >> metis_tac[]) >>
  `expr_body_pre cenv cx env e es'` by
    (irule expr_body_pre_builtin_arg >> conj_tac
     >- metis_tac[expr_body_pre_static_facts] >>
     qexistsl [`BaseT (UintT 256)`, `[e]`, `Len`, `es'`] >> simp[]) >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty' e es'` by
    (qpat_x_assum `body_expr_prefix_ok _ _` (mp_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     metis_tac[]) >>
  conj_asm2_tac >- metis_tac[expr_sim_prefix_of_vv] >>
  PURE_REWRITE_TAC[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `compile_expr _ _ (Builtin _ Len _) _ = _` mp_tac >>
  simp[compile_expr_len] >> pairarg_tac >> simp[as_stack_val_pair] >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def, gas_shadow_builtin_def, compile_expr_len] >>
  pairarg_tac >> simp[as_stack_val_pair] >> strip_tac >>
  rename1 `compile_expr cenv ty' e sa = (evv,sm)` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) shadow_sa = (evv',sm')` >>
  `evv' = evv /\ gas_shadow_state sm sm'` by
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `compile_expr _ _ e sa = _` (irule_at Any) >>
     qpat_assum `compile_expr _ _ (gas_shadow_expr e) shadow_sa = _` (irule_at Any) >>
     simp[] >> irule gas_shadow_stmt_compile_expr_env) >>
  `cs_extends sa sm /\ cs_extends shadow_sa sm'` by metis_tac[compile_expr_extends] >>
  `cs_extends sm sb /\ cs_extends sm' shadow_sb` by
    (fs[as_stack_val_pair] >> conj_tac >> irule len_load_extends >>
     metis_tac[pairTheory.PAIR]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa sm' shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es'` by metis_tac[len_operand_admissible] >>
  `!qe. SND (eval_expr cx (Builtin (BaseT (UintT 256)) Len [e]) qe) =
        SND (eval_expr cx e qe)` by
    (gen_tac >> simp[eval_expr_len] >> Cases_on `eval_expr cx e qe` >>
     rename1 `_ = (res,mid)` >> Cases_on `res` >> simp[bind_def] >>
     Cases_on `result_array_length cx x mid` >> drule result_array_length_state >>
     strip_tac >> gvs[] >> rename1 `result_array_length cx _ _ = (r,_)` >>
     Cases_on `r` >> simp[bind_def, return_def]) >>
  drule gas_prefix_full_state_cong >> disch_then (fn th => simp[th]) >>
  qpat_x_assum `expr_vv_sim_prefix _ _ _ _ e es'`
    (mp_tac o REWRITE_RULE[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`sm'`,`evv`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[] >> disch_then irule >> first_assum ACCEPT_TAC
QED

Resume env_builtin_expr_prefix_ok[account]:
  drule expr_body_pre_static_facts >> strip_tac >>
  `i <> Code` by fs[allocLimitsTheory.alloc_limits_expr_def] >>
  `?e. es = [e] /\ ty = account_item_type i /\ expr_type e = BaseT AddressT` by
    (fs[cj 9 well_typed_expr_def, well_typed_builtin_app_def] >>
     Cases_on `es` >> gvs[] >> rename1 `h::rest` >> Cases_on `rest` >> gvs[]) >>
  gvs[] >>
  conj_asm1_tac
  >- (mp_tac account_prefix_from_suffix >>
      (impl_tac >- (rpt (pop_assum kall_tac) >> rpt gen_tac >> strip_tac >>
        drule_all account_suffix_full_run >>
        disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
        qexistsl [`t`, `G'`, `tn'`] >> simp[])) >>
      disch_then irule >>
      fs[type_check_def, assert_def] >> metis_tac[]) >>
  irule expr_vv_sim_stack_prefix >> simp[compile_acc_stack] >>
  metis_tac[eval_expr_builtin_value]
QED

Resume env_builtin_expr_prefix_ok[hash]:
  `bt <> Len` by (Cases_on `bt = BlockHash` >> gvs[]) >>
  `body_exprs_full_ok cx es /\ body_exprs_prefix_ok cx es` by
    (fs[type_check_def, assert_def] >> metis_tac[]) >>
  conj_asm1_tac
  >- (mp_tac hash_builtin_value_prefix_from_suffixes >>
      (impl_tac >- (conj_tac >-
        (map_every qx_gen_tac [`arg`,`sa`,`op`,`sb`,`func`,`st0`,`suffix_cenv`,`suffix_cx`,
           `mid`,`s`,`suffix_ctx`,`DF`,`lo`,`d`,`G`,`tn`,`explicit`,`PG`,`i`] >>
        strip_tac >>
        mp_tac (Q.SPECL [`arg`,`sa`,`op`,`sb`,`func`,`st0`,`suffix_cenv`,`suffix_cx`,
          `mid`,`s`,`suffix_ctx`,`DF`,`lo`,`d`,`G`,`tn`,`explicit`,`PG`,`i`]
          blockhash_full_suffix) >>
        (impl_tac >- simp[]) >>
        disch_then (qx_choosel_then [`r`,`G'`,`tn'`] assume_tac) >>
        qexistsl [`r`,`G'`,`tn'`] >> rpt strip_tac >> first_x_assum drule >>
        Cases_on `unop_result suffix_cx (BaseT (BytesT (Fixed 32))) BlockHash
          [BaseT (UintT 256)] (IntV i) mid` >> simp[]) >>
        rpt gen_tac >> strip_tac >> irule blobhash_full_suffix >>
        simp[] >> qexists_tac `arg` >> simp[])) >>
      disch_then irule >> fs[type_check_def, assert_def] >> metis_tac[]) >>
  irule expr_vv_sim_stack_prefix >>
  Cases_on `bt = BlockHash` >> gvs[compile_blockhash_stack, compile_blobhash_stack] >>
  metis_tac[eval_expr_builtin_value]
QED

Resume env_builtin_expr_prefix_ok[method]:
  `?e. es = [e]` by
    (Cases_on `es` >> gvs[builtin_args_length_ok_def] >>
     rename1 `h::rest` >> Cases_on `rest` >> gvs[]) >> gvs[] >>
  Cases_on `method_id_literal e = NONE`
  >- (suspend "method_runtime") >>
  `?la l. e = Literal la l` by
    (Cases_on `e` >> gvs[method_id_literal_def] >> metis_tac[]) >> gvs[] >>
  Cases_on `method_id_literal (Literal la l)` >> gvs[method_id_literal_sim_prefix]
QED

Resume env_builtin_expr_prefix_ok[method_runtime]:
  `body_expr_prefix_ok cx e` by
    (fs[type_check_def, assert_def, body_exprs_prefix_ok_def] >> metis_tac[]) >>
  `expr_body_pre cenv cx env e es'` by
    (irule expr_body_pre_builtin_arg >> conj_tac
     >- metis_tac[expr_body_pre_static_facts] >>
     qexistsl [`ty`, `[e]`, `MethodId`, `es'`] >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es'` by
    (qpat_x_assum `body_expr_prefix_ok _ _` (mp_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     metis_tac[]) >>
  conj_asm2_tac >- metis_tac[expr_sim_prefix_of_vv] >>
  PURE_REWRITE_TAC[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `compile_expr _ _ (Builtin _ MethodId _) _ = _` mp_tac >>
  simp[compile_method_id_singleton_runtime] >> pairarg_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def, gas_shadow_builtin_def, compile_method_id_singleton_runtime,
       gas_shadow_expr_type] >> pairarg_tac >> strip_tac >>
  rename1 `lower_value _ cenv _ e sa = (x,sm)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (x',sm')` >>
  `x' = x /\ gas_shadow_state sm sm'` by
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = _` (irule_at Any) >>
     simp[] >> irule gas_shadow_stmt_lower_value_env) >>
  `cs_extends sa sm /\ cs_extends shadow_sa sm'` by metis_tac[compile_expr_grows] >>
  `cs_extends sm sb /\ cs_extends sm' shadow_sb` by
    (`!ctype op fixed a. cs_extends a (SND (compile_method_id_runtime ctype op fixed a))` by
       (rpt (pop_assum kall_tac) >>
        mp_tac (cj 5 hash_suffix_appends) >> simp[cs_appends_def] >> metis_tac[pairTheory.PAIR]) >>
     Cases_on `ty = BaseT (BytesT (Fixed 4))` >> gvs[as_stack_val_pair, as_ptr_val_pair]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa sm' shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es'` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `!qe. SND (eval_expr cx (Builtin ty MethodId [e]) qe) =
        SND (bind (eval_expr cx e) (read_result cx) qe)` by
    (`eval_expr cx (Builtin ty MethodId [e]) =
       bind (bind (eval_expr cx e) (read_result cx))
        (\v s. ((case builtin_result cx s.accounts ty MethodId [expr_type e] [v]
                    of INL w => INL (Value w) | INR exc => INR exc),s))` by
       (irule eval_expr_unary_builtin_action >>
        simp[precompile_builtin_def, is_self_codesize_def, builtin_args_length_ok_def]) >>
     pop_assum SUBST1_TAC >> gen_tac >> Cases_on `bind (eval_expr cx e) (read_result cx) qe` >>
     rename1 `_ = (res,mid)` >> Cases_on `res` >> simp[bind_def]) >>
  drule gas_prefix_full_state_cong >> disch_then (fn th => simp[th]) >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ e es'`
    (mp_tac o REWRITE_RULE[expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`sm'`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  gvs[] >> disch_then irule >> first_assum ACCEPT_TAC
QED

Finalise env_builtin_expr_prefix_ok
