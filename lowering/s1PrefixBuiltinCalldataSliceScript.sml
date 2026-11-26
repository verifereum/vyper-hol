(* Request-prefix companion to bodyFullBuiltinCalldataSlice. *)
Theory s1PrefixBuiltinCalldataSlice
Ancestors
  s1PrefixPreds bodyFullBuiltinCalldataSlice s1PrefixDefs
  s1PrefixBuiltinBytestringCalldataCase s1PrefixOfVV
  exprSimHash exprSimCalldataSlice externalEntryShape[qualified,ignore_grammar]
  gasShadowCompileStmtHelpers gasShadowState exprLoweringProps context
  fragExec compileEnv vyperInterpreter vyperState list pair
  gasShadow exprLowering exprSimSource vyperContext
Libs
  dep_rewrite

Theorem calldata_slice_vv_sim_prefix:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann n args es.
  (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
      body_exprs_full_ok cx args) /\
  (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
      body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (CalldataSlice n) args) es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (CalldataSlice n) args) es
Proof
  rpt gen_tac >> strip_tac >> drule_all calldata_slice_body_operand_prefix >>
  disch_then (qspecl_then [`shadow_func`,`lo`,`func`,`d`,`PG`,`DF`]
    strip_assume_tac) >> gvs[] >>
  pure_rewrite_tac[expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lower_value compile_expr cenv (BaseT (UintT 256)) e sa` >>
  rename1 `_ = (x,sm)` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (BaseT (UintT 256))
      (gas_shadow_expr e) shadow_sa` >>
  rename1 `_ = (shadow_x,shadow_sm)` >>
  `x = shadow_x /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (lower_value compile_expr cenv (BaseT (UintT 256)) e)
       (lower_value compile_expr (gas_shadow_env T cenv) (BaseT (UintT 256))
         (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  qpat_x_assum `x = shadow_x` (SUBST_ALL_TAC o SYM) >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    (qpat_x_assum `compile_expr _ _ (Builtin _ (CalldataSlice _) _) _ = _` mp_tac >>
     qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def,gas_shadow_builtin_def,compile_calldata_slice_parts] >>
     Cases_on `compile_slice_calldata x (Lit (n2w n))
       (type_memory_bytes cenv (BaseT (BytesT (Dynamic m)))) sm` >>
     Cases_on `compile_slice_calldata x (Lit (n2w n))
       (type_memory_bytes cenv (BaseT (BytesT (Dynamic m)))) shadow_sm` >>
     simp[as_ptr_val_def,comp_return_def] >> rpt strip_tac >> gvs[] >>
     metis_tac[externalEntryShapeTheory.compile_slice_calldata_labels,SND]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[cj 2 compile_expr_grows] >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def,expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!qe. SND (eval_expr cx (Builtin (BaseT (BytesT (Dynamic m))) (CalldataSlice n) [e]) qe) =
        SND (bind (eval_expr cx e) (read_result cx) qe)` by
    (gen_tac >> DEP_REWRITE_TAC[eval_expr_unary_builtin_action] >>
     simp[precompile_builtin_def,builtin_args_length_ok_def,is_self_codesize_def] >>
     Cases_on `bind (eval_expr cx e) (read_result cx) qe` >>
     rename1 `_ = (res,ee)` >> Cases_on `res` >> simp[bind_def]) >>
  metis_tac[gas_prefix_full_state_cong]
QED

Theorem calldata_slice_expr_sim_prefix:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann n args es.
  (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
      body_exprs_full_ok cx args) /\
  (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
      body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (CalldataSlice n) args) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (CalldataSlice n) args) es
Proof
  rpt strip_tac >> irule expr_sim_prefix_of_vv >>
  irule calldata_slice_vv_sim_prefix >> metis_tac[]
QED
