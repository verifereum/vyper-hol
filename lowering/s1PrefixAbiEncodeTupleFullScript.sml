(* Request-prefix companion to bodyFullAbiEncodeTupleFull. *)
Theory s1PrefixAbiEncodeTupleFull
Ancestors
  s1PrefixPreds bodyFullAbiEncodeTupleFull s1PrefixDefs
  s1PrefixExtCallPosList s1PrefixOfVV exprBodyPreProps
  exprSimAbiEncodeRuntimeInputs abiEncodeArgsCase gasShadowCompileHelpers
  gasShadowCompile gasShadowState vyperState vyperTypeSystem vyperAST exprLowering

Theorem abi_encode_tuple_vv_prefix_from_packaging:
  !tops ctx ce cx env ann ensure mid ty args es DF lo d shadow_ctx PG func shadow_func cty.
  body_inv tops ctx ce cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\
  (!s'' x t. type_check
      (type_builtin_args_length_ok (AbiEncode ensure mid) (LENGTH args))
      "TypeBuiltin args" s'' = (INL x,t) ==> body_exprs_full_ok cx args) /\
  (!s'' x t. type_check
      (type_builtin_args_length_ok (AbiEncode ensure mid) (LENGTH args))
      "TypeBuiltin args" s'' = (INL x,t) ==> body_exprs_prefix_ok cx args) ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx cty (TypeBuiltin ann (AbiEncode ensure mid) ty args) es
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_static_facts >> strip_tac >>
  `1 <= LENGTH args` by
    (Cases_on `args` >> simp[] >>
     qpat_x_assum `well_typed_expr _ _` mp_tac >>
     simp[Once well_typed_expr_def, well_typed_type_builtin_args_def]) >>
  `type_check (type_builtin_args_length_ok (AbiEncode ensure mid) (LENGTH args))
        "TypeBuiltin args" es = (INL (),es)` by
    simp[type_check_def, vyperContextTheory.type_builtin_args_length_ok_def, assert_def, return_def] >>
  `body_exprs_full_ok cx args /\ body_exprs_prefix_ok cx args` by metis_tac[] >>
  rewrite_tac[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `compile_expr _ _ _ sa = _`) compile_abi_encode_body_layout >>
  disch_then drule_all >>
  disch_then (qx_choosel_then [`svs`,`st`,`out`] strip_assume_tac) >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) shadow_sa = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def] >> strip_tac >>
  drule_at (Pat `compile_expr _ _ _ shadow_sa = _`) compile_abi_encode_body_layout >>
  disch_then drule_all >>
  disch_then (qx_choosel_then [`shadow_svs`,`shadow_st`,`shadow_out`] strip_assume_tac) >>
  `gas_shadow_compiles (compile_abi_encode_args compile_expr ce args)
     (compile_abi_encode_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr args))` by
    (irule (SIMP_RULE bool_ss []
       (Q.INST [`sh` |-> `T`] gas_shadow_compiles_abi_encode_args_env)) >>
     simp[cj 1 gas_shadow_compile_expr_env]) >>
  `shadow_svs = svs /\ gas_shadow_state st shadow_st` by
    (qpat_x_assum `gas_shadow_compiles _ _` mp_tac >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `shadow_svs = svs` SUBST_ALL_TAC >>
  `!e q. MEM e args /\ expr_sim_inv ce cx env q ==> expr_body_pre ce cx env e q`
     by metis_tac[abi_args_body_pre_arg] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_exprs cx args) (es,s0,G0,tn0)` by
    (irule (Q.INST [`kw_es` |-> `[]:expr list`]
       extcall_request_positional_packing_prefix) >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`ce`,`d`,`env`,`sa`,`st`,`shadow_func`,`shadow_sa`,
                   `shadow_st`,`svs`,`tops`] >>
     fs[compile_abi_encode_args_def, gasShadowCompileBaseTheory.lowered_value_type_gas_shadow_env]) >>
  drule (Q.INST [`target` |-> `ty`] eval_expr_abi_encode_action) >>
  disch_then (fn th => rewrite_tac[th]) >>
  `!q. SND (bind (eval_exprs cx args)
       (\vs ee. ((case evaluate_type_builtin cx (AbiEncode ensure mid) ty (MAP expr_type args) vs of
                   INL w => INL (Value w) | INR err => INR (Error err)),ee)) q) =
       SND (eval_exprs cx args q)` by
    (gen_tac >> Cases_on `eval_exprs cx args q` >> rename1 `_ = (res,ee)` >>
     Cases_on `res` >> simp[bind_def]) >>
  drule gas_prefix_full_state_cong >> simp[]
QED
