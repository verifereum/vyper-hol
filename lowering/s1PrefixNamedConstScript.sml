(* NamedConst evaluates and emits the same interval as its sole operand. *)
Theory s1PrefixNamedConst
Ancestors
  s1PrefixDefs s1PrefixPreds s1PrefixOfVV bodyFullNamedConst exprBodyPreProps
  exprSimSource gasShadowCompile gasShadowState gasShadow vyperTypeSystem
  vyperTypeBuiltins vyperContext vyperInterpreter vyperState vyperAST
  context list

Theorem named_const_vv_prefix[local]:
  well_typed_expr env (Builtin ann NamedConst [e]) /\
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty e es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann NamedConst [e]) es
Proof
  strip_tac >>
  `expr_type e = ann /\ named_const_operand e /\ well_typed_expr env e` by
    gvs[well_typed_expr_def, well_typed_builtin_app_def, builtin_operands_ok_def] >>
  drule_then assume_tac named_const_eval >>
  pure_rewrite_tac[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (raw,sm)` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa` >>
  rename1 `_ = (shraw,shadow_sm)` >>
  `gas_shadow_compiles (compile_expr cenv ty e)
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  `shraw = raw` by
    (qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[]) >>
  drule_all named_const_operand_shape >> simp[] >> strip_tac >>
  `(!n. vv_operand raw <> Label n) /\
   (if is_word_type ann then ?op. raw = StackValue ann op
    else ?p. raw = LocatedValue ann p /\ p.ptr_location = LocMemory)` by
    (Cases_on `is_word_type ann` >> gvs[vv_operand_def]) >>
  `compile_expr cenv ty (Builtin ann NamedConst [e]) sa =
    ((if is_word_type ann then raw
      else LocatedValue ann (mk_ptr (vv_operand raw) LocMemory)),sm)` by
    (irule named_const_parent_compile >> simp[]) >>
  `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Builtin ann NamedConst [e])) shadow_sa =
    ((if is_word_type ann then raw
      else LocatedValue ann (mk_ptr (vv_operand raw) LocMemory)),shadow_sm)` by
    (simp[NoAsms, Once gas_shadow_expr_def, gas_shadow_builtin_def] >>
     irule named_const_parent_compile >> fs[]) >>
  gvs[] >>
  qpat_x_assum `expr_vv_sim_prefix _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`raw`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[] >> disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem named_const_expr_prefix_ok:
  !cx ann args.
    (!s x t.
       type_check (builtin_args_length_ok NamedConst (LENGTH args)) "Builtin args" s =
       (INL x,t) /\ NamedConst <> Len /\ NamedConst <> Env MsgGas /\
       code_slice_source NamedConst args = NONE ==>
       body_exprs_prefix_ok cx args) ==>
    body_expr_prefix_ok cx (Builtin ann NamedConst args)
Proof
  rpt gen_tac >> strip_tac >> once_rewrite_tac[body_expr_prefix_ok_def] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac expr_body_pre_static_facts >>
  `builtin_args_length_ok NamedConst (LENGTH args)` by
    (qpat_assum `well_typed_expr _ (Builtin _ _ _)`
       (mp_tac o ONCE_REWRITE_RULE [well_typed_expr_def]) >>
     strip_tac >> drule well_typed_builtin_app_length >> simp[]) >>
  `body_exprs_prefix_ok cx args` by
    (first_x_assum (qspecl_then [`es`,`()`,`es`] mp_tac) >>
     simp[type_check_def, assert_def, code_slice_source_def]) >>
  gvs[builtin_args_length_ok_def, LENGTH_EQ_1, body_exprs_prefix_ok_def] >>
  rename1 `body_expr_prefix_ok cx e` >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  conj_asm2_tac >- (irule expr_sim_prefix_of_vv >> first_assum ACCEPT_TAC) >>
  irule named_const_vv_prefix >> conj_tac
  >- (qexists_tac `env` >> simp[]) >>
  qpat_x_assum `body_expr_prefix_ok _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  metis_tac[]
QED
