(* Joint finite-horizon Len simulation. *)
Theory bodyFullBuiltinEnvLen
Ancestors
  bodyFullShadowBodyInv
  bodyFullBuiltinEnvLenCompose bodyFullBuiltinEnvLenSuffix
  bodyFullExprGeneric bodyFullPreds bodyFullGhostFrame gasOutcomeFullCompose
  gasShadowCompileStmtHelpers exprSimLen exprSimSource exprSimWordArgs
  fragGasSeqPtr fragGasOriginPtr emitHelperProps allocaHistory
  loweringStateRelDefs ptrSafeRun ptrDiscipline instMemFrontier
  contextCodegenRel codegenRel unitTransformDefs memSafeRun
  vyperTypeSystem vyperTypeBuiltins list finite_map emitHelper compileEnv
  fragExec venomInst venomState exprSimHypsDefs bodySimFull vyperAST
  exprBopLowering exprLoweringProps exprLowering exprSimUnwrap gasShadowState
  bodyFullPredsMods[qualified] bodyInvSplit[qualified]

Theorem len_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    bt = Len /\ builtin_args_length_ok bt (LENGTH args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt <> Len ==>
      body_exprs_full_ok_mods mods exps cx args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt = Len ==>
      body_expr_full_ok_mods mods exps cx (HD args)) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule len_pre_args >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >>
     gvs[expr_body_pre_def]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty e es` by
    (qpat_x_assum `body_expr_full_ok _ _` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  conj_asm1_tac
  >- (rw[expr_sim_full_def] >> suspend "value") >>
  irule expr_vv_sim_stack_full >> simp[expr_type_def, is_word_type_def] >>
  conj_tac
  >- (gen_tac >> simp[compile_expr_len] >>
      Cases_on `compile_expr cenv ty e sa` >>
      simp[as_stack_val_pair]) >>
  metis_tac[eval_expr_builtin_value]
QED

Resume len_builtin_sim_full[value]:
  gvs[lower_value_def, compile_expr_len, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_expr cenv ty e sa = (evv,sm)` >>
  Cases_on `compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca
    (vv_operand evv) (case vv_location evv of NONE => LocMemory | SOME l => l) sm` >>
  gvs[as_stack_val_pair, unwrap_value_def, comp_return_def] >>
  drule_all len_load_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_shadow_compiles (compile_expr cenv ty e)
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
    irule gas_shadow_stmt_compile_expr_env >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`shadow_sa`] mp_tac o
     REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa` >> gvs[] >>
  gvs[gasShadowTheory.gas_shadow_expr_def, gasShadowTheory.gas_shadow_builtin_def, compile_expr_len,
      as_stack_val_pair, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[unwrap_value_def, comp_return_def] >>
  `cs_extends r shadow_sb` by metis_tac[len_load_extends] >>
  `cs_extends shadow_sa r` by metis_tac[compile_expr_extends] >>
  `fn_has_code shadow_sa r shadow_func` by metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[len_operand_admissible] >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`r`,`evv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> disch_tac >>
  simp[expr_type_def, is_word_type_def] >>
  match_mp_tac (SRULE [expr_type_def, is_word_type_def]
    (MATCH_MP len_full_compose len_full_suffix)) >>
  simp[] >>
  qexistsl_tac [`env`,`sm`,`evv`] >> simp[] >>
  conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
  conj_tac
  >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[]) >>
  drule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  disch_then irule >> simp[] >> rpt gen_tac >> strip_tac >>
  qexists_tac `tv` >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Finalise len_builtin_sim_full
