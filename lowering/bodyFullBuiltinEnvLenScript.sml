(* Joint finite-horizon Len simulation. *)
Theory bodyFullBuiltinEnvLen
Ancestors
  bodyFullExprGeneric bodyFullPreds bodyFullGhostFrame gasOutcomeFullCompose
  gasShadowCompileStmtHelpers exprSimLen exprSimSource exprSimWordArgs
  fragGasSeqPtr fragGasOriginPtr emitHelperProps allocaHistory
  loweringStateRelDefs ptrSafeRun ptrDiscipline instMemFrontier
  contextCodegenRel codegenRel unitTransformDefs memSafeRun
  vyperTypeSystem vyperTypeBuiltins list finite_map emitHelper compileEnv
  fragExec venomInst venomState exprSimHypsDefs bodySimFull vyperAST
  exprBopLowering exprLoweringProps exprLowering exprSimUnwrap gasShadowState

Theorem len_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    bt = Len /\ builtin_args_length_ok bt (LENGTH args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt <> Len ==>
      body_exprs_full_ok cx args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt = Len ==>
      body_expr_full_ok cx (HD args)) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
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
  mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `ty`, `e` |-> `e`]
    gas_shadow_stmt_compile_expr) >>
  simp[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `compile_expr cenv ty (gas_shadow_expr e) shadow_sa` >> gvs[] >>
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
  (impl_tac >- simp[]) >> disch_tac >>
  FAIL_TAC "Len full child available"
QED

Finalise len_builtin_sim_full
