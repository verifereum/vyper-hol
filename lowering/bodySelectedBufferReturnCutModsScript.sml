(* Compiler cuts for the real and gas-shadow buffered Return. *)
Theory bodySelectedBufferReturnCutMods
Ancestors
  stmtSimReturn stmtLowering exprLowering compileEnv context
  loweringPosts exprLoweringProps
  externalEntryShape fragExec emitHelper emitHelperProps
  gasShadow gasShadowCompileBase gasShadowCompileStmtHelpers gasShadowState
Libs
  monadsyntax

Theorem buffered_return_unlock_copy[local]:
  cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
  cenv.ce_returns_count = 0 /\
  compile_internal_return_from_env cenv ty sty op rpc sm = ((),sb) ==>
  ?elems su sc.
    compile_return_unlock cenv sm = ((),su) /\
    compile_internal_return cenv (SOME op) rpc 0 ty sty elems
      (SOME (Var bp)) su = ((),sb) /\
    compile_store_memory cenv op (Var bp) ty sty su = ((),sc) /\
    emit_inst RET [rpc] [] sc = ((),sb)
Proof
  strip_tac >>
  qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_from_env_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_return_unlock cenv sm` >> rename1 `_ = (u,su)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `compile_store_memory cenv op (Var bp) ty sty su` >>
  rename1 `_ = (u,sc)` >> Cases_on `u` >> simp[]
QED

Theorem buffered_return_cut[local]:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = 0 /\
  cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
  stmt_env cenv lctx ty (Return (SOME e)) sa = (ce',sb) /\
  fn_has_code sa sb func ==>
  ce' = cenv /\
  ?op sm elems su sc.
    lower_value compile_expr cenv ty e sa = (op,sm) /\
    compile_return_unlock cenv sm = ((),su) /\
    compile_internal_return cenv (SOME op) (Var rpc) 0 ty
      (lowered_value_type cenv e) elems (SOME (Var bp)) su = ((),sb) /\
    compile_store_memory cenv op (Var bp) ty (lowered_value_type cenv e) su = ((),sc) /\
    emit_inst RET [Var rpc] [] sc = ((),sb) /\
    fn_has_code sa sm func /\ fn_has_code sm su func /\
    fn_has_code su sc func /\ fn_has_code sc sb func
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, Once compile_stmt_def] >>
  Cases_on `lower_value compile_expr cenv ty e sa` >>
  rename1 `_ = (op,sm)` >> simp[] >>
  Cases_on `compile_internal_return_from_env cenv ty (lowered_value_type cenv e) op (Var rpc) sm` >>
  rename1 `_ = (u,bs)` >> Cases_on `u` >> simp[] >> strip_tac >>
  qpat_x_assum `cenv = ce'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `bs = sb` SUBST_ALL_TAC >>
  drule_all buffered_return_unlock_copy >> strip_tac >>
  qexistsl_tac [`elems`,`su`,`sc`] >> simp[] >>
  drule_then strip_assume_tac compile_return_unlock_shape >>
  `cs_extends sa sm` by metis_tac[compile_expr_grows] >>
  `cs_extends su sc` by metis_tac[compile_store_memory_labels, pairTheory.SND] >>
  `cs_extends sc sb` by metis_tac[cs_extends_emit_inst] >>
  `cs_extends su sb /\ cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`sm`,`su`,`sb`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`su`,`sc`,`sb`,`func`] mp_tac fn_has_code_split >> simp[]
QED

Theorem selected_buffer_return_paired_cut_mods:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = 0 /\
  cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
  stmt_env cenv lctx ty (Return (SOME e)) sa = (ce',sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Return (SOME e))) sha =
    (gas_shadow_env T ce',shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func ==>
  ce' = cenv /\
  ?op sm shm.
    lower_value compile_expr cenv ty e sa = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (op,shm) /\
    gas_shadow_state sm shm /\
    fn_has_code sa sm func /\ fn_has_code sha shm shadow_func /\
    (?elems su sc.
      cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
      compile_return_unlock cenv sm = ((),su) /\
      compile_internal_return cenv (SOME op) (Var rpc) 0 ty
        (lowered_value_type cenv e) elems (SOME (Var bp)) su = ((),sb) /\
      compile_store_memory cenv op (Var bp) ty (lowered_value_type cenv e) su = ((),sc) /\
      emit_inst RET [Var rpc] [] sc = ((),sb) /\
      fn_has_code sm su func /\ fn_has_code su sc func /\ fn_has_code sc sb func) /\
    ?shelems shu shc.
      compile_return_unlock (gas_shadow_env T cenv) shm = ((),shu) /\
      compile_internal_return (gas_shadow_env T cenv) (SOME op) (Var rpc) 0 ty
        (lowered_value_type (gas_shadow_env T cenv) (gas_shadow_expr e))
        shelems (SOME (Var bp)) shu = ((),shb) /\
      compile_store_memory (gas_shadow_env T cenv) op (Var bp) ty
        (lowered_value_type (gas_shadow_env T cenv) (gas_shadow_expr e)) shu = ((),shc) /\
      emit_inst RET [Var rpc] [] shc = ((),shb) /\
      fn_has_code shm shu shadow_func /\ fn_has_code shu shc shadow_func /\
      fn_has_code shc shb shadow_func
Proof
  strip_tac >> drule_all buffered_return_cut >> strip_tac >>
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (assume_tac o REWRITE_RULE [gas_shadow_stmt_def, optionTheory.OPTION_MAP_DEF]) >>
  `(gas_shadow_env T cenv).ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
   (gas_shadow_env T cenv).ce_returns_count = 0 /\
   (gas_shadow_env T cenv).ce_return_buf = SOME (PtrVar (Var bp) cap)` by
    simp[gas_shadow_env_def] >>
  drule_all (Q.INST [`cenv` |-> `gas_shadow_env T cenv`] buffered_return_cut) >>
  strip_tac >>
  rename1 `lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (shop,shm)` >>
  `op = shop /\ gas_shadow_state sm shm` by
    (mp_tac (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`sha`] mp_tac) >> simp[]) >>
  qpat_x_assum `op = shop` SUBST_ALL_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`shop`,`sm`,`shm`] >> asm_rewrite_tac[] >>
  conj_tac >- (qexistsl_tac [`elems`,`su`,`sc`] >> asm_rewrite_tac[]) >>
  rename1 `compile_return_unlock (gas_shadow_env T cenv) shm = ((),shu)` >>
  rename1 `emit_inst RET [Var rpc] [] shc = ((),shb)` >>
  rename1 `compile_internal_return (gas_shadow_env T cenv) (SOME shop) (Var rpc) 0 ty _ shelems _ shu = _` >>
  qexistsl_tac [`shelems`,`shu`,`shc`] >> asm_rewrite_tac[]
QED
