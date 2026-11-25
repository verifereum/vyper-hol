(* The real and shadow compiler intervals of a normalized Uint2Str. *)
Theory bodyUint2StrCodeMods
Ancestors
  exprSimUint2Str exprLoweringProps exprLowering fragExec compileEnv
  gasShadowCompileStmtHelpers gasShadowCompileBase gasShadowState gasShadow
  vyperAST

Theorem uint2str_code_cuts_mods:
  compile_expr ce ty (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Builtin (BaseT (StringT n)) (Uint2Str n) [e])) sha = (vv,shb) /\
  gas_shadow_state sa sha /\ gas_shadow_state sb shb /\
  fn_has_code sa sb fn /\ fn_has_code sha shb shfn ==>
  ?op sm shm.
    lower_value compile_expr ce ty e sa = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (op,shm) /\
    gas_shadow_state sm shm /\
    as_ptr_val (BaseT (StringT n)) LocMemory
      (compile_uint2str op n (type_memory_bytes ce (BaseT (StringT n))) sm) = (vv,sb) /\
    as_ptr_val (BaseT (StringT n)) LocMemory
      (compile_uint2str op n (type_memory_bytes ce (BaseT (StringT n))) shm) = (vv,shb) /\
    cs_extends sa sm /\ cs_extends sm sb /\ cs_extends sha shm /\ cs_extends shm shb /\
    fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
    fn_has_code sha shm shfn /\ fn_has_code shm shb shfn /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id
Proof
  strip_tac >>
  drule_then (qx_choose_then `op` (qx_choose_then `sm` strip_assume_tac))
    uint2str_compile_cut >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[Once gas_shadow_expr_def, gas_shadow_builtin_def] >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [] o MATCH_MP uint2str_compile_cut) >>
  qpat_assum `gas_shadow_state sa sha`
    (mp_tac o MATCH_MP
      (Q.INST [`cenv` |-> `ce`, `sd` |-> `T`]
        (REWRITE_RULE [gas_shadow_compiles_def] gas_shadow_stmt_lower_value_env))) >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (op,shm)` >>
  imp_res_tac (cj 2 compile_expr_grows) >>
  `cs_extends sm sb` by
    (irule (SRULE [cs_appends_def] uint2str_code_appends) >> goal_assum (drule_at Any)) >>
  `cs_extends shm shb` by
    (irule (SRULE [cs_appends_def] uint2str_code_appends) >> goal_assum (drule_at Any)) >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sha shm shfn /\ fn_has_code shm shb shfn` by
    (irule fn_has_code_split >> simp[]) >>
  simp[]
QED
