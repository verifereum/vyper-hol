(* The compiler cuts shared by the non-reading array prefix and its selector. *)
Theory bodyArrayNoCopyCodeMods
Ancestors
  exprSimSubscriptArrayFramed exprLowering exprLoweringProps fragExec
  gasShadowCompileStmtHelpers gasShadowCompilePure gasShadowState gasShadow
  compileEnv context vyperAST

Theorem array_subscript_code_parts[local]:
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  place_type cenv obj = ValPT (ArrayT et bd) /\
  ~copies_subscript_base cenv obj idx /\ fn_has_code sa sb func ==>
  ?bvv sm iop st2 dst loc.
    compile_expr cenv ty obj sa = (bvv,sm) /\
    lower_value compile_expr cenv ty idx sm = (iop,st2) /\
    loc = (case vv_location bvv of SOME l => l | NONE => LocMemory) /\
    compile_array_subscript (vv_operand bvv) iop
      (case bd of vyperAST$Fixed _ => F | vyperAST$Dynamic _ => T)
      (case bd of vyperAST$Fixed n => n | vyperAST$Dynamic _ => 0)
      (word_scale loc) (elem_size_in_location cenv loc et)
      (is_signed_type (expr_type idx))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) st2 = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst loc) /\
    fn_has_code sa sm func /\ fn_has_code sm st2 func /\ fn_has_code st2 sb func /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    sm.cs_next_var <= st2.cs_next_var /\ sm.cs_next_id <= st2.cs_next_id
Proof
  strip_tac >> drule_all_then strip_assume_tac compile_expr_array_subscript >>
  drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
  drule_then strip_assume_tac (cj 2 compile_expr_grows) >>
  rename1 `lower_value compile_expr cenv ty idx sm = (iop,st2)` >>
  `cs_extends st2 sb` by
    (`ci_mono st2 sb` suffices_by simp[ci_mono_def] >>
     qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
  `cs_extends sm sb` by (irule cs_extends_trans >> qexists_tac `st2` >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sm st2 func /\ fn_has_code st2 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  qexistsl_tac [`bvv`,`sm`,`iop`,`st2`,`dst`,`loc`] >> asm_rewrite_tac[]
QED

Theorem matching_shadow_cut[local]:
  gas_shadow_compiles f g /\ gas_shadow_state s t /\
  f s = (x,s') /\ g t = (y,t') ==>
  x = y /\ gas_shadow_state s' t'
Proof
  simp[gas_shadow_compiles_def] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem array_nocopy_paired_parts_mods:
  place_type cenv obj = ValPT (ArrayT et bd) /\
  ~copies_subscript_base cenv obj idx /\
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Subscript ann obj idx)) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  local_ptrs_reserved cenv sa ==>
  ?bvv sm iop st2 dst loc shadow_sm shadow_st2.
    compile_expr cenv ty obj sa = (bvv,sm) /\
    lower_value compile_expr cenv ty idx sm = (iop,st2) /\
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa =
      (bvv,shadow_sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr idx)
      shadow_sm = (iop,shadow_st2) /\
    loc = (case vv_location bvv of SOME l => l | NONE => LocMemory) /\
    compile_array_subscript (vv_operand bvv) iop
      (case bd of vyperAST$Fixed _ => F | vyperAST$Dynamic _ => T)
      (case bd of vyperAST$Fixed n => n | vyperAST$Dynamic _ => 0)
      (word_scale loc) (elem_size_in_location cenv loc et)
      (is_signed_type (expr_type idx))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) st2 = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst loc) /\
    gas_shadow_state sm shadow_sm /\ gas_shadow_state st2 shadow_st2 /\
    fn_has_code sa sm func /\ fn_has_code sm st2 func /\ fn_has_code st2 sb func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\
    fn_has_code shadow_sm shadow_st2 shadow_func /\
    fn_has_code shadow_st2 shadow_sb shadow_func /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    sm.cs_next_var <= st2.cs_next_var /\ sm.cs_next_id <= st2.cs_next_id /\
    local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv st2
Proof
  strip_tac >> drule_all_then strip_assume_tac array_subscript_code_parts >>
  `place_type (gas_shadow_env T cenv) (gas_shadow_expr obj) = ValPT (ArrayT et bd)` by
    simp[] >>
  `~copies_subscript_base (gas_shadow_env T cenv)
      (gas_shadow_expr obj) (gas_shadow_expr idx)` by fs[copies_subscript_base_def] >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _`
    (assume_tac o REWRITE_RULE [gas_shadow_expr_def]) >>
  qpat_x_assum `compile_expr cenv ty (Subscript ann obj idx) sa = _` kall_tac >>
  drule_all_then strip_assume_tac array_subscript_code_parts >>
  rename1 `compile_expr cenv ty obj sa = (bvv,sm)` >>
  rename1 `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa =
      (shadow_bvv,shadow_sm)` >>
  `bvv = shadow_bvv /\ gas_shadow_state sm shadow_sm` by
    (irule matching_shadow_cut >>
     qexistsl_tac [`compile_expr cenv ty obj`,
       `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj)`,
       `sa`,`shadow_sa`] >>
     simp[gas_shadow_stmt_compile_expr_env]) >>
  rename1 `lower_value compile_expr cenv ty idx sm = (iop,st2)` >>
  rename1 `lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr idx)
       shadow_sm = (shadow_iop,shadow_st2)` >>
  `iop = shadow_iop /\ gas_shadow_state st2 shadow_st2` by
    (irule matching_shadow_cut >>
     qexistsl_tac [`lower_value compile_expr cenv ty idx`,
       `lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr idx)`,
       `sm`,`shadow_sm`] >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv st2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  qexistsl_tac [`bvv`,`sm`,`iop`,`st2`,`dst`,`loc`,`shadow_sm`,`shadow_st2`] >>
  qpat_assum `vv = LocatedValue ann (mk_ptr dst loc)` (fn th => pure_rewrite_tac[th]) >>
  simp[]
QED
