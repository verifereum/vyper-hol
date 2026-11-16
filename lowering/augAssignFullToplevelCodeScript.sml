(* Compiler certificates for the scalar top-level AugAssign phase chain. *)
Theory augAssignFullToplevelCode
Ancestors
  stmtSimAugAssignStorage bodyFullShared gasShadowCompileStmtHelpers
  gasShadowCompileArith gasShadowCompilePure gasShadowState
  exprLoweringProps emitHelperProps codegenRel compileEnv fragExec loweringSlice
  stmtSimDefs stmtLowering exprLowering gasShadow list finite_map

Theorem augassign_toplevel_phase_slices_full[local]:
  emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (cur,s1) /\
  lower_value compile_expr cenv ty e s1 = (rhs,s2) /\
  compile_binop bop cur rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (res,s3) /\
  emit_void (if tr then TSTORE else SSTORE) [Lit slot;res] s3 = ((),sb) /\
  fn_has_code sa sb func ==>
  cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
  cs_extends s3 sb /\ cs_extends sa s2 /\ cs_extends sa s3 /\
  cs_extends s1 s3 /\ cs_extends s1 sb /\ cs_extends s2 sb /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sb func
Proof
  strip_tac >>
  `cs_extends sa s1 /\ cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  `cs_extends sa s2 /\ cs_extends sa s3 /\
   cs_extends s1 s3 /\ cs_extends s1 sb /\ cs_extends s2 sb` by
    metis_tac[cs_extends_trans] >>
  simp[] >> metis_tac[fn_has_code_mid, cs_extends_refl]
QED

Theorem augassign_toplevel_shadow_code_full:
  stmt_env cenv lctx ret_ty
    (AugAssign ty (TopLevelNameTarget nsid) bop e) sa = (ce,sb) /\
  stmt_env cenv lctx ret_ty
    (gas_shadow_stmt (AugAssign ty (TopLevelNameTarget nsid) bop e))
    shadow_sa = (ce,shadow_sb) /\
  FLOOKUP cenv.ce_module_vars nsid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_hashmap_info nsid = NONE /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ce = cenv /\
  ?s1 s2 s3 ss1 ss2 ss3 cur rhs res sres.
    emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (cur,s1) /\
    lower_value compile_expr cenv ty e s1 = (rhs,s2) /\
    compile_binop bop cur rhs ty NONE
      (if bop = Exp then expr_int_literal e else NONE) s2 = (res,s3) /\
    emit_void (if tr then TSTORE else SSTORE) [Lit slot;res] s3 = ((),sb) /\
    emit_op (if tr then TLOAD else SLOAD) [Lit slot] shadow_sa = (cur,ss1) /\
    lower_value compile_expr cenv ty (gas_shadow_expr e) ss1 = (rhs,ss2) /\
    compile_binop bop cur rhs ty NONE
      (if bop = Exp then expr_int_literal (gas_shadow_expr e) else NONE)
      ss2 = (sres,ss3) /\
    emit_void (if tr then TSTORE else SSTORE) [Lit slot;sres] ss3 =
      ((),shadow_sb) /\
    gas_shadow_state s1 ss1 /\ gas_shadow_state s2 ss2 /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
    cs_extends s3 sb /\ cs_extends sa s2 /\ cs_extends sa s3 /\
    cs_extends s1 s3 /\ cs_extends s1 sb /\ cs_extends s2 sb /\
    fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
    fn_has_code s2 s3 func /\ fn_has_code s3 sb func /\
    fn_has_code ss1 ss2 shadow_func
Proof
  strip_tac >>
  drule_all augassign_toplevel_code_parts >> strip_tac >>
  qpat_x_assum `ce = cenv` SUBST_ALL_TAC >>
  `stmt_env cenv lctx ret_ty
    (AugAssign ty (TopLevelNameTarget nsid) bop (gas_shadow_expr e))
    shadow_sa = (cenv,shadow_sb)` by
    fs[gas_shadow_stmt_def, gas_shadow_expr_def] >>
  drule_all augassign_toplevel_code_parts >> strip_tac >>
  `cur_op' = cur_op /\ gas_shadow_state s1 s1'` by
    (irule gas_shadow_step >>
     qexistsl_tac [`emit_op (if tr then TLOAD else SLOAD) [Lit slot]`,
       `emit_op (if tr then TLOAD else SLOAD) [Lit slot]`, `sa`, `shadow_sa`] >>
     simp[]) >> gvs[] >>
  `rhs_op' = rhs_op /\ gas_shadow_state s2 s2'` by
    (irule gas_shadow_step >>
     qexistsl_tac [`lower_value compile_expr cenv ty e`,
       `lower_value compile_expr cenv ty (gas_shadow_expr e)`, `s1`, `s1'`] >>
     simp[gas_shadow_stmt_lower_value]) >> gvs[] >>
  drule_all augassign_toplevel_phase_slices_full >> strip_tac >>
  drule_all (SRULE [] (Q.INST [`e` |-> `gas_shadow_expr e`]
    augassign_toplevel_phase_slices_full)) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
