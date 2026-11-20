(* Paired compiler slices for finite-horizon AugAssign consumers. *)
Theory augAssignFullCodeStages
Ancestors
  stmtSimAugAssignPlace stmtLoweringMono gasShadowCompileStmtHelpers
  gasShadowCompileArith gasShadowCompilePure gasShadowState gasShadow
  exprLoweringProps fragExec stmtLowering exprLowering compileEnv
  emitHelper vyperAST list

Theorem augassign_shadow_step[local]:
  gas_shadow_compiles f g /\ gas_shadow_state sa ta /\
  f sa = (x,sb) /\ g ta = (y,tb) ==>
  x = y /\ gas_shadow_state sb tb
Proof
  strip_tac >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then drule >> simp[]
QED

Theorem augassign_full_code_stages:
  stmt_env cenv lctx ret_ty (AugAssign ty t bop e) sa = (c,sf) /\
  stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign ty t bop e))
    shadow_sa = (c,shadow_sf) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sf shadow_sf /\
  fn_has_code sa sf func /\ fn_has_code shadow_sa shadow_sf shadow_func ==>
  c = cenv /\
  ?r s0 shadow_s0.
    compile_get_target_ptr compile_expr cenv t sa = (r,s0) /\
    compile_get_target_ptr compile_expr cenv (gas_shadow_target t)
      shadow_sa = (r,shadow_s0) /\
    gas_shadow_state s0 shadow_s0 /\
    ci_mono sa s0 /\ ci_mono shadow_sa shadow_s0 /\
    fn_has_code sa s0 func /\ fn_has_code shadow_sa shadow_s0 shadow_func /\
    ((FST (SND r) = NONE /\
      emit_void INVALID [] s0 = ((),sf) /\
      emit_void INVALID [] shadow_s0 = ((),shadow_sf) /\
      ci_mono s0 sf /\ ci_mono shadow_s0 shadow_sf /\
      fn_has_code s0 sf func /\
      fn_has_code shadow_s0 shadow_sf shadow_func) \/
     ?loc cur rhs result s1 s2 s3 shadow_s1 shadow_s2 shadow_s3.
       FST (SND r) = SOME loc /\
       (if loc = LocCode then
          compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST r)
        else
          emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
            [FST r]) s0 = (cur,s1) /\
       (if loc = LocCode then
          compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST r)
        else
          emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
            [FST r]) shadow_s0 = (cur,shadow_s1) /\
       lower_value compile_expr cenv ty e s1 = (rhs,s2) /\
       lower_value compile_expr cenv ty (gas_shadow_expr e) shadow_s1 =
         (rhs,shadow_s2) /\
       compile_binop bop cur rhs ty NONE
         (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
       compile_binop bop cur rhs ty NONE
         (if bop = Exp then expr_int_literal e else NONE) shadow_s2 =
         (result,shadow_s3) /\
       (if loc = LocCode then
          compile_ptr_store cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST r) result
        else
          emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE)
            [FST r; result]) s3 = ((),sf) /\
       (if loc = LocCode then
          compile_ptr_store cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST r) result
        else
          emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE)
            [FST r; result]) shadow_s3 = ((),shadow_sf) /\
       gas_shadow_state s1 shadow_s1 /\ gas_shadow_state s2 shadow_s2 /\
       gas_shadow_state s3 shadow_s3 /\
       ci_mono s0 s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 sf /\
       ci_mono shadow_s0 shadow_s1 /\ ci_mono shadow_s1 shadow_s2 /\
       ci_mono shadow_s2 shadow_s3 /\ ci_mono shadow_s3 shadow_sf /\
       fn_has_code s0 s1 func /\ fn_has_code s1 s2 func /\
       fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
       fn_has_code shadow_s0 shadow_s1 shadow_func /\
       fn_has_code shadow_s1 shadow_s2 shadow_func /\
       fn_has_code shadow_s2 shadow_s3 shadow_func /\
       fn_has_code shadow_s3 shadow_sf shadow_func)
Proof
  strip_tac >>
  qpat_assum `stmt_env _ _ _ (AugAssign _ _ _ _) _ = _`
    (strip_assume_tac o MATCH_MP aug_place_code_parts) >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
  simp[gas_shadow_stmt_def] >>
  disch_then (strip_assume_tac o MATCH_MP aug_place_code_parts) >>
  rename1 `compile_get_target_ptr compile_expr cenv t sa = (r,s0)` >>
  rename1 `compile_get_target_ptr compile_expr cenv (gas_shadow_target t)
    shadow_sa = (sr,shadow_s0)` >>
  `r = sr /\ gas_shadow_state s0 shadow_s0` by
    (irule augassign_shadow_step >>
     rpt (first_assum (irule_at Any)) >>
     simp[gas_shadow_stmt_get_target_ptr]) >>
  `ci_mono sa s0 /\ ci_mono shadow_sa shadow_s0` by
    (mp_tac (Q.SPECL [`t`, `cenv`, `sa`] ci_mono_compile_get_target_ptr) >>
     mp_tac (Q.SPECL [`gas_shadow_target t`, `cenv`, `shadow_sa`]
       ci_mono_compile_get_target_ptr) >> simp[]) >>
  gvs[]
  >- (`ci_mono s0 sf /\ ci_mono shadow_s0 shadow_sf` by
        metis_tac[ci_mono_emit_void, pairTheory.SND] >>
      gvs[ci_mono_def] >> imp_res_tac fn_has_code_split >> simp[]) >>
  rename1 `(if loc = LocCode then _ else _) shadow_s0 = (shadow_cur,shadow_s1)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_s1 =
    (shadow_rhs,shadow_s2)` >>
  rename1 `compile_binop _ shadow_cur shadow_rhs _ _ _ shadow_s2 =
    (shadow_result,shadow_s3)` >>
  `cur = shadow_cur /\ gas_shadow_state s1 shadow_s1` by
    (irule augassign_shadow_step >>
     rpt (first_assum (irule_at Any)) >>
     rw[gas_shadow_compiles_emit_op, gasShadowCompileContextTheory.gas_shadow_compiles_ptr_load]) >>
  gvs[] >>
  `rhs = shadow_rhs /\ gas_shadow_state s2 shadow_s2` by
    (irule augassign_shadow_step >>
     rpt (first_assum (irule_at Any)) >>
     simp[gas_shadow_stmt_lower_value]) >>
  gvs[] >>
  `result = shadow_result /\ gas_shadow_state s3 shadow_s3` by
    (irule augassign_shadow_step >>
     rpt (first_assum (irule_at Any)) >>
     simp[gas_shadow_compiles_binop]) >>
  gvs[] >>
  `ci_mono s0 s1 /\ ci_mono shadow_s0 shadow_s1` by
    (Cases_on `loc = LocCode` >> gvs[] >>
     metis_tac[ci_mono_compile_ptr_load, ci_mono_emit_op, pairTheory.SND]) >>
  `ci_mono s1 s2 /\ ci_mono shadow_s1 shadow_s2` by
    metis_tac[cj 2 compile_expr_grows, ci_mono_def] >>
  `ci_mono s2 s3 /\ ci_mono shadow_s2 shadow_s3` by
    metis_tac[compile_binop_grows, ci_mono_def] >>
  `ci_mono s3 sf /\ ci_mono shadow_s3 shadow_sf` by
    (Cases_on `loc = LocCode` >> gvs[] >>
     metis_tac[ci_mono_compile_ptr_store, ci_mono_emit_void, pairTheory.SND]) >>
  gvs[ci_mono_def] >>
  imp_res_tac cs_extends_trans >> imp_res_tac fn_has_code_split >> simp[]
QED
