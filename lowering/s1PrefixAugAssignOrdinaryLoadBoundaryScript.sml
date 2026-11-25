(* Static and compiler inputs for the ordinary AugAssign load/RHS cut. *)
Theory s1PrefixAugAssignOrdinaryLoadBoundary
Ancestors
  s1PrefixAugAssignOrdinaryTarget s1PrefixAugAssignOrdinaryLoad
  s1PrefixDefs augAssignFullCodeStages augAssignFullEntryPre
  stmtSimAugAssignPlace loweringPosts exprLoweringProps

Theorem augassign_ordinary_load_stage_inputs:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign aty t bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (AugAssign aty t bop e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (AugAssign aty t bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign aty t bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign aty t bop e)) /\
  stmt_frag_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (AugAssign aty t bop e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (AugAssign aty t bop e)))
    (eval_stmt cx (AugAssign aty t bop e)) es
    (st0,sa,sb,shadow_sa,shadow_sb,s0,G0,tn0,ce) /\
  compile_get_target_ptr compile_expr cenv t sa = (r,ca) /\
  compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
    (gas_shadow_target t) shadow_sa = (r,shadow_ca) ==>
  expr_body_pre cenv cx env e es /\
  target_indices_pre cenv cx env t /\
  is_word_type aty /\ type_place_target env t = SOME (Type aty) /\
  compile_get_target_ptr compile_expr cenv t sa = (r,ca) /\
  compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
    (gas_shadow_target t) shadow_sa = (r,shadow_ca) /\
  sa.cs_next_var <= ca.cs_next_var /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  return_buf_frame d cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  ((FST (SND r) = NONE /\ emit_void INVALID [] ca = ((),sb)) \/
   (?loc old cb rhsop cc shadow_cb shadow_cc.
     FST (SND r) = SOME loc /\
     (if loc = LocCode then
        compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST r)
      else emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
        [FST r]) ca = (old,cb) /\ fn_has_code ca cb func /\
     lower_value compile_expr cenv aty e cb = (rhsop,cc) /\
     lower_value compile_expr (gas_shadow_env T cenv) aty (gas_shadow_expr e)
        shadow_cb = (rhsop,shadow_cc) /\
     gas_shadow_state cb shadow_cb /\ gas_shadow_state cc shadow_cc /\
     fn_has_code cb cc func /\ fn_has_code shadow_cb shadow_cc shadow_func))
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e es` by (drule_all augassign_entry_rhs_pre >> simp[]) >>
  `target_indices_pre cenv cx env t` by (drule_all augassign_entry_target_indices_pre >> simp[]) >>
  drule (cj 1 aug_place_typing) >> strip_tac >>
  drule_all (cj 1 aug_place_typing_word) >> strip_tac >>
  qpat_x_assum `stmt_frag_full_pre _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [stmt_frag_full_pre_def]) >>
  drule_all augassign_full_code_stages >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`r0`,`ca0`,`shadow_ca0`] (map_every assume_tac o CONJUNCTS))) >>
  `r0 = r /\ ca0 = ca /\ shadow_ca0 = shadow_ca` by
    metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `r0 = r` SUBST_ALL_TAC >>
  qpat_x_assum `ca0 = ca` SUBST_ALL_TAC >>
  qpat_x_assum `shadow_ca0 = shadow_ca` SUBST_ALL_TAC >>
  `sa.cs_next_var <= ca.cs_next_var` by fs[ci_mono_def] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  simp[] >>
  qpat_x_assum `_ \/ ?loc old rhs result cb cc cd shadow_cb shadow_cc shadow_cd. _`
    (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
      (qx_choosel_then [`loc`,`old`,`rhsop`,`resop`,`cb`,`cc`,`cd`,
                        `shadow_cb`,`shadow_cc`,`shadow_cd`] STRIP_ASSUME_TAC))
  >- simp[] >>
  disj2_tac >>
  qexistsl_tac [`loc`,`old`,`cb`,`rhsop`,`cc`,`shadow_cb`,`shadow_cc`] >>
  Cases_on `loc` >> fs[]
QED
