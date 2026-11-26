(* Joint finite-horizon AsWeiValue simulation. *)
Theory bodyFullBuiltinWordWei
Ancestors
  bodyFullShadowBodyInv
  bodyFullBuiltinWordWeiPrefix bodyFullBuiltinWordWeiContinuation
  bodyFullPreds bodyFullSimProjection bodySimFull exprSimSource gasOutcomeFullCompose
  exprSimWordBuiltins gasShadowCompileStmtHelpers bodyInvCodeProps exprBodyPreProps
  exprLoweringProps exprSimUnopProps fragExec exprSimDefs gasExemptCert
  vyperStorageTrace vyperStorageFootprint gasStorage compileEnv vyperTypeSystem vyperContext vyperAST list

Theorem word_wei_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
       (~is_word_type (expr_type e) ==>
        !tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) =
                SOME tvt ==>
              type_memory_size tvt = 0) /\
       expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx ty e es /\
       (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
       (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
       expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx ty e es) /\
    (?dn. bt = AsWeiValue dn) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `cx_tops cx = tops` by
    metis_tac[body_inv_main_code] >>
  drule as_wei_value_argument_shape >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> conj_tac
     >- metis_tac[expr_body_pre_static_facts] >>
     qexistsl_tac [`BaseT (UintT 256)`, `[e]`, `AsWeiValue dn`, `es`] >>
     simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (fs[builtin_args_length_ok_def, body_exprs_full_ok_def] >>
     drule_all body_expr_full_ok_simulations >> simp[]) >>
  conj_asm1_tac
  >- (rw[expr_sim_full_def] >>
      qpat_assum `lower_value _ _ _ (Builtin _ _ _) sa = _`
        (mp_then Any mp_tac lower_value_as_wei_value) >> simp[] >> strip_tac >>
      qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
      simp[Once gasShadowTheory.gas_shadow_expr_def, gasShadowTheory.gas_shadow_builtin_def] >>
      disch_then (mp_then Any mp_tac lower_value_as_wei_value) >>
      simp[gasShadowTheory.gas_shadow_expr_type] >> strip_tac >>
      rename1 `lower_value _ _ _ e sa = (x,s1)` >>
      rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (y,sh1)` >>
      `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
         (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
           (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
      `x = y /\ gas_shadow_state s1 sh1` by
        (qpat_x_assum `gas_shadow_compiles _ _`
           (mp_tac o REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
         disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
      qpat_x_assum `x = y` (SUBST_ALL_TAC o SYM) >>
      `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by
        (qpat_assum `lower_value _ _ _ e sa = _`
           (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
         simp[is_word_type_def] >> metis_tac[]) >>
      `cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var` by
        metis_tac[straight_fresh_cs_extends, straight_fresh_as_wei_value_int] >>
      `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
        metis_tac[fn_has_code_split] >>
      `cs_extends shadow_sa sh1` by metis_tac[compile_expr_grows] >>
      `cs_extends sh1 shadow_sb` by
        metis_tac[straight_fresh_cs_extends, straight_fresh_as_wei_value_int] >>
      `fn_has_code shadow_sa sh1 shadow_func` by metis_tac[fn_has_code_split] >>
      `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
        metis_tac[expr_body_pre_gas_admissible] >>
      qpat_assum `expr_type e = _` (fn ety =>
        qpat_x_assum `expr_sim_full _ _ _ _ e es`
          (drule_all o REWRITE_RULE [expr_sim_full_def, ety])) >>
      strip_tac >>
      qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
      rewrite_tac[as_wei_value_source_bind] >>
      irule gas_outcome_full_bind_all >> rpt conj_tac
      >~ [`gas_marked_exec _ _ _ _ _ _ _`]
      >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
          qexistsl_tac [`mid`, `t`, `v`] >>
          gvs[])
      >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
      >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
      >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
      >- (irule storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
      >~ [`storage_trace_frame _`]
      >- (gen_tac >> simp[storage_trace_frame_def]) >>
      qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
      conj_tac
      >~ [`storage_trace_domain _ _ _`]
      >- (rpt strip_tac >>
          `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
            fs[storage_trace_domain_def] >>
          qunabbrev_tac `childQ` >>
          qpat_assum `!H. valid_horizon _ _ H _ ==> _`
            (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
          (impl_tac >- simp[]) >>
          disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
          `post_value_type cenv e = BaseT (UintT k)` by
            (qspecl_then [`cenv`, `e`] mp_tac loweringPostsTheory.post_value_type_word >>
             asm_rewrite_tac[] >> simp[is_word_type_def]) >>
          simp[expr_type_def, is_word_type_def, Abbr `childR`] >>
          qpat_assum `expr_type e = BaseT (UintT k)`
            (fn ety => irule (SRULE [ety, GSYM LEFT_EXISTS_AND_THM,
              GSYM CONJ_ASSOC] as_wei_value_continuation_full)) >>
          simp[NoAsms] >>
          asm_rewrite_tac[] >>
          rpt conj_tac
          >- (qexists_tac `marks` >> asm_rewrite_tac[]) >>
          TRY (qexistsl_tac [`s1`, `x`]) >>
          fs[loweringPostsTheory.post_value_type_word,
            is_word_type_def] >> metis_tac[]) >>
      irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      conj_tac >- simp[] >>
      simp[Abbr `childR`] >> rpt strip_tac >>
      Cases_on `res` >> fs[expr_exit_def]) >>
  first_x_assum irule >>
  simp[expr_type_def, is_word_type_def] >> conj_tac
  >- (gen_tac >> Cases_on `compile_expr cenv ty
         (Builtin (BaseT (UintT 256)) (AsWeiValue dn) [e]) sa` >>
      drule_at Any compile_word_builtin_stack >> simp[] >> metis_tac[]) >>
  metis_tac[eval_expr_builtin_value]
QED
