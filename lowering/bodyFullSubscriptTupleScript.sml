Theory bodyFullSubscriptTuple
Ancestors exprSimAttributeProps[qualified,ignore_grammar] context[qualified,ignore_grammar]
  bodyFullSubscriptTupleLanding bodyFullEmptyLeafData exprSimFullBundleProps
  exprSimTuple exprSimSource exprSimUnwrap exprSimHyps bodySimFull gasOutcomeFullCompose
  gasShadowCompilePure gasShadowCompileStmtHelpers
  gasShadow gasShadowState gasShadowCompile gasExemptCert vyperStorageTrace
  vyperStorageFootprint emitHelperProps exprLoweringProps fragExec
  loweringPosts compileEnv valueEncoding vyperTyping vyperInterpreter
  vyperState vyperAST stateRelProj tupleMemoryLayout typedCopyLayoutPtr

Theorem subscript_tuple_vv_sim_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann obj idx es tys.
    expr_body_pre cenv cx env (Subscript ann obj idx) es /\
    expr_type obj = TupleT tys /\ place_type cenv obj = ValPT (TupleT tys) /\
    post_value_type cenv obj = expr_type obj /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty obj es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann obj idx) es
Proof
  rpt gen_tac >> strip_tac >> drule_all tuple_pre_base >> strip_tac >> gvs[] >>
  simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_expr_tuple_subscript >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv ty obj sa = (bvv,sm)` >>
  `cs_extends sm sb` by
    (drule emit_op_extends >> simp[same_blocks_def, cs_extends_def] >>
     strip_tac >> qexists_tac `[]` >> simp[]) >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `?shadow_sm. compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa =
      (bvv,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_expr cenv ty obj)
         (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj))` by
       irule gas_shadow_stmt_compile_expr_env >>
     pop_assum (qspecl_then [`sa`, `shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa` >>
     simp[]) >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    suspend "shadow_extends" >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (drule_all fn_has_code_split >> simp[]) >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    (drule expr_body_pre_vv_gas_admissible >> simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ obj _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                          `bvv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ baseQ baseR` >>
  `eval_expr cx (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) =
   bind (eval_expr cx obj)
     (\r. select_result cx (TupleT tys) r (ValueSubscript (IntV (&k))))` by
    simp[tuple_source] >>
  asm_rewrite_tac[] >>
  irule gas_outcome_full_bind_all >>
  `!res : eval_result + exception. !r.
     (?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r) <=> expr_exit res r` by
    (Cases >> simp[exprSimDefsTheory.expr_exit_def]) >> simp[] >>
  rpt conj_tac
  >~ [`storage_trace_frame (select_result _ _ _ _)`]
  >- simp[storage_trace_frame_select]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[cj 5 evaluate_storage_trace_frame] >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >~ [`storage_trace_domain _ _ _`] >- suspend "selected" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[Abbr `baseR`] >>
  simp[Abbr `baseQ`, Abbr `baseR`] >>
  rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def]
QED

Resume subscript_tuple_vv_sim_full[shadow_extends]:
  drule compile_expr_extends >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
  simp[gas_shadow_expr_def] >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ (gas_shadow_expr obj) _) _ = _`
    (mp_then Any mp_tac compile_expr_tuple_subscript) >>
  simp[gas_shadow_place_type] >> strip_tac >>
  drule emit_op_extends >> simp[same_blocks_def, cs_extends_def] >>
  strip_tac >> qexists_tac `[]` >> simp[]
QED

Resume subscript_tuple_vv_sim_full[selected]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `s`] >>
  strip_tac >> fs[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[storage_trace_domain_def] >>
  `baseQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> baseQ H _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  qpat_x_assum `baseQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `baseQ`, NoAsms] >>
  disch_then strip_assume_tac >> gvs[] >>
  `~s.vs_halted /\ mid.gas_obs = []` by metis_tac[] >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (qpat_x_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[] >>
     `mid with gas_obs := [] = mid` by
       (qpat_x_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> simp[]) >>
  `emit_op ADD [vv_operand bvv; Lit (n2w (tuple_offset cenv tys (vv_loc bvv) k))]
     sm = (p,sb)` by fs[exprLoweringTheory.literal_int_index_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_vv_sim_full_post (DF,lo,d,ctx,func) cenv cx obj
         (es,sa,sm,s0,bvv,G0,tn0) H (INL tv) mid G1 tn1 s` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     simp[expr_vv_sim_full_post_def, expr_sim_full_endpoint_def]) >>
  drule_all tuple_select_add_landing >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`child`,`w`,`t`,`G2`,`tn2`] strip_assume_tac)) >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`G2`,`mid`,`INL child`,`t`,`tn2`] >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_assum `mid with gas_obs := [] = mid` (pure_rewrite_tac o single) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` (drule_then mp_tac)) >>
  simp[NoAsms, expr_vv_sim_full_post_def, expr_sim_full_endpoint_def, AC CONJ_ASSOC CONJ_COMM]
QED

Finalise subscript_tuple_vv_sim_full
