Theory bodyFullConvertScalarJoint
Ancestors
  bodyFullShadowBodyInv
  haltExitProj
  bodyFullPreds bodyFullSimProjection bodySimFull bodyFullOfVV bodyFullExprGeneric
  bodyFullConvertScalarSuffix bodyFullConvertScalarFrame bodyFullPathHistory
  bodyFullConvertEndpointPosts
  exprSimConvert exprSimHyps exprSimSource gasShadowCompile gasShadowState
  exprLowering exprLoweringProps compileEnv vyperContext vyperInterpreter
  vyperState vyperAST

Theorem convert_scalar_vv_sim_full:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  body_expr_full_ok cx e /\ ~is_bytestring_type (expr_type e) /\
  ~is_bytestring_type dst ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr cenv ty (TypeBuiltin _ _ _ _) sa = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def] >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
  simp[exprBopLoweringTheory.lower_value_child_call, SF ETA_ss, expr_type_def] >>
  strip_tac >>
  `?out. compile_type_convert x (case ann of FlagT name =>
      ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
      | _ => mk_convert_op (expr_type e) ann) sm = (out,sb) /\
      vv = StackValue ann out` by
    (Cases_on `ann` >> gvs[exprBopLoweringTheory.as_stack_val_pair] >>
     metis_tac[pairTheory.PAIR]) >>
  gvs[] >>
  `?shadow_sm. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (x,shadow_sm) /\
      gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
       (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e))` by
       irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
                REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> simp[]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[compile_expr_grows] >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def] >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def] >>
  simp[exprBopLoweringTheory.lower_value_child_call, SF ETA_ss, expr_type_def] >>
  strip_tac >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    (Cases_on `ann` >> gvs[exprBopLoweringTheory.as_stack_val_pair] >>
     metis_tac[cj 1 externalEntryShapeTheory.compile_type_convert_labels, pairTheory.SND]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (drule_all body_expr_full_ok_simulations >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[convert_operand_admissible,
      exprSimStackTheory.eval_expr_force_admissible, eval_expr_type_builtin_value] >>
  qpat_x_assum `expr_sim_full _ _ _ _ e _` mp_tac >>
  simp[expr_sim_full_def] >>
  disch_then (qspecl_then
    [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  `eval_expr cx (TypeBuiltin ann Convert ann [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v ee. (sum_CASE (convert_result cx (expr_type e) ann v)
         (\w. INL (Value w)) INR, ee))` by
    (simp[FUN_EQ_THM] >> gen_tac >>
     simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, type_builtin_args_length_ok_def] >>
     simp[Once evaluate_def, bind_def, return_def] >>
     Cases_on `eval_expr cx e x'` >> rename1 `_ = (raw,ee)` >>
     Cases_on `raw` >> simp[] >> rename1 `_ = (INL tv,ee)` >>
     Cases_on `read_result cx tv ee` >> rename1 `_ = (res,fin)` >>
     Cases_on `res` >> simp[] >> rename1 `_ = (INL val,fin)` >>
     simp[Once evaluate_def, bind_def, return_def, lift_sum_def,
       convert_result_def, evaluate_type_builtin_def] >>
     Cases_on `evaluate_convert_from (get_tenv cx) (expr_type e) val ann` >>
     simp[return_def, raise_def]) >>
  pop_assum SUBST1_TAC >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >>
  rpt conj_tac
  >- simp[vyperStorageTraceTheory.storage_trace_frame_def]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> metis_tac[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
       cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\
    ~t.vs_halted /\ ee.gas_obs = []` >> conj_tac
  >- suspend "continuation" >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`] >>
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type, halt_exit_INR_type]
QED

Resume convert_scalar_vv_sim_full[continuation]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >> fs[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `childQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 t /\
    ~t.vs_halted /\ mid.gas_obs = []` by metis_tac[] >>
  qpat_x_assum `childQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `childQ`, NoAsms] >> strip_tac >> gvs[] >>
  `is_word_type (expr_type e) /\ is_word_type ann` by
    metis_tac[bodyPtrTypeBuiltinsScalarSemanticTheory.scalar_source_body_word_types] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    (irule expr_body_pre_word_value >> simp[] >>
     qexistsl_tac [`cenv`,`env`,`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,`mid with gas_obs := []`] >>
     simp[expr_body_pre_gas_obs] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[vyperStateTheory.bind_def, NoAsms]) >>
  `?tout. evaluate_type (get_tenv cx) ann = SOME tout` by
    metis_tac[convertScalarTypingTheory.expr_body_pre_scalar_convert, optionTheory.IS_SOME_EXISTS] >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e
     es sa sm s0 mid v x t /\ ghost_inv_at (DF (storage_trace_horizon mid.storage_trace))
     lo d cenv cx mid G1 tn1 t` by metis_tac[] >>
  `eval_operand x t = SOME (typed_val_to_w256 tv v)` by
    (gvs[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def] >> metis_tac[]) >>
  `op_prov G1 x = NONE /\ op_taint tn1 x = {}` by
    gvs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    gvs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `fn_has_code sm sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `!name n. ann = FlagT name /\ FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
      cenv.ce_flag_n_members (nsid_to_string name) = n` by
    (rpt strip_tac >> irule convertScalarTypingTheory.scalar_flag_member_count >>
     qexistsl_tac [`cx`,`env`,`es`] >>
     gvs[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (`stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid t` by
       fs[loweringPostsTheory.expr_post_def] >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx mid t`
       (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     simp[]) >>
  drule_all scalar_convert_origin_path >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  Cases_on `convert_result cx (expr_type e) ann v`
  >- (rename1 `convert_result cx (expr_type e) ann v = INL vout` >>
      qpat_x_assum `!vout. INL _ = INL vout ==> _`
        (qspec_then `vout` mp_tac) >> simp_tac bool_ss [] >> strip_tac >>
      irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
      reverse conj_tac >- simp[] >>
      qexistsl_tac [`Gf`,`mid`,`INL (Value vout)`,`t'`,`tnf`] >>
      simp[] >> qx_gen_tac `H` >> strip_tac >>
      `bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
        (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
         simp[bind_def, NoAsms] >>
         `mid with gas_obs := [] = mid` by
           (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> simp[]) >>
      `valid_horizon cx st0 H es.storage_trace` by
        (qpat_assum `bind _ _ _ = (INL v,mid)` mp_tac >>
         qpat_assum `valid_horizon cx st0 H mid.storage_trace` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         drule_at (Pat `f st = _`) vyperStorageFootprintTheory.valid_horizon_frame >>
         simp[vyperStorageTraceTheory.storage_trace_frame_bind,
           cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
      `storage_well_formed_on cx es (FST H)` by
        (qpat_assum `!H. valid_horizon _ _ _ es.storage_trace ==> _`
          (qspec_then `H` mp_tac) >> simp[]) >>
      `storage_well_formed_on cx mid (FST H)` by
        (irule dynamic_read_storage_well_formed >>
         conj_tac >- (qexists_tac `st0` >> simp[]) >>
         qexistsl_tac [`cenv`,`e`,`env`,
           `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,`v`] >>
         simp[expr_body_pre_gas_obs] >>
         qpat_assum `storage_well_formed_on cx es (FST H)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
         strip_tac >> rpt gen_tac >>
         `get_storage cx (es with gas_obs := gas_explicit marks s0.vs_gas_readings) b =
          get_storage cx es b` by
           (Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]) >> simp[]) >>
      `sa.cs_next_var <= sm.cs_next_var` by
        (drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >> simp[]) >>
      `local_ptrs_reserved cenv sm` by
        metis_tac[local_ptrs_reserved_next_var] >>
      `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
       (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z)` by
        metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
      `alloca_inv t` by
        gvs[loweringPostsTheory.expr_post_def, stmt_state_rel_def] >>
      `alloca_history func t'` by
        (irule body_full_path_alloca_history >> conj_tac >- simp[] >>
         qexistsl_tac [`DF H`,`G1`,`Gf`,`PG`,`ctx`,
           `gas_explicit_sites ctx shadow_ctx`,`lo`,`[]`,`t`,`tn1`,`tnf`] >> simp[]) >>
      `expr_post H ctx func cenv cx e es sa sm s0 mid v x t /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by metis_tac[] >>
      drule_all dynamic_endpoint_vv_posts >>
      disch_then (qspec_then `lowered_value_type cenv (TypeBuiltin ann Convert ann [e])` strip_assume_tac) >>
      `mid with gas_obs := [] = mid` by
        (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp t'` by
        (`t' = (t with vs_inst_idx := t'.vs_inst_idx) with vs_vars := t'.vs_vars` by
           metis_tac[stateFrameTheory.state_frame_eq_reconstruct] >>
         qpat_x_assum `t' = (t with vs_inst_idx := _) with vs_vars := _` SUBST1_TAC >>
         qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
      simp[contextTheory.vv_location_def]) >>
  qpat_x_assum `!exc. INR _ = INR exc ==> _`
    (qspec_then `y` mp_tac) >> simp_tac bool_ss [] >> strip_tac >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`,`mid`,`Abort err t'`,`INR (Error (RuntimeError msg))`,`tnf`] >>
  simp[fragExecTheory.exit_result_def, exprSimDefsTheory.expr_exit_def,
       halt_exit_not_halt]
QED
Finalise convert_scalar_vv_sim_full
