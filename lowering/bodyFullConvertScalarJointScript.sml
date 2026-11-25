Theory bodyFullConvertScalarJoint
Ancestors
  bodyFullShadowBodyInv
  haltExitProj
  bodyFullPreds bodyFullSimProjection bodySimFull bodyFullOfVV bodyFullExprGeneric
  bodyFullConvertScalarSuffix bodyFullConvertScalarFrame bodyFullPathHistory
  bodyFullConvertEndpointPosts exprSimFullBundleProps bodyFullEmptyLeafData
  vyperStorageTrace vyperStorageFootprint exprSimDefs
  exprSimConvert exprSimHyps exprSimSource gasShadowCompile gasShadowState
  exprLowering exprLoweringProps compileEnv vyperContext vyperInterpreter
  vyperState vyperAST

(* Retain the raw run with the same endpoint and all-horizon ghost pair
   that the original scalar continuation publishes. *)
Theorem scalar_convert_selected_terminal:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e]) es /\
  expr_body_pre cenv cx env e es /\ valid_conversion (expr_type e) ann /\
  ~is_bytestring_type (expr_type e) /\ ~is_bytestring_type ann /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_type_convert x (case ann of FlagT name =>
      ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
      | _ => mk_convert_op (expr_type e) ann) sm = (out,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> storage_well_formed_on cx es (FST H)) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL v,mid with gas_obs := tail)) /\
  mid.gas_obs = [] /\ ~t.vs_halted /\ storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,s0,x,G0,tn0)
       H (INL v) mid G1 tn1 t) ==>
  ?r Gf tnf.
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (r,Gf,tnf)) /\
    ((?vout u. convert_result cx (expr_type e) ann v = INL vout /\
       run_inst_seq (emitted_insts sm sb) t = OK u /\
       r = OK (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
       !H. valid_horizon cx st0 H mid.storage_trace ==>
         expr_vv_sim_full_post (DF,lo,d,ctx,func) cenv cx (TypeBuiltin ann Convert ann [e])
           (es,sa,sb,s0,StackValue ann out,G0,tn0) H (INL (Value vout)) mid Gf tnf
           (u with vs_inst_idx := LENGTH sb.cs_current_insts)) \/
     (?msg err u t'. convert_result cx (expr_type e) ann v = INR (Error (RuntimeError msg)) /\
       run_inst_seq (emitted_insts sm sb) t = Abort err u /\ r = Abort err t'))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss())
      [expr_sim_full_post_def,expr_sim_full_endpoint_def])) >>
  `is_word_type (expr_type e) /\ is_word_type ann` by
    metis_tac[bodyPtrTypeBuiltinsScalarSemanticTheory.scalar_source_body_word_types] >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     `mid with gas_obs := [] = mid` by
       (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
     simp[NoAsms] >> metis_tac[]) >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    (irule expr_body_pre_word_value >> simp[] >>
     qexistsl_tac [`cenv`,`env`,`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,`mid`] >>
     fs[expr_body_pre_gas_obs, bind_def]) >>
  `?tout. evaluate_type (get_tenv cx) ann = SOME tout` by
    metis_tac[convertScalarTypingTheory.expr_body_pre_scalar_convert, optionTheory.IS_SOME_EXISTS] >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `eval_operand x t = SOME (typed_val_to_w256 tv v)` by
    (gvs[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def] >> metis_tac[]) >>
  `op_prov G1 x = NONE /\ op_taint tn1 x = {}` by gvs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by gvs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `!name n. ann = FlagT name /\ FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
      cenv.ce_flag_n_members (nsid_to_string name) = n` by
    (rpt strip_tac >> irule convertScalarTypingTheory.scalar_flag_member_count >>
     qexistsl_tac [`cx`,`env`,`es`] >> gvs[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  drule_all scalar_convert_origin_path_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  Cases_on `convert_result cx (expr_type e) ann v`
  >- suspend "terminal_success" >>
  qpat_x_assum `!exc. INR _ = INR exc ==> _`
    (qspec_then `y` mp_tac) >> simp_tac bool_ss [] >> strip_tac >> gvs[] >>
  qexistsl_tac [`Abort err t'`,`Gf`,`tnf`] >> simp[] >> metis_tac[]
QED

Resume scalar_convert_selected_terminal[terminal_success]:
  rename1 `convert_result cx (expr_type e) ann v = INL vout` >>
  qpat_x_assum `!vout. INL _ = INL vout ==> _`
    (qspec_then `vout` mp_tac) >> simp_tac bool_ss [] >> strip_tac >>
  qexistsl_tac [`OK t'`,`Gf`,`tnf`] >> simp[] >> qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `bind _ _ _ = (INL v,mid)` mp_tac >>
     qpat_assum `valid_horizon cx st0 H mid.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_at (Pat `f st = _`) valid_horizon_frame >>
     simp[storage_trace_frame_bind, cj 5 evaluate_storage_trace_frame,
       storage_trace_frame_read_result]) >>
  `storage_well_formed_on cx mid (FST H)` by
    (irule dynamic_read_storage_well_formed >>
     conj_tac >- (qexists_tac `st0` >> simp[]) >>
     qexistsl_tac [`cenv`,`e`,`env`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,`v`] >>
     simp[expr_body_pre_gas_obs] >>
     `storage_well_formed_on cx es (FST H)` by metis_tac[] >>
     qpat_assum `storage_well_formed_on cx es (FST H)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[storage_well_formed_on_def] >> strip_tac >> rpt gen_tac >>
     `get_storage cx (es with gas_obs := gas_explicit marks s0.vs_gas_readings) b =
      get_storage cx es b` by
       (Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]) >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >> simp[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `alloca_inv t` by gvs[loweringPostsTheory.expr_post_def, stmt_state_rel_def] >>
  `alloca_history func t'` by
    (irule body_full_path_alloca_history >> conj_tac >- simp[] >>
     qexistsl_tac [`DF H`,`G1`,`Gf`,`PG`,`ctx`,`explicit`,`lo`,`[]`,`t`,`tn1`,`tnf`] >> simp[]) >>
  qpat_assum `!H. _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss())
      [expr_sim_full_post_def,expr_sim_full_endpoint_def])) >>
  drule_all dynamic_endpoint_vv_posts >>
  disch_then (qspec_then `lowered_value_type cenv (TypeBuiltin ann Convert ann [e])` strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t'` by
    (`t' = (t with vs_inst_idx := t'.vs_inst_idx) with vs_vars := t'.vs_vars` by
       metis_tac[stateFrameTheory.state_frame_eq_reconstruct] >>
     qpat_x_assum `t' = (t with vs_inst_idx := _) with vs_vars := _` SUBST1_TAC >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
  gvs[expr_vv_sim_full_post_def,expr_sim_full_endpoint_def,contextTheory.vv_location_def,
      expr_type_def]
QED
Finalise scalar_convert_selected_terminal

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
    fs[storage_trace_domain_def] >>
  `childQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 t /\
    ~t.vs_halted /\ mid.gas_obs = []` by metis_tac[] >>
  qpat_x_assum `childQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `childQ`, NoAsms] >> strip_tac >> gvs[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,s0,x,G0,tn0)
        H (INL v) mid G1 tn1 t` by
    (rpt strip_tac >> simp[expr_sim_full_post_def, expr_sim_full_endpoint_def] >>
     metis_tac[]) >>
  `fn_has_code sm sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> storage_well_formed_on cx es (FST H)` by
    metis_tac[] >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `is_word_type ann` by
    metis_tac[bodyPtrTypeBuiltinsScalarSemanticTheory.scalar_source_body_word_types] >>
  drule_all scalar_convert_selected_terminal >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac)
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
      reverse conj_tac >- simp[] >>
      qexistsl_tac [`Gf`,`mid`,`INL (Value vout)`,
        `u with vs_inst_idx := LENGTH sb.cs_current_insts`,`tnf`] >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!H. _ ==> expr_vv_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
        (drule_then (strip_assume_tac o SIMP_RULE (srw_ss())
          [expr_vv_sim_full_post_def,expr_sim_full_endpoint_def,expr_type_def])) >>
      gvs[contextTheory.vv_location_def]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`,`mid`,`Abort err t'`,`INR (Error (RuntimeError msg))`,`tnf`] >>
  gvs[fragExecTheory.exit_result_def,expr_exit_def,halt_exit_not_halt]
QED
Finalise convert_scalar_vv_sim_full
