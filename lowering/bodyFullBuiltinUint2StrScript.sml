(* Uint2Str's actual suffix and ghost updates do not depend on the horizon.
   The constructor fixed region still needs the ghost_inv_at clauses;
   the old lo=0 pointer result does not certify this successful joint prefix. *)
Theory bodyFullBuiltinUint2Str
Ancestors
  bodyFullPreds bodySimFull bodyFullOfVV bodyFullAllocaFresh
  bodyFullGhostFrame bodyFullUnwrapRun bodyFullShared bodyMemoryDefs
  bodyFullBuiltinUint2StrSuffix bodyFullBuiltinUint2StrRun
  exprSimUint2Str bodyMemBiUint2StrBlocks bodyPtrBytestringBuiltinsUintArithmetic
  gasOutcomeFullCompose gasOutcomeFull fragGasOriginPtrLoop fragGasSeqPtr
  bodyPtrDefs exprSimHypsDefs exprSimSource exprLoweringProps exprLowering
  gasExemptCert gasShadowCompileStmtHelpers gasShadowState gasShadow
  vyperStorageTrace vyperStorageFootprint vyperEvalExprPreservesScopesDom
  exprSimHash exprSimWordArgs exprSimProps exprSimHyps loweringPosts
  loweringStateRelDefs ptrDiscipline compileEnv fragExec
  vyperInterpreter vyperState vyperValue vyperContext vyperAST list words
Libs
  horizonTypeLib

val _ = Parse.hide "body";

Theorem uint2str_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann n args es.
    (builtin_args_length_ok (Uint2Str n) (LENGTH args) ==>
     body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann (Uint2Str n) args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Uint2Str n) args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Uint2Str n) args) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (Uint2Str n) args) es` suffices_by
    (strip_tac >> simp[] >> irule expr_sim_full_of_vv >> simp[] >>
     conj_tac >- (rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
       (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
     simp[optionTheory.IS_SOME_EXISTS] >>
     disch_then (qx_choose_then `rty` assume_tac) >>
     qexists_tac `rty` >> simp[] >> rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env (Builtin ann (Uint2Str n) args)
       (es with gas_obs := gs)` by simp[] >>
     drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[] >> metis_tac[]) >>
  `well_typed_expr env (Builtin ann (Uint2Str n) args)` by fs[expr_body_pre_def] >>
  drule uint2str_expr_types >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> fs[expr_body_pre_def]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty e es` by
    (fs[vyperContextTheory.builtin_args_length_ok_def, body_exprs_full_ok_def,
        body_expr_full_ok_def] >> metis_tac[]) >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_word >> simp[is_word_type_def]) >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule uint2str_compile_cut >>
  disch_then (qx_choose_then `op` (qx_choose_then `sm` strip_assume_tac)) >>
  `?sx ss. lower_value compile_expr cenv ty (gas_shadow_expr e) shadow_sa = (sx,ss)` by
    metis_tac[pairTheory.PAIR] >>
  `sx = op /\ gas_shadow_state sm ss` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `ty`, `e` |-> `e`]
      gas_shadow_stmt_lower_value) >> rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `sx = op` SUBST_ALL_TAC >>
  `as_ptr_val (BaseT (StringT n)) LocMemory
    (compile_uint2str op n (type_memory_bytes cenv (BaseT (StringT n))) ss) =
      (vv,shadow_sb)` by
    (qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, gas_shadow_builtin_def] >>
     disch_then (mp_tac o MATCH_MP uint2str_compile_cut) >>
     strip_tac >> gvs[]) >>
  `cs_extends sm sb /\ cs_extends ss shadow_sb` by
    (mp_tac (Q.INST [`x` |-> `op`, `ann` |-> `BaseT (StringT n)`,
      `N` |-> `type_memory_bytes cenv (BaseT (StringT n))`] uint2str_code_appends) >>
     simp[cs_appends_def] >> metis_tac[]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa ss` by
    metis_tac[cj 2 compile_expr_grows] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    metis_tac[cj 2 compile_expr_grows] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa ss shadow_func` by metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ e es`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `ss`, `op`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- fs[]) >> disch_tac >>
  suspend "compose"
QED

Resume uint2str_builtin_sim_full[compose]:
  `eval_expr cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v mid. ((case builtin_result cx mid.accounts (BaseT (StringT n))
        (Uint2Str n) [expr_type e] [v] of
          INL r => INL (Value r) | INR ex => INR ex),mid))` by
    (irule eval_expr_unary_builtin_action >>
     simp[precompile_builtin_def, builtin_args_length_ok_def]) >>
  pop_assum SUBST1_TAC >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >- simp[storage_trace_frame_def]
  >~ [`storage_trace_frame (bind _ _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res ee G' tn' t. childQ H res ee G' tn' t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      conj_tac >- simp[] >> simp[Abbr `childR`] >> rpt strip_tac >>
      Cases_on `res` >>
      gvs[exprSimDefsTheory.expr_exit_def, stmtSimPropsTheory.expr_exit_INR_type]) >>
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> childQ H res mid G1 tn1 t /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp_tac (srw_ss()) [Abbr `childQ`] >> strip_tac >>
  disj1_tac >> goal_assum (drule_at Any) >> simp[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es sa sm s0 mid v op t /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> childQ H res mid G1 tn1 t /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> BETA_TAC >> strip_tac >> gvs[]) >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `?X. v = IntV (&X) /\ X < dimword(:256) /\
       eval_operand op t = SOME (n2w X) /\ expr_sim_inv cenv cx env mid` by
    (irule (at_horizon_named "H" uint2str_operand_endpoint) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`s0.vs_gas_readings`, `marks`, `mid`] >> simp[]) >>
  qpat_x_assum `v = IntV _` SUBST_ALL_TAC >>
  suspend "suffix"
QED

Resume uint2str_builtin_sim_full[suffix]:
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL (IntV (&X)),mid)` by
    (qpat_assum `!tail. bind (eval_expr cx e) _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `res = INL (IntV (&X))` mp_tac >>
     qpat_assum `mid with gas_obs := [] = mid` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rw[]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `?observations. mid.storage_trace = es.storage_trace ++ observations` by
    (drule_all storage_trace_frame_prefix >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >> pop_assum mp_tac >>
     qpat_assum `mid.storage_trace = es.storage_trace ++ observations` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rw[] >> metis_tac[valid_horizon_append]) >>
  `local_ptrs_reserved cenv sm` by
    (fs[local_ptrs_reserved_def] >> rpt strip_tac >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `(!r len. cenv.ce_return_buf = SOME (PtrVar (Var r) len) ==> not_fresh_at sm r) /\
   (!r len. cenv.ce_return_pc = SOME (PtrVar (Var r) len) ==> not_fresh_at sm r)` by
    (conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[cs_extends_def] >> metis_tac[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `op_prov G1 op = NONE /\ op_taint tn1 op = {}` by fs[ptr_val_ok_def, is_word_type_def] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = _`
       (mp_then Any mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV)
         forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  mp_tac (Q.INST [`fn` |-> `func`, `ee` |-> `mid`, `s` |-> `t`, `G` |-> `G1`, `tn` |-> `tn1`,
    `H0` |-> `storage_trace_horizon mid.storage_trace`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL (at_horizon_named "H0"
      (at_horizon_named "H" uint2str_suffix_joint_full)))) >>
  impl_tac >- suspend "suffix_entry" >>
  disch_then (qx_choose_then `u` (qx_choose_then `HG` (qx_choose_then `tm` strip_assume_tac))) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`HG`, `mid`, `INL (Value (StringV (num_to_dec_string X)))`, `u`, `tm`] >>
  simp[uint2str_source_result] >>
  rpt strip_tac >> simp[expr_type_def, lowered_value_type_def, post_value_type_def] >>
  Cases_on `vv` >> gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def] >>
  rpt conj_tac >> simp[] >> decide_tac
QED

Resume uint2str_builtin_sim_full[suffix_entry]:
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
    metis_tac[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    expr_post H ctx func cenv cx e es sa sm s0 mid (IntV (&X)) op t /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by metis_tac[] >>
  `!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) /\
      aid < sa.cs_next_id ==> b+len <= t.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx es s0` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.alloca_next_valid_def] >> rpt strip_tac >>
     res_tac >> decide_tac) >>
  `!name b len. local_region cenv es.scopes s0 name b len ==> b+len <= t.vs_alloca_next` by
    (rpt strip_tac >>
     drule_all (at_horizon_named "H" body_local_region_frontier) >> decide_tac) >>
  simp[] >> conj_tac >> first_assum ACCEPT_TAC
QED

Finalise uint2str_builtin_sim_full
