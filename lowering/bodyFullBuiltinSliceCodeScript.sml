(* Self and external code Slice callers share one full code suffix. *)
Theory bodyFullBuiltinSliceCode
Ancestors
  bodyFullPreds bodySimFull bodyFullOfVV gasOutcomeFullCompose
  bodyFullBuiltinSliceOperands exprSimSliceExtcodeTyped
  bodyFullBuiltinBytestringQuery bodyFullBuiltinBytestringBuffer
  bodyFullBuiltinBytestringBounds bodyFullBuiltinBytestringCopy
  bodyFullBuiltinBytestringAbort
  bodyFullBuiltinSliceCodeTail
  exprSimSliceSelfCode
  bodyPtrBytestringBuiltinsWindowGhost wordArgsPtr
  exprSimSliceSource exprSimSliceOrdinaryFrame exprSimHypsDefs
  exprLowering vyperInterpreter vyperAST list
  fragExec emitHelperProps bodyPtrBytestringBuiltinsSlice
  bodyPtrBytestringBuiltinsBuffer loweringPosts loweringStateRelDefs
  reasonCodeResourcesPtr bodyPtrAttributeFields

Theorem slice_builtin_some_vv_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a n args es code_ty addr.
    (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_full_ok cx args
       | SOME (code_ty,addr) =>
           body_exprs_full_ok cx (TL args) /\
           (!s tail_vs t.
              eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_full_ok cx [addr])) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a (Slice n) args) es /\
    code_slice_source (Slice n) args = SOME (code_ty,addr) ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a (Slice n) args) es
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `code_slice_source _ _ = SOME _`
    (strip_assume_tac o REWRITE_RULE [code_slice_source_SOME]) >>
  gvs[] >>
  fs[vyperContextTheory.builtin_args_length_ok_def] >>
  rw[expr_vv_sim_full_def] >>
  `body_expr_full_ok cx start` by fs[body_exprs_full_ok_def] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty start es` by
    (`expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
     metis_tac[slice_code_child_full]) >>
  Cases_on `is_self_code (Builtin code_ty (Acc Code) [addr])`
  >- suspend "self_operands" >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `!xs. ~names_builtin (Slice n) xs` by metis_tac[] >>
  qpat_x_assum `!bt xs. _` kall_tac >>
  qpat_x_assum `compile_expr _ _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch, compile_builtin_dispatch_component_eq,
       exprBopLoweringTheory.lower_value_child_call, is_self_code_def, is_extcode_def, extcode_addr_expr_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule_all exprSimSliceExtcodeContextTheory.slice_extcode_pipeline_context >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def, gasShadowTheory.gas_shadow_builtin_def,
       compile_expr_builtin_dispatch,
       compile_builtin_dispatch_component_eq,
       exprBopLoweringTheory.lower_value_child_call, is_extcode_def, extcode_addr_expr_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  `~is_self_code (Builtin code_ty (Acc Code) [gas_shadow_expr addr])` by
    (qspec_then `Builtin code_ty (Acc Code) [addr]` mp_tac
       (GEN_ALL gasShadowCompilePureTheory.gas_shadow_is_self_code) >>
     pure_rewrite_tac[gasShadowTheory.gas_shadow_expr_def,
                      gasShadowTheory.gas_shadow_builtin_def, MAP] >> simp[]) >>
  gvs[] >>
  `local_ptrs_reserved cenv shadow_sa` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists `sa` >> fs[gasShadowStateTheory.gas_shadow_state_def]) >>
  qpat_assum `as_ptr_val _ _ (compile_slice_extcode _ _ _ _ _) = (_,shadow_sb)`
    (mp_then Any mp_tac exprSimSliceExtcodeContextTheory.slice_extcode_pipeline_context) >>
  disch_then drule_all >> strip_tac >>
  `start_op' = start_op /\ gas_shadow_state st1 st1'` by
    metis_tac[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value,
              gasShadowStateTheory.gas_shadow_compiles_def, pairTheory.FST, pairTheory.SND] >>
  gvs[] >>
  rev_drule slice_extcode_actions >> disch_then (fn th => rewrite_tac[th]) >>
  `expr_body_pre cenv cx env start es` by
    (`well_typed_expr env
        (Builtin a (Slice n) [Builtin code_ty (Acc Code) [addr];start;len])` by
       fs[expr_body_pre_def] >>
     drule slice_typed_args >> strip_tac >> gvs[] >>
     `expr_type start <> BaseT (BytesT (Dynamic 24576))` by simp[] >>
     `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
     drule exprSimSourceTheory.expr_body_pre_builtin_typed_arg >>
     disch_then (qspecl_then [`start`,`es`] mp_tac) >> simp[]) >>
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ start _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then drule >>
  disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ child_post _` >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- (rpt gen_tac >> BETA_TAC >>
    rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.storage_trace_frame_state_reads,
              vyperStorageTraceTheory.storage_trace_frame_lifts,
              vyperStorageTraceTheory.storage_trace_frame_return,
              exprSimSliceOrdinaryContinueTheory.slice_read_frame] >> rpt gen_tac)) >>
  conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    qexistsl_tac [`mid`,`t`,`v`] >> fs[]) >>
  conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  conj_tac >- simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame] >>
  qexists `\H res ee G tn t. child_post H res ee G tn t /\
    ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      reverse conj_tac
      >- (rpt strip_tac >> Cases_on `res` >>
          fs[exprSimDefsTheory.expr_exit_INL] >>
          rename1 `expr_exit (INR exc) r` >>
          qspec_then `Value` (qspec_then `INR exc`
            (fn th => simp[SIMP_RULE (srw_ss()) [] th]))
            exprSimDefsTheory.expr_exit_success_map) >>
      simp[]) >>
  rpt gen_tac >> strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> child_post _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[Abbr `child_post`, NoAsms] >> strip_tac >> gvs[] >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     strip_tac >>
     `expr_body_pre cenv cx env start
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
     qspecl_then [`cenv`,`cx`,`env`,`start`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []`,
       `INL v`,`mid with gas_obs := []`] mp_tac
       exprSimSourceTheory.expr_body_pre_eval >> fs[SF ETA_ss]) >>
  `body_expr_full_ok cx len` by
    (qpat_x_assum `body_exprs_full_ok cx [start;len]` mp_tac >>
     simp[body_exprs_full_ok_def] >> strip_tac >>
     first_x_assum irule >>
     qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (mp_tac o MATCH_MP vyperStatePreservationTheory.bind_split)) >>
     rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty len (mid with gas_obs := [])` by
    (mp_tac (Q.INST [`ct` |-> `code_ty`,`e` |-> `len`,
       `ee` |-> `mid with gas_obs := []`] slice_code_child_full) >> simp[]) >>
  `expr_body_pre cenv cx env len mid` by
    (`well_typed_expr env
        (Builtin a (Slice n) [Builtin code_ty (Acc Code) [addr];start;len])` by
       fs[expr_body_pre_def] >>
     drule slice_typed_args >> strip_tac >> gvs[] >>
     `expr_type len <> BaseT (BytesT (Dynamic 24576))` by simp[] >>
     drule exprSimSourceTheory.expr_body_pre_builtin_typed_arg >>
     disch_then (qspecl_then [`len`,`mid`] mp_tac) >> fs[]) >>
  `len_op' = len_op /\ gas_shadow_state st2 st2'` by
    metis_tac[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value,
              gasShadowStateTheory.gas_shadow_compiles_def, pairTheory.FST, pairTheory.SND] >>
  gvs[] >>
  `sa.cs_next_var <= st1.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `return_buf_frame d cenv st1 t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >>
     metis_tac[cj 6 (iffLR loweringPostsTheory.expr_post_def)]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def])) >>
     simp[]) >>
  `gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok mid` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ len _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`st1`,`st2`,`st1'`,`st2'`,
    `len_op`,`t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) len_post _` >>
  BETA_TAC >> irule gas_outcome_full_bind_all >>
  conj_tac >- (rpt gen_tac >> BETA_TAC >>
    rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.storage_trace_frame_state_reads,
              vyperStorageTraceTheory.storage_trace_frame_lifts,
              vyperStorageTraceTheory.storage_trace_frame_return,
              exprSimSliceOrdinaryContinueTheory.slice_read_frame] >> rpt gen_tac)) >>
  conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> fs[]) >>
  conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  conj_tac >- simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame] >>
  qexists `\H res ee G tn u. len_post H res ee G tn u /\
    ee.gas_obs = [] /\ ~u.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx len) _) _ _ _`
        (irule_at Any) >>
      reverse conj_tac
      >- (rpt strip_tac >> Cases_on `res` >>
          fs[exprSimDefsTheory.expr_exit_INL] >>
          rename1 `expr_exit (INR exc) r` >>
          qspec_then `Value` (qspec_then `INR exc`
            (fn th => simp[SIMP_RULE (srw_ss()) [] th]))
            exprSimDefsTheory.expr_exit_success_map) >>
      simp[]) >>
  qx_genl_tac [`len_marks`,`len_res`,`len_mid`,`G2`,`tn2`,`u`] >>
  strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon len_mid.storage_trace)
      len_mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> len_post _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon len_mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[Abbr `len_post`, NoAsms] >> strip_tac >>
  rename1 `len_res = INL lv` >> gvs[] >>
  `len_mid with gas_obs := [] = len_mid` by
    (qpat_assum `len_mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `expr_sim_inv cenv cx env len_mid` by
    (qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     qspecl_then [`cenv`,`cx`,`env`,`len`,
       `mid with gas_obs := gas_explicit len_marks t.vs_gas_readings ++ []`,
       `INL lv`,`len_mid with gas_obs := []`] mp_tac
       exprSimSourceTheory.expr_body_pre_eval >> fs[SF ETA_ss]) >>
  `?s vs t. eval_exprs cx [start;len] s = (INL vs,t)` by
    (mp_tac (Q.INST [`sv` |-> `v`,`es` |-> `es`,`mid` |-> `mid`,
       `fin` |-> `len_mid`,`xs` |-> `gas_explicit marks s0.vs_gas_readings`,
       `ys` |-> `gas_explicit len_marks t.vs_gas_readings`]
       slice_two_reads_replay_success) >> simp[]) >>
  `body_expr_full_ok cx addr` by
    (`body_exprs_full_ok cx [addr]` by metis_tac[] >>
     fs[body_exprs_full_ok_def]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty addr len_mid` by
    (mp_tac (Q.INST [`ct` |-> `code_ty`,`e` |-> `addr`,
       `ee` |-> `len_mid`] slice_code_child_full) >> simp[]) >>
  `expr_body_pre cenv cx env addr len_mid` by
    metis_tac[slice_code_address_body_pre] >>
  `addr_op' = addr_op /\ gas_shadow_state st3 st3'` by
    metis_tac[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value,
              gasShadowStateTheory.gas_shadow_compiles_def, pairTheory.FST, pairTheory.SND] >>
  gvs[] >>
  `st1.cs_next_var <= st2.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st1` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st1` >> simp[]) >>
  `return_buf_frame d cenv st2 u` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon len_mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`t`,`st1`] >> simp[] >>
     metis_tac[cj 6 (iffLR loweringPostsTheory.expr_post_def)]) >>
  `!H. valid_horizon cx st0 H len_mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx len_mid u /\
       storage_well_formed_on cx len_mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx len_mid G2 tn2 u` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def])) >>
     simp[]) >>
  `gas_admissible (bind (eval_expr cx addr) (read_result cx)) expr_res_ok len_mid` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ addr _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`st2`,`st3`,`st2'`,`st3'`,
    `addr_op`,`u`,`G2`,`tn2`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ (len_mid,u,G2,tn2) addr_post _` >>
  BETA_TAC >> irule gas_outcome_full_bind_all >>
  conj_tac >- (rpt gen_tac >> BETA_TAC >>
    rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.storage_trace_frame_state_reads,
              vyperStorageTraceTheory.storage_trace_frame_lifts,
              vyperStorageTraceTheory.storage_trace_frame_return] >> rpt gen_tac)) >>
  conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> fs[]) >>
  conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  conj_tac >- simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame] >>
  qexists `\H res ee G tn z. addr_post H res ee G tn z /\
    ee.gas_obs = [] /\ ~z.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx addr) _) _ _ _`
        (irule_at Any) >>
      reverse conj_tac
      >- (rpt strip_tac >> Cases_on `res` >>
          fs[exprSimDefsTheory.expr_exit_INL] >>
          rename1 `expr_exit (INR exc) r` >>
          qspec_then `Value` (qspec_then `INR exc`
            (fn th => simp[SIMP_RULE (srw_ss()) [] th]))
            exprSimDefsTheory.expr_exit_success_map) >>
      simp[]) >>
  qx_genl_tac [`addr_marks`,`addr_res`,`addr_mid`,`G3`,`tn3`,`z`] >>
  strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon addr_mid.storage_trace)
      addr_mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> addr_post _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon addr_mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[Abbr `addr_post`, NoAsms] >> strip_tac >>
  rename1 `addr_res = INL av` >> gvs[] >>
  `addr_mid with gas_obs := [] = addr_mid` by
    (qpat_assum `addr_mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `well_typed_expr env
      (Builtin a (Slice n) [Builtin code_ty (Acc Code) [addr];start;len])` by
    fs[expr_body_pre_def] >>
  `well_typed_expr env (Builtin code_ty (Acc Code) [addr])` by
    (qpat_x_assum `well_typed_expr env (Builtin _ (Slice _) _)` mp_tac >>
     simp[vyperTypeSystemTheory.well_typed_expr_def]) >>
  `code_ty = BaseT (BytesT (Dynamic 24576)) /\ expr_type addr = BaseT AddressT` by
    (qpat_assum `well_typed_expr env (Builtin _ (Acc Code) _)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[vyperTypeSystemTheory.well_typed_expr_def,
          vyperTypeSystemTheory.well_typed_builtin_app_def,
          vyperTypeSystemTheory.account_item_type_def,vyperTypeSystemTheory.env_item_type_def,
          vyperASTTheory.expr_type_def]) >>
  `a = BaseT (BytesT (Dynamic n)) /\ expr_type start = BaseT (UintT 256) /\
   expr_type len = BaseT (UintT 256) /\
   slice_operands_ok (Slice n) [Builtin code_ty (Acc Code) [addr];start;len]` by
    (qpat_assum `well_typed_expr env (Builtin _ (Slice _) _)`
       (mp_tac o MATCH_MP slice_typed_args) >> simp[vyperASTTheory.expr_type_def]) >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx start
      es sa st1 s0 mid v start_op t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes /\
   ?i. v = IntV (&i) /\ i < dimword (:256) /\
       eval_operand start_op t = SOME (n2w i)` by
    (qpat_x_assum `!tail. bind (eval_expr cx start) _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[] >>
     mp_tac (Q.INST [`e` |-> `start`,`ee` |-> `mid`,`s` |-> `s0`,
       `sb` |-> `st1`,`op` |-> `start_op`,
       `H` |-> `storage_trace_horizon mid.storage_trace`,
       `gs` |-> `gas_explicit marks s0.vs_gas_readings`]
       (INST_TYPE [alpha |-> ``:256``]
         exprSimSliceOrdinaryContinueTheory.slice_uint_read_post)) >>
     (impl_tac >- simp[]) >> simp[]) >>
  rename1 `v = IntV (&i)` >>
  gvs[] >>
  `expr_post (storage_trace_horizon len_mid.storage_trace) ctx func cenv cx len
      mid st1 st2 t len_mid lv len_op u` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon len_mid.storage_trace` mp_tac) >> simp[]) >>
  `MAP FDOM mid.scopes = MAP FDOM len_mid.scopes /\
   ?k. lv = IntV (&k) /\ k < dimword (:256) /\
       eval_operand len_op u = SOME (n2w k)` by
    (qpat_x_assum `!tail. bind (eval_expr cx len) _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[] >>
     mp_tac (Q.INST [`e` |-> `len`,`es` |-> `mid`,`ee` |-> `len_mid`,
       `sa` |-> `st1`,`sb` |-> `st2`,`s` |-> `t`,`t` |-> `u`,
       `v` |-> `lv`,`op` |-> `len_op`,
       `H` |-> `storage_trace_horizon len_mid.storage_trace`,
       `gs` |-> `gas_explicit len_marks t.vs_gas_readings`]
       (INST_TYPE [alpha |-> ``:256``]
         exprSimSliceOrdinaryContinueTheory.slice_uint_read_post)) >>
     (impl_tac >- simp[]) >> simp[]) >>
  rename1 `lv = IntV (&k)` >>
  gvs[] >>
  `expr_post (storage_trace_horizon addr_mid.storage_trace) ctx func cenv cx addr
      len_mid st2 st3 u addr_mid av addr_op z` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ addr _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon addr_mid.storage_trace` mp_tac) >> simp[]) >>
  `expr_sim_inv cenv cx env addr_mid /\
   MAP FDOM len_mid.scopes = MAP FDOM addr_mid.scopes /\
   ?bs. av = BytesV bs /\ LENGTH bs = 20 /\
     eval_operand addr_op z = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))` by
    (qpat_x_assum `!tail. bind (eval_expr cx addr) _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[] >>
     mp_tac (Q.INST [`e` |-> `addr`,`es` |-> `len_mid`,`ee` |-> `addr_mid`,
       `sa` |-> `st2`,`sb` |-> `st3`,`s` |-> `u`,`t` |-> `z`,
       `v` |-> `av`,`op` |-> `addr_op`,
       `H` |-> `storage_trace_horizon addr_mid.storage_trace`,
       `gs` |-> `gas_explicit addr_marks u.vs_gas_readings`]
       (INST_TYPE [alpha |-> ``:256``]
         exprSimSliceExtcodeContinueTheory.slice_address_read_post)) >>
     (impl_tac >- simp[]) >> simp[]) >>
  rename1 `av = BytesV bs` >>
  gvs[] >>
  rewrite_tac[exprSimSliceExtcodeContinueTheory.slice_extcode_source_tail] >>
  `0 < k /\ k <= n` by
    (qpat_x_assum `!tail. bind (eval_expr cx len) _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[] >>
     qpat_x_assum `slice_operands_ok _ _` mp_tac >>
     simp[vyperTypeSystemTheory.slice_operands_ok_def] >>
     Cases_on `len` >> simp[] >>
     rename1 `Literal lt lit` >> Cases_on `lit` >> simp[] >>
     strip_tac >> gvs[] >>
     drule exprSimSliceCapacityReadTheory.slice_literal_read_length >> intLib.ARITH_TAC) >>
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) < dimword (:256)` by
    (fs[expr_body_pre_def,allocLimitsTheory.alloc_limits_expr_def,
       allocLimitsTheory.type_alloc_ok_def,compileEnvTheory.is_word_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `32+n <= type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` by
    (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     simp[compileEnvTheory.type_memory_bytes_def,vfmConstantsTheory.word_size_def]) >>
  `(!x. start_op = Var x ==> not_fresh_at st1 x) /\
   (!l. start_op <> Label l)` by
    (qspecl_then [`cenv`,`cx`,`env`,`start`,`es`,`ty`,`sa`,`start_op`,`st1`]
       mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
     impl_tac >- simp[compileEnvTheory.is_word_type_def] >> strip_tac >> simp[]) >>
  `(!x. len_op = Var x ==> not_fresh_at st2 x) /\ (!l. len_op <> Label l)` by
    (qspecl_then [`cenv`,`cx`,`env`,`len`,`mid`,`ty`,`st1`,`len_op`,`st2`]
       mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
     impl_tac >- simp[compileEnvTheory.is_word_type_def] >> strip_tac >> simp[]) >>
  `(!x. addr_op = Var x ==> not_fresh_at st3 x) /\ (!l. addr_op <> Label l)` by
    (qspecl_then [`cenv`,`cx`,`env`,`addr`,`len_mid`,`ty`,`st2`,`addr_op`,`st3`]
       mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
     impl_tac >- simp[compileEnvTheory.is_word_type_def] >> strip_tac >> simp[]) >>
  `!x. start_op = Var x ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st1` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `eval_operand start_op u = SOME (n2w i)` by
    (qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==> expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon len_mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (mp_then Any (qspecl_then [`start_op`,`n2w i`] mp_tac) slice_post_operands) >>
     simp[]) >>
  `eval_operand start_op z = SOME (n2w i)` by
    (qpat_assum `!H. valid_horizon _ _ H addr_mid.storage_trace ==> expr_post _ _ _ _ _ addr _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon addr_mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (mp_then Any (qspecl_then [`start_op`,`n2w i`] mp_tac) slice_post_operands o CONJUNCT1) >>
     simp[]) >>
  `eval_operand len_op z = SOME (n2w k)` by
    (qpat_assum `!H. valid_horizon _ _ H addr_mid.storage_trace ==> expr_post _ _ _ _ _ addr _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon addr_mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (mp_then Any (qspecl_then [`len_op`,`n2w k`] mp_tac) slice_post_operands o CONJUNCT1) >>
     simp[]) >>
  `op_taint tn1 start_op = {} /\ op_prov G1 start_op = NONE /\
   op_taint tn2 len_op = {} /\ op_prov G2 len_op = NONE /\
   op_taint tn3 addr_op = {} /\ op_prov G3 addr_op = NONE` by
    (qpat_assum `ptr_val_ok _ _ _ start_op G1 tn1 t` mp_tac >>
     qpat_assum `ptr_val_ok _ _ _ len_op G2 tn2 u` mp_tac >>
     qpat_assum `ptr_val_ok _ _ _ addr_op G3 tn3 z` mp_tac >>
     qpat_assum `expr_type start = _` mp_tac >>
     qpat_assum `expr_type len = _` mp_tac >>
     qpat_assum `expr_type addr = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[bodyPtrDefsTheory.ptr_val_ok_def,compileEnvTheory.is_word_type_def]) >>
  qpat_assum `ghost_kept_at lo cenv mid st1 G1 tn1 t G2 tn2`
    (assume_tac o CONJUNCT1 o REWRITE_RULE[bodyPtrDefsTheory.ghost_kept_at_def]) >>
  qpat_assum `ghost_kept_at lo cenv len_mid st2 G2 tn2 u G3 tn3`
    (assume_tac o CONJUNCT1 o REWRITE_RULE[bodyPtrDefsTheory.ghost_kept_at_def]) >>
  `op_taint tn3 start_op = {} /\ op_prov G3 start_op = NONE /\
   op_taint tn3 len_op = {} /\ op_prov G3 len_op = NONE` by
    (qpat_assum `!x. not_fresh_at st1 x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at st2 x ==> _` mp_tac >>
     qpat_assum `!x. start_op = Var x ==> not_fresh_at st1 x` mp_tac >>
     qpat_assum `!x. start_op = Var x ==> not_fresh_at st2 x` mp_tac >>
     qpat_assum `!x. len_op = Var x ==> not_fresh_at st2 x` mp_tac >>
     qpat_assum `op_taint tn1 start_op = {}` mp_tac >>
     qpat_assum `op_prov G1 start_op = NONE` mp_tac >>
     qpat_assum `op_taint tn2 len_op = {}` mp_tac >>
     qpat_assum `op_prov G2 len_op = NONE` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `start_op` >> Cases_on `len_op` >>
     gvs[ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  Cases_on `compile_slice_extcode addr_op start_op len_op
      (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) st3` >>
  gvs[as_ptr_val_def] >>
  rename1 `compile_slice_extcode addr_op start_op len_op _ st3 = (out,sb)` >>
  drule exprSimSliceExtcodeTheory.slice_extcode_decompose >> strip_tac >>
  `stmt_state_rel (storage_trace_horizon addr_mid.storage_trace)
      ctx func cenv cx addr_mid z /\
   ghost_inv_at (DF (storage_trace_horizon addr_mid.storage_trace))
      lo d cenv cx addr_mid G3 tn3 z` by
    (qpat_assum `!H. valid_horizon _ _ H addr_mid.storage_trace ==> expr_post _ _ _ _ _ addr _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon addr_mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> fs[loweringPostsTheory.expr_post_def]) >>
  `alloca_inv z /\ allocas_from lo z /\ lo <= z.vs_alloca_next` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,bodyPtrDefsTheory.ghost_inv_at_def] >>
  `accounts_agree (storage_trace_horizon addr_mid.storage_trace)
     cx (addr_mid:evaluation_state).accounts z.vs_accounts /\ accounts_well_typed (addr_mid:evaluation_state).accounts` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def,loweringStateRelDefsTheory.accounts_rel_def,
       exprSimHypsDefsTheory.expr_sim_inv_def] >>
  `((lookup_account
      (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))) z.vs_accounts).code =
      (lookup_account (word_of_bytes_be bs) (addr_mid:evaluation_state).accounts).code) /\
   LENGTH (lookup_account (word_of_bytes_be bs) (addr_mid:evaluation_state).accounts).code <= 24576` by
    (drule_all exprSimSliceExtcodeTheory.slice_extcode_account >> simp[]) >>
  `LENGTH (lookup_account (word_of_bytes_be bs) (addr_mid:evaluation_state).accounts).code < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  `step_inst_base (mk_inst st3.cs_next_id EXTCODESIZE [addr_op]
      [STRING #"%" (toString st3.cs_next_var)]) z =
    OK (update_var (STRING #"%" (toString st3.cs_next_var))
      (n2w (LENGTH (lookup_account (word_of_bytes_be bs) (addr_mid:evaluation_state).accounts).code)) z)` by
    (qpat_assum `eval_operand addr_op z = SOME _`
       (mp_then Any mp_tac exprSimSliceExtcodeTheory.slice_extcodesize_step) >> simp[]) >>
  `!x. start_op = Var x ==> not_fresh_at st3 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st2` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `!x. len_op = Var x ==> not_fresh_at st3 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st2` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at st3 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at st3 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `!H. valid_horizon cx st0 H addr_mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx addr_mid z /\
     storage_well_formed_on cx addr_mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx addr_mid G3 tn3 z` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H addr_mid.storage_trace ==>
        expr_post _ _ _ _ _ addr _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (mp_tac o REWRITE_RULE[loweringPostsTheory.expr_post_def])) >> simp[]) >>
  `!v wd. i+k <= LENGTH
      (lookup_account (word_of_bytes_be bs) (addr_mid:evaluation_state).accounts).code /\
    v.vs_accounts = z.vs_accounts /\ v.vs_call_ctx = z.vs_call_ctx /\
    v.vs_code = z.vs_code /\
    eval_operand dst v = SOME wd /\ eval_operand start_op v = SOME (n2w i) /\
    eval_operand len_op v = SOME (n2w k) /\
    (EXTCODECOPY = EXTCODECOPY ==> eval_operand addr_op v = eval_operand addr_op z) ==>
    step_inst_base (mk_inst se.cs_next_id EXTCODECOPY [addr_op;dst;start_op;len_op] []) v =
      OK (write_memory_with_expansion (w2n wd)
        (TAKE k (DROP i (lookup_account (word_of_bytes_be bs)
          (addr_mid:evaluation_state).accounts).code)) v)` by
    (rpt strip_tac >>
     mp_tac (exprSimSliceExtcodeTheory.slice_extcodecopy_step |> Q.INST
       [`addr` |-> `addr_op`,`dst` |-> `dst`,`start` |-> `start_op`,`len` |-> `len_op`,
        `s` |-> `v`,`a` |-> `typed_val_to_w256 (BaseTV AddressT) (BytesV bs)`,
        `d` |-> `wd`,`b` |-> `n2w i`,`n` |-> `n2w k`,`iid` |-> `se.cs_next_id`]) >>
     simp[wordsTheory.w2n_n2w]) >>
  rpt (qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac) >>
  (fn (asl,w) =>
    let val provider = bodyFullBuiltinSliceCodeTailTheory.slice_code_tail_full
        val args = snd (strip_comb w)
        val actual_df = fst (pairSyntax.dest_pair (hd args))
        val actual_source = el 5 args
        val formal_df = first (fn v => fst (dest_var v) = "DF") (free_vars (concl provider))
        val formal_source = first (fn v => fst (dest_var v) = "source") (free_vars (concl provider))
        val post = find_term (fn tm =>
          let val (f,xs) = strip_comb tm in
            is_const f andalso fst (dest_const f) = "vv_post" andalso length xs = 14
          end) w
        val actual_e = el 6 (snd (strip_comb post))
        val actual_args = el 3 (snd (strip_comb actual_e))
        val formal_e = first (fn v => fst (dest_var v) = "e") (free_vars (concl provider))
        val formal_args = first (fn v => fst (dest_var v) = "args") (free_vars (concl provider))
        val tys = match_type (type_of formal_df) (type_of actual_df)
        val fields = Q.INST [`sa` |-> `st3`,`s` |-> `z`,`G` |-> `G3`,`tn` |-> `tn3`,
      `start` |-> `start_op`,`cnt` |-> `len_op`,`limit` |-> `src_len`,
      `query_op` |-> `EXTCODESIZE`,`query_ops` |-> `[addr_op]`,
      `copy_op` |-> `EXTCODECOPY`,`copy_ops` |-> `[addr_op;dst;start_op;len_op]`,
      `addr` |-> `addr_op`,`data` |-> `dst`,
      `N` |-> `type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))`,
      `code` |-> `(lookup_account (word_of_bytes_be bs) (addr_mid:evaluation_state).accounts).code`,
      `es` |-> `addr_mid`,`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
      `tops` |-> `cx_tops cx`]
          (INST_TYPE tys provider)
        val typed = INST [inst tys formal_df |-> actual_df,
          inst tys formal_source |-> actual_source,inst tys formal_e |-> actual_e,
          inst tys formal_args |-> actual_args] fields
    in mp_tac typed (asl,w) end) >>
  (impl_tac >-
    (simp[MEM,vyperStateTheory.get_accounts_def,vyperStateTheory.bind_def,
      vyperStateTheory.lift_sum_def,vyperStateTheory.return_def,
      vyperStateTheory.raise_def,exprSimSliceSourceTheory.slice_bytes_nat] >>
     conj_tac
     >- (qpat_assum `!x. start_op = Var x ==> not_fresh_at st3 x` mp_tac >>
         qpat_assum `!x. len_op = Var x ==> not_fresh_at st3 x` mp_tac >>
         rpt (pop_assum kall_tac) >> metis_tac[]) >>
     Cases_on `i+k <= LENGTH
       (lookup_account (word_of_bytes_be bs) (addr_mid:evaluation_state).accounts).code` >>
     simp[vyperStateTheory.return_def,vyperStateTheory.raise_def])) >>
  strip_tac >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  reverse conj_tac >- simp[] >>
  qx_genl_tac [`H`,`res`,`ee`,`HG`,`tm`,`target`] >> strip_tac >>
  RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `res = INL _ /\ _` strip_assume_tac >>
  qpat_assum `res = INL _` SUBST_ALL_TAC >>
  qabbrev_tac `copied = TAKE k (DROP i
    (lookup_account (word_of_bytes_be bs) (addr_mid:evaluation_state).accounts).code)` >>
  `ee with gas_obs := [] = ee` by
    (qpat_assum `ee.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `ee = addr_mid` by
    (qunabbrev_tac `copied` >>
     qpat_assum `!tail. bind get_accounts _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `k <= n` mp_tac >>
     qpat_assum `ee with gas_obs := [] = ee` mp_tac >>
     qpat_assum `addr_mid with gas_obs := [] = addr_mid` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `i+k <= LENGTH
       (lookup_account (word_of_bytes_be bs) (addr_mid:evaluation_state).accounts).code` >>
     fs[vyperStateTheory.get_accounts_def,vyperStateTheory.bind_def,
        vyperStateTheory.lift_sum_def,vyperStateTheory.return_def,
        vyperStateTheory.raise_def,exprSimSliceSourceTheory.slice_bytes_nat] >>
     qpat_assum `k <= n` (fn kn =>
       full_simp_tac (srw_ss()) [kn,vyperStateTheory.return_def,vyperStateTheory.raise_def]) >>
     qpat_assum `addr_mid with gas_obs := _ = ee with gas_obs := []`
       (mp_tac o Q.AP_TERM `\st:evaluation_state. st with gas_obs := []`) >> simp[]) >>
  qpat_assum `ee = addr_mid` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H addr_mid.storage_trace ==>
       valid_horizon cx st0 H len_mid.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `!tail. bind (eval_expr cx addr) _ _ = _`
       (qspec_then `[]`
         (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame)) >>
     simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
  `!H. valid_horizon cx st0 H len_mid.storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
       (qspec_then `[]`
         (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame)) >>
     simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
       (qspec_then `[]`
         (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame)) >>
     simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
  `valid_horizon cx st0 H len_mid.storage_trace` by
    (qpat_assum `!H. valid_horizon _ _ H addr_mid.storage_trace ==>
       valid_horizon _ _ H len_mid.storage_trace` irule >> simp[]) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
       valid_horizon _ _ H mid.storage_trace` irule >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       valid_horizon _ _ H es.storage_trace` irule >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
      expr_post H _ _ _ _ start _ _ _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
      expr_post H _ _ _ _ len _ _ _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H addr_mid.storage_trace ==>
      expr_post H _ _ _ _ addr _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  `sa.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= st2.cs_next_id /\
   st2.cs_next_id <= st3.cs_next_id /\ st2.cs_next_var <= st3.cs_next_var` by
    (qpat_assum `ci_mono sa st1` mp_tac >>
     qpat_assum `ci_mono st1 st2` mp_tac >>
     qpat_assum `ci_mono st2 st3` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `vv_post H ctx func cenv cx
      (Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
        [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code) [addr];start;len])
      mid st1 sb t addr_mid (Value (BytesV copied))
      (LocatedValue (BaseT (BytesT (Dynamic n)))
        (mk_ptr out LocMemory)) target` by
    (`stmt_state_rel H ctx func cenv cx mid t` by
       (qpat_assum `expr_post H _ _ _ _ start _ _ _ _ _ _ _ _`
          (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[loweringPostsTheory.expr_post_def])) >>
     (fn (asl,w) =>
       let val provider = exprSimSliceOrdinaryContinueTheory.slice_two_operand_post_rebase
           val actual = hd (snd (strip_comb w))
           val formal = first (fn v => fst (dest_var v) = "H")
             (free_vars (concl provider))
           val tys = match_type (type_of formal) (type_of actual)
           val typed = INST [inst tys formal |-> actual] (INST_TYPE tys provider)
       in mp_tac (Q.INST [`ctx` |-> `ctx`,`func` |-> `func`,
       `cenv` |-> `cenv`,`cx` |-> `cx`,`ec` |-> `mid`,`sc` |-> `st1`,`u` |-> `t`,
       `e1` |-> `len_mid`,`sd` |-> `st2`,`t` |-> `u`,
       `e2` |-> `addr_mid`,`se` |-> `st3`,`r` |-> `z`,
       `start` |-> `len`,`len` |-> `addr`,
       `v1` |-> `IntV (&k)`,`op1` |-> `len_op`,
       `v2` |-> `BytesV bs`,`op2` |-> `addr_op`,`sf` |-> `sb`,`ef` |-> `addr_mid`,
       `tv` |-> `Value (BytesV copied)`,
       `result` |-> `Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
         [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code) [addr];start;len]`,
       `vv` |-> `LocatedValue (BaseT (BytesT (Dynamic n)))
         (mk_ptr out LocMemory)`,`z` |-> `target`]
       typed) (asl,w) end) >>
     (impl_tac >- simp[loweringPostsTheory.expr_has_effect_thm]) >>
     disch_then ACCEPT_TAC) >>
  `wb_frame cenv es mid sa s0 t` by
    (qpat_assum `expr_post H _ _ _ _ start _ _ _ _ _ _ _ _`
       (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame)) >>
  `(~expr_has_effect
      (Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
        [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code) [addr];start;len]) ==>
      pure_frame cenv func es sa s0 t)` by
    (simp[loweringPostsTheory.expr_has_effect_thm] >> strip_tac >>
     qpat_assum `expr_post H _ _ _ _ start _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac exprSimWordArgsTheory.expr_post_pure_frame) >> simp[]) >>
  `vv_post H ctx func cenv cx
      (Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
        [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code) [addr];start;len])
      es sa sb s0 addr_mid (Value (BytesV copied))
      (LocatedValue (BaseT (BytesT (Dynamic n)))
        (mk_ptr out LocMemory)) target` by
    (match_mp_tac (Q.INST [`es1` |-> `mid`,`sm` |-> `st1`,`t` |-> `t`]
       exprSimCalldataSliceTheory.vv_post_prefix_frame) >> simp[]) >>
  `wb_frame cenv mid len_mid st1 t u` by
    (qpat_assum `expr_post H _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame)) >>
  `wb_frame cenv len_mid addr_mid st2 u z` by
    (qpat_assum `expr_post H _ _ _ _ addr _ _ _ _ _ _ _ _`
       (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame)) >>
  `wb_frame cenv es len_mid sa s0 u` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then Any (qspecl_then [`sa`,`mid`,`len_mid`,`st1`,`t`,`u`] mp_tac)
         exprSimWordArgsTheory.wb_frame_trans) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  `sa.cs_next_var <= st2.cs_next_var /\ sa.cs_next_var <= st3.cs_next_var /\
   sa.cs_next_id <= st2.cs_next_id /\ sa.cs_next_id <= st3.cs_next_id` by decide_tac >>
  `wb_frame cenv es addr_mid sa s0 z` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then Any (qspecl_then [`sa`,`len_mid`,`addr_mid`,`st2`,`u`,`z`] mp_tac)
         exprSimWordArgsTheory.wb_frame_trans) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then Any (qspecl_then [`lo`,`sa`,`G0`,`tn0`,`G1`,`tn1`,
         `mid`,`st1`,`G2`,`tn2`,`t`,`mid`] mp_tac)
         wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G3 tn3` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then Any (qspecl_then [`lo`,`sa`,`G0`,`tn0`,`G2`,`tn2`,
         `len_mid`,`st2`,`G3`,`tn3`,`u`,`len_mid`] mp_tac)
         wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 HG tm` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then Any (qspecl_then [`lo`,`sa`,`G0`,`tn0`,`G3`,`tn3`,
         `addr_mid`,`st3`,`HG`,`tm`,`z`,`addr_mid`] mp_tac)
         wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  qpat_assum `vv_post H ctx func cenv cx _ es sa sb s0 addr_mid _ _ target`
    (assume_tac o REWRITE_RULE[contextTheory.mk_ptr_def]) >>
  qpat_assum `vv_store_bound cx _ _ addr_mid _ _ target`
    (assume_tac o REWRITE_RULE[contextTheory.mk_ptr_def]) >>
  qpat_assum `ptr_vv_ok cx _ _ _ addr_mid HG tm target`
    (assume_tac o REWRITE_RULE[contextTheory.mk_ptr_def]) >>
  simp[vyperASTTheory.expr_type_def,exprLoweringTheory.lowered_value_type_def,
       contextTheory.mk_ptr_def,contextTheory.vv_location_def]
QED

Resume slice_builtin_some_vv_full[self_operands]:
  qpat_assum `is_self_code _`
    (mp_tac o REWRITE_RULE[exprSimSliceSelfCodeTheory.is_self_code_thm]) >>
  disch_then (qx_choose_then `ct` (qx_choose_then `self_ty` strip_assume_tac)) >>
  gvs[] >>
  `well_typed_expr env
      (Builtin a (Slice n) [Builtin code_ty (Acc Code) [Builtin self_ty (Env SelfAddr) []];start;len])` by
    fs[expr_body_pre_def] >>
  `well_typed_expr env (Builtin code_ty (Acc Code) [Builtin self_ty (Env SelfAddr) []])` by
    (qpat_x_assum `well_typed_expr env (Builtin _ (Slice _) _)` mp_tac >>
     simp[vyperTypeSystemTheory.well_typed_expr_def]) >>
  `code_ty = BaseT (BytesT (Dynamic 24576)) /\ self_ty = BaseT AddressT` by
    (qpat_assum `well_typed_expr env (Builtin _ (Acc Code) _)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[vyperTypeSystemTheory.well_typed_expr_def,
          vyperTypeSystemTheory.well_typed_builtin_app_def,
          vyperTypeSystemTheory.account_item_type_def,vyperTypeSystemTheory.env_item_type_def,
          vyperASTTheory.expr_type_def]) >>
  `a = BaseT (BytesT (Dynamic n)) /\ expr_type start = BaseT (UintT 256) /\
   expr_type len = BaseT (UintT 256) /\
   slice_operands_ok (Slice n) [Builtin code_ty (Acc Code) [Builtin self_ty (Env SelfAddr) []];start;len]` by
    (qpat_assum `well_typed_expr env (Builtin _ (Slice _) _)`
       (mp_tac o MATCH_MP slice_typed_args) >> simp[vyperASTTheory.expr_type_def]) >>
  gvs[] >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `!xs. ~names_builtin (Slice n) xs` by metis_tac[] >>
  qpat_x_assum `!bt xs. _` kall_tac >>
  qpat_x_assum `compile_expr _ _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
       exprBopLoweringTheory.lower_value_child_call,is_self_code_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  Cases_on `compile_slice_code start_op len_op
    (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) st2` >>
  gvs[as_ptr_val_def] >>
  rename1 `compile_slice_code start_op len_op _ st2 = (out,sb)` >>
  drule exprSimSliceSelfCodeTheory.slice_code_decompose >> strip_tac >> gvs[] >>
  drule_all exprSimSliceSelfCodeTheory.slice_self_code_pipeline_context >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def,gasShadowTheory.gas_shadow_builtin_def,
       compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
       exprBopLoweringTheory.lower_value_child_call,is_self_code_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  Cases_on `compile_slice_code start_op' len_op'
    (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) st2'` >>
  gvs[as_ptr_val_def] >>
  `local_ptrs_reserved cenv shadow_sa` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> fs[gasShadowStateTheory.gas_shadow_state_def]) >>
  qpat_assum `compile_slice_code start_op' len_op' _ st2' = _`
    (mp_then Any strip_assume_tac exprSimSliceSelfCodeTheory.slice_code_decompose) >>
  gvs[] >>
  drule_all exprSimSliceSelfCodeTheory.slice_self_code_pipeline_context >> strip_tac >>
  `start_op' = start_op /\ gas_shadow_state st1 st1'` by
    metis_tac[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value,
              gasShadowStateTheory.gas_shadow_compiles_def,pairTheory.FST,pairTheory.SND] >>
  gvs[] >>
  rewrite_tac[exprSimSliceSelfCodeTheory.slice_self_code_actions] >>
  `expr_body_pre cenv cx env start es` by
    (`well_typed_expr env
        (Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
          [Builtin (BaseT AddressT) (Env SelfAddr) []];start;len])` by
       fs[expr_body_pre_def] >>
     drule slice_typed_args >> strip_tac >> gvs[] >>
     `expr_type start <> BaseT (BytesT (Dynamic 24576))` by simp[] >>
     `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
     drule exprSimSourceTheory.expr_body_pre_builtin_typed_arg >>
     disch_then (qspecl_then [`start`,`es`] mp_tac) >> simp[]) >>
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ start _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then drule >>
  disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ child_post _` >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- (rpt gen_tac >> BETA_TAC >>
    rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.storage_trace_frame_state_reads,
              vyperStorageTraceTheory.storage_trace_frame_lifts,
              vyperStorageTraceTheory.storage_trace_frame_return,
              exprSimSliceOrdinaryContinueTheory.slice_read_frame] >> rpt gen_tac)) >>
  conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    qexistsl_tac [`mid`,`t`,`v`] >> fs[]) >>
  conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  conj_tac >- simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame] >>
  qexists `\H res ee G tn t. child_post H res ee G tn t /\
    ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      reverse conj_tac
      >- (rpt strip_tac >> Cases_on `res` >>
          fs[exprSimDefsTheory.expr_exit_INL] >>
          rename1 `expr_exit (INR exc) exit_r` >>
          qspec_then `Value` (qspec_then `INR exc`
            (fn th => simp[SIMP_RULE (srw_ss()) [] th]))
            exprSimDefsTheory.expr_exit_success_map) >>
      simp[]) >>
  rpt gen_tac >> strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> child_post _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[Abbr `child_post`, NoAsms] >> strip_tac >> gvs[] >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     strip_tac >>
     `expr_body_pre cenv cx env start
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
     qspecl_then [`cenv`,`cx`,`env`,`start`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []`,
       `INL v`,`mid with gas_obs := []`] mp_tac
       exprSimSourceTheory.expr_body_pre_eval >> fs[SF ETA_ss]) >>
  `body_expr_full_ok cx len` by
    (qpat_x_assum `body_exprs_full_ok cx [start;len]` mp_tac >>
     simp[body_exprs_full_ok_def] >> strip_tac >>
     first_x_assum irule >>
     qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (mp_tac o MATCH_MP vyperStatePreservationTheory.bind_split)) >>
     rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty len (mid with gas_obs := [])` by
    (mp_tac (Q.INST [`a` |-> `BaseT (BytesT (Dynamic n))`,
       `ct` |-> `BaseT (BytesT (Dynamic 24576))`,
       `addr` |-> `Builtin (BaseT AddressT) (Env SelfAddr) []`,`e` |-> `len`,
       `ee` |-> `mid with gas_obs := []`] slice_code_child_full) >> simp[]) >>
  `expr_body_pre cenv cx env len mid` by
    (`well_typed_expr env
        (Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
          [Builtin (BaseT AddressT) (Env SelfAddr) []];start;len])` by
       fs[expr_body_pre_def] >>
     drule slice_typed_args >> strip_tac >> gvs[] >>
     `expr_type len <> BaseT (BytesT (Dynamic 24576))` by simp[] >>
     drule exprSimSourceTheory.expr_body_pre_builtin_typed_arg >>
     disch_then (qspecl_then [`len`,`mid`] mp_tac) >> fs[]) >>
  `len_op' = len_op /\ gas_shadow_state st2 st2'` by
    metis_tac[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value,
              gasShadowStateTheory.gas_shadow_compiles_def, pairTheory.FST, pairTheory.SND] >>
  gvs[] >>
  `sa.cs_next_var <= st1.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `return_buf_frame d cenv st1 t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >>
     metis_tac[cj 6 (iffLR loweringPostsTheory.expr_post_def)]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def])) >>
     simp[]) >>
  `gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok mid` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ len _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`st1`,`st2`,`st1'`,`st2'`,
    `len_op`,`t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) len_post _` >>
  BETA_TAC >> irule gas_outcome_full_bind_all >>
  conj_tac >- (rpt gen_tac >> BETA_TAC >>
    rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.storage_trace_frame_state_reads,
              vyperStorageTraceTheory.storage_trace_frame_lifts,
              vyperStorageTraceTheory.storage_trace_frame_return,
              exprSimSliceOrdinaryContinueTheory.slice_read_frame] >> rpt gen_tac)) >>
  conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> fs[]) >>
  conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  conj_tac >- simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame] >>
  qexists `\H res ee G tn u. len_post H res ee G tn u /\
    ee.gas_obs = [] /\ ~u.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx len) _) _ _ _`
        (irule_at Any) >>
      reverse conj_tac
      >- (rpt strip_tac >> Cases_on `res` >>
          fs[exprSimDefsTheory.expr_exit_INL] >>
          rename1 `expr_exit (INR exc) exit_r` >>
          qspec_then `Value` (qspec_then `INR exc`
            (fn th => simp[SIMP_RULE (srw_ss()) [] th]))
            exprSimDefsTheory.expr_exit_success_map) >>
      simp[]) >>
  qx_genl_tac [`len_marks`,`len_res`,`len_mid`,`G2`,`tn2`,`u`] >>
  strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon len_mid.storage_trace)
      len_mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> len_post _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon len_mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[Abbr `len_post`, NoAsms] >> strip_tac >>
  rename1 `len_res = INL lv` >> gvs[] >>
  `len_mid with gas_obs := [] = len_mid` by
    (qpat_assum `len_mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `expr_sim_inv cenv cx env len_mid` by
    (qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     qspecl_then [`cenv`,`cx`,`env`,`len`,
       `mid with gas_obs := gas_explicit len_marks t.vs_gas_readings ++ []`,
       `INL lv`,`len_mid with gas_obs := []`] mp_tac
       exprSimSourceTheory.expr_body_pre_eval >> fs[SF ETA_ss]) >>
  `!H. valid_horizon cx st0 H len_mid.storage_trace ==>
      expr_post H ctx func cenv cx len mid st1 st2 t len_mid lv len_op u` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
        expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx start
      es sa st1 s0 mid v start_op t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes /\
   ?i. v = IntV (&i) /\ i < dimword (:256) /\
       eval_operand start_op t = SOME (n2w i)` by
    (qpat_x_assum `!tail. bind (eval_expr cx start) _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[] >>
     mp_tac (Q.INST [`e` |-> `start`,`ee` |-> `mid`,`s` |-> `s0`,
       `sb` |-> `st1`,`op` |-> `start_op`,
       `H` |-> `storage_trace_horizon mid.storage_trace`,
       `gs` |-> `gas_explicit marks s0.vs_gas_readings`]
       (INST_TYPE [alpha |-> ``:256``]
         exprSimSliceOrdinaryContinueTheory.slice_uint_read_post)) >>
     (impl_tac >- simp[]) >> simp[]) >>
  rename1 `v = IntV (&i)` >>
  gvs[] >>
  `expr_post (storage_trace_horizon len_mid.storage_trace) ctx func cenv cx len
      mid st1 st2 t len_mid lv len_op u` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon len_mid.storage_trace` mp_tac) >> simp[]) >>
  `MAP FDOM mid.scopes = MAP FDOM len_mid.scopes /\
   ?k. lv = IntV (&k) /\ k < dimword (:256) /\
       eval_operand len_op u = SOME (n2w k)` by
    (qpat_x_assum `!tail. bind (eval_expr cx len) _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[] >>
     mp_tac (Q.INST [`e` |-> `len`,`es` |-> `mid`,`ee` |-> `len_mid`,
       `sa` |-> `st1`,`sb` |-> `st2`,`s` |-> `t`,`t` |-> `u`,
       `v` |-> `lv`,`op` |-> `len_op`,
       `H` |-> `storage_trace_horizon len_mid.storage_trace`,
       `gs` |-> `gas_explicit len_marks t.vs_gas_readings`]
       (INST_TYPE [alpha |-> ``:256``]
         exprSimSliceOrdinaryContinueTheory.slice_uint_read_post)) >>
     (impl_tac >- simp[]) >> simp[]) >>
  rename1 `lv = IntV (&k)` >>
  gvs[] >>
  `0 < k /\ k <= n` by
    (qpat_x_assum `!tail. bind (eval_expr cx len) _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[] >>
     qpat_x_assum `slice_operands_ok _ _` mp_tac >>
     simp[vyperTypeSystemTheory.slice_operands_ok_def] >>
     Cases_on `len` >> simp[] >>
     rename1 `Literal lt lit` >> Cases_on `lit` >> simp[] >>
     strip_tac >> gvs[] >>
     drule exprSimSliceCapacityReadTheory.slice_literal_read_length >> intLib.ARITH_TAC) >>
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) < dimword (:256)` by
    (fs[expr_body_pre_def,allocLimitsTheory.alloc_limits_expr_def,
       allocLimitsTheory.type_alloc_ok_def,compileEnvTheory.is_word_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `32+n <= type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` by
    (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     simp[compileEnvTheory.type_memory_bytes_def,vfmConstantsTheory.word_size_def]) >>
  `(!x. start_op = Var x ==> not_fresh_at st1 x) /\
   (!l. start_op <> Label l)` by
    (qspecl_then [`cenv`,`cx`,`env`,`start`,`es`,`ty`,`sa`,`start_op`,`st1`]
       mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
     impl_tac >- simp[compileEnvTheory.is_word_type_def] >> strip_tac >> simp[]) >>
  `(!x. len_op = Var x ==> not_fresh_at st2 x) /\ (!l. len_op <> Label l)` by
    (qspecl_then [`cenv`,`cx`,`env`,`len`,`mid`,`ty`,`st1`,`len_op`,`st2`]
       mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
     impl_tac >- simp[compileEnvTheory.is_word_type_def] >> strip_tac >> simp[]) >>
  `!x. start_op = Var x ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st1` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `eval_operand start_op u = SOME (n2w i)` by
    (qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==> expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon len_mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (mp_then Any (qspecl_then [`start_op`,`n2w i`] mp_tac) slice_post_operands) >>
     simp[]) >>
  `op_taint tn1 start_op = {} /\ op_prov G1 start_op = NONE /\
   op_taint tn2 len_op = {} /\ op_prov G2 len_op = NONE` by
    (qpat_assum `ptr_val_ok _ _ _ start_op G1 tn1 t` mp_tac >>
     qpat_assum `ptr_val_ok _ _ _ len_op G2 tn2 u` mp_tac >>
     qpat_assum `expr_type start = _` mp_tac >>
     qpat_assum `expr_type len = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[bodyPtrDefsTheory.ptr_val_ok_def,compileEnvTheory.is_word_type_def]) >>
  qpat_assum `ghost_kept_at lo cenv mid st1 G1 tn1 t G2 tn2`
    (assume_tac o CONJUNCT1 o REWRITE_RULE[bodyPtrDefsTheory.ghost_kept_at_def]) >>
  `op_taint tn2 start_op = {} /\ op_prov G2 start_op = NONE` by
    (qpat_assum `!x. not_fresh_at st1 x ==> _` mp_tac >>
     qpat_assum `!x. start_op = Var x ==> not_fresh_at st1 x` mp_tac >>
     qpat_assum `op_taint tn1 start_op = {}` mp_tac >>
     qpat_assum `op_prov G1 start_op = NONE` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> Cases_on `start_op` >>
     gvs[ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H len_mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx len_mid u /\
     storage_well_formed_on cx len_mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx len_mid G2 tn2 u` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
        ghost_inv_at _ _ _ _ _ _ G2 tn2 u`
       (qspec_then `H` mp_tac) >>
     qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
        expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _`
       (qspec_then `H` (mp_tac o REWRITE_RULE[loweringPostsTheory.expr_post_def])) >> simp[]) >>
  `u.vs_code = cx.txn.code` by
    (qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
        stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon len_mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     fs[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def,loweringStateRelDefsTheory.accounts_rel_def]) >>
  `LENGTH cx.txn.code < dimword (:256)` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.context_well_typed_def,wordsTheory.dimword_def]) >>
  `step_inst_base (mk_inst st2.cs_next_id CODESIZE []
      [STRING #"%" (toString st2.cs_next_var)]) u =
    OK (update_var (STRING #"%" (toString st2.cs_next_var))
      (n2w (LENGTH cx.txn.code)) u)` by
    simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
         venomInstTheory.mk_inst_def,venomExecSemanticsTheory.exec_read0_def] >>
  `!v wd. i+k <= LENGTH cx.txn.code /\
    v.vs_accounts = u.vs_accounts /\ v.vs_call_ctx = u.vs_call_ctx /\
    v.vs_code = u.vs_code /\
    eval_operand dst v = SOME wd /\ eval_operand start_op v = SOME (n2w i) /\
    eval_operand len_op v = SOME (n2w k) /\
    (CODECOPY = EXTCODECOPY ==> eval_operand start_op v = eval_operand start_op u) ==>
    step_inst_base (mk_inst se.cs_next_id CODECOPY [dst;start_op;len_op] []) v =
      OK (write_memory_with_expansion (w2n wd)
        (TAKE k (DROP i cx.txn.code)) v)` by
    (rpt strip_tac >>
     `TAKE k (DROP i cx.txn.code ++ REPLICATE k 0w) = TAKE k (DROP i cx.txn.code)` by
       (irule rich_listTheory.TAKE_APPEND1 >> simp[]) >>
     simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomInstTheory.mk_inst_def,venomExecSemanticsTheory.exec_write2_def,
       wordsTheory.w2n_n2w]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  rpt (qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac) >>
  (fn (asl,w) =>
    let val provider = bodyFullBuiltinSliceCodeTailTheory.slice_code_tail_full
        val args = snd (strip_comb w)
        val actual_df = fst (pairSyntax.dest_pair (hd args))
        val actual_source = el 5 args
        val formal_df = first (fn v => fst (dest_var v) = "DF") (free_vars (concl provider))
        val formal_source = first (fn v => fst (dest_var v) = "source") (free_vars (concl provider))
        val post = find_term (fn tm =>
          let val (f,xs) = strip_comb tm in
            is_const f andalso fst (dest_const f) = "vv_post" andalso length xs = 14
          end) w
        val actual_e = el 6 (snd (strip_comb post))
        val actual_args = el 3 (snd (strip_comb actual_e))
        val formal_e = first (fn v => fst (dest_var v) = "e") (free_vars (concl provider))
        val formal_args = first (fn v => fst (dest_var v) = "args") (free_vars (concl provider))
        val tys = match_type (type_of formal_df) (type_of actual_df)
        val fields = Q.INST [`sa` |-> `st2`,`s` |-> `u`,`G` |-> `G2`,`tn` |-> `tn2`,
      `start` |-> `start_op`,`cnt` |-> `len_op`,`limit` |-> `src_len`,
      `query_op` |-> `CODESIZE`,`query_ops` |-> `[]`,
      `copy_op` |-> `CODECOPY`,`copy_ops` |-> `[dst;start_op;len_op]`,
      `addr` |-> `start_op`,`data` |-> `dst`,
      `N` |-> `type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))`,
      `code` |-> `cx.txn.code`,
      `es` |-> `len_mid`,`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
      `tops` |-> `cx_tops cx`]
          (INST_TYPE tys provider)
        val typed = INST [inst tys formal_df |-> actual_df,
          inst tys formal_source |-> actual_source,inst tys formal_e |-> actual_e,
          inst tys formal_args |-> actual_args] fields
    in mp_tac typed (asl,w) end) >>
  (impl_tac >-
    (simp[MEM,vyperStateTheory.get_accounts_def,vyperStateTheory.bind_def,
      vyperStateTheory.lift_sum_def,vyperStateTheory.return_def,
      vyperStateTheory.raise_def,exprSimSliceSourceTheory.slice_bytes_nat] >>
     conj_tac
     >- (qpat_assum `!x. start_op = Var x ==> not_fresh_at st2 x` mp_tac >>
         qpat_assum `!x. len_op = Var x ==> not_fresh_at st2 x` mp_tac >>
         rpt (pop_assum kall_tac) >> metis_tac[]) >>
     Cases_on `i+k <= LENGTH
       cx.txn.code` >>
     simp[vyperStateTheory.return_def,vyperStateTheory.raise_def])) >>
  strip_tac >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  reverse conj_tac >- simp[] >>
  qx_genl_tac [`H`,`res`,`ee`,`HG`,`tm`,`target`] >> strip_tac >>
  RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `res = INL _ /\ _` strip_assume_tac >>
  qpat_assum `res = INL _` SUBST_ALL_TAC >>
  qabbrev_tac `copied = TAKE k (DROP i
    cx.txn.code)` >>
  `ee with gas_obs := [] = ee` by
    (qpat_assum `ee.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `ee = len_mid` by
    (qunabbrev_tac `copied` >>
     qpat_assum `!tail. bind get_accounts _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `k <= n` mp_tac >>
     qpat_assum `ee with gas_obs := [] = ee` mp_tac >>
     qpat_assum `len_mid with gas_obs := [] = len_mid` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `i+k <= LENGTH
       cx.txn.code` >>
     fs[vyperStateTheory.get_accounts_def,vyperStateTheory.bind_def,
        vyperStateTheory.lift_sum_def,vyperStateTheory.return_def,
        vyperStateTheory.raise_def,exprSimSliceSourceTheory.slice_bytes_nat] >>
     qpat_assum `k <= n` (fn kn =>
       full_simp_tac (srw_ss()) [kn,vyperStateTheory.return_def,vyperStateTheory.raise_def]) >>
     qpat_assum `len_mid with gas_obs := _ = ee with gas_obs := []`
       (mp_tac o Q.AP_TERM `\st:evaluation_state. st with gas_obs := []`) >> simp[]) >>
  qpat_assum `ee = len_mid` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H len_mid.storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
       (qspec_then `[]`
         (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame)) >>
     simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
       (qspec_then `[]`
         (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame)) >>
     simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
       valid_horizon _ _ H mid.storage_trace` irule >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       valid_horizon _ _ H es.storage_trace` irule >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
      expr_post H _ _ _ _ start _ _ _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
      expr_post H _ _ _ _ len _ _ _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  `sa.cs_next_var <= st1.cs_next_var /\ st1.cs_next_var <= st2.cs_next_var /\
   sa.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= st2.cs_next_id` by
    (qpat_assum `ci_mono sa st1` mp_tac >>
     qpat_assum `ci_mono st1 st2` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `vv_post H ctx func cenv cx
      (Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
        [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
          [Builtin (BaseT AddressT) (Env SelfAddr) []];start;len])
      es sa sb s0 len_mid (Value (BytesV copied))
      (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)) target` by
    ((fn (asl,w) =>
       let val provider = exprSimSliceOrdinaryContinueTheory.slice_two_operand_post_rebase
           val actual = hd (snd (strip_comb w))
           val formal = first (fn v => fst (dest_var v) = "H")
             (free_vars (concl provider))
           val tys = match_type (type_of formal) (type_of actual)
           val typed = INST [inst tys formal |-> actual] (INST_TYPE tys provider)
       in mp_tac (Q.INST [`ctx` |-> `ctx`,`func` |-> `func`,
       `cenv` |-> `cenv`,`cx` |-> `cx`,`ec` |-> `es`,`sc` |-> `sa`,`u` |-> `s0`,
       `e1` |-> `mid`,`sd` |-> `st1`,`t` |-> `t`,
       `e2` |-> `len_mid`,`se` |-> `st2`,`r` |-> `u`,
       `start` |-> `start`,`len` |-> `len`,
       `v1` |-> `IntV (&i)`,`op1` |-> `start_op`,
       `v2` |-> `IntV (&k)`,`op2` |-> `len_op`,`sf` |-> `sb`,`ef` |-> `len_mid`,
       `tv` |-> `Value (BytesV copied)`,
       `result` |-> `Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
         [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
           [Builtin (BaseT AddressT) (Env SelfAddr) []];start;len]`,
       `vv` |-> `LocatedValue (BaseT (BytesT (Dynamic n)))
         (mk_ptr out LocMemory)`,`z` |-> `target`]
       typed) (asl,w) end) >>
     (impl_tac >- simp[loweringPostsTheory.expr_has_effect_thm]) >>
     disch_then ACCEPT_TAC) >>
  `wb_frame cenv es mid sa s0 t` by
    (qpat_assum `expr_post H _ _ _ _ start _ _ _ _ _ _ _ _`
       (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame)) >>
  `wb_frame cenv mid len_mid st1 t u` by
    (qpat_assum `expr_post H _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame)) >>
  `wb_frame cenv es len_mid sa s0 u` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then Any (qspecl_then [`sa`,`mid`,`len_mid`,`st1`,`t`,`u`] mp_tac)
         exprSimWordArgsTheory.wb_frame_trans) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  `sa.cs_next_var <= st2.cs_next_var /\ sa.cs_next_id <= st2.cs_next_id` by decide_tac >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then Any (qspecl_then [`lo`,`sa`,`G0`,`tn0`,`G1`,`tn1`,
         `mid`,`st1`,`G2`,`tn2`,`t`,`mid`] mp_tac)
         wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 HG tm` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then Any (qspecl_then [`lo`,`sa`,`G0`,`tn0`,`G2`,`tn2`,
         `len_mid`,`st2`,`HG`,`tm`,`u`,`len_mid`] mp_tac)
         wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  qpat_assum `vv_post H ctx func cenv cx _ es sa sb s0 len_mid _ _ target`
    (assume_tac o REWRITE_RULE[contextTheory.mk_ptr_def]) >>
  qpat_assum `vv_store_bound cx _ _ len_mid _ _ target`
    (assume_tac o REWRITE_RULE[contextTheory.mk_ptr_def]) >>
  qpat_assum `ptr_vv_ok cx _ _ _ len_mid HG tm target`
    (assume_tac o REWRITE_RULE[contextTheory.mk_ptr_def]) >>
  simp[vyperASTTheory.expr_type_def,exprLoweringTheory.lowered_value_type_def,
       contextTheory.mk_ptr_def,contextTheory.vv_location_def]
QED

Finalise slice_builtin_some_vv_full
