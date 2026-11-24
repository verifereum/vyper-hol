Theory externalReturnValuedFull
Ancestors
  externalReturnPrefix externalReturnPackage externalReturnRawJoint
  externalReturnWordJoint loweringHalt allocationPtr
  externalEntryJoint nonreentrantExit nonreentrantEquiv
  contextCodegenRel venomInst valueEncodingDefs e2eDefs gasSummary exprSimHyps
  bodyFullAllocaFresh bodyFullAllocGeneric typedCopyAgreement representationCleanPtr
  exprPtrUnwrapFacts bytesSnapshotMemory typeLayoutProps
  reasonCopySourcePtr bodyCopyMemoryBase exprSimBufferStore valueEncodingProps
  valueCopy rawReturnValue
  bodySimFull gasOutcomeFullCompose gasOutcomeFull
  gasStorage gasExemptCert exprSimDefs bodyPtrDefs vyperStorageFootprint
  vyperStorageTrace externalReturnSiteSemantics assignRelayoutCaller
  vyperTypeSystem vyperTypeInvariants exprSimIfExpCompat exprSimSource
  externalRawReturnType externalReturnBounds wideningZeroLayout
  gasShadowCompileStmtHelpers gasShadowState stmtLoweringMono
  stmtLowering exprLoweringProps stmtSimReturn stmtSimProps exprOperandVar
  exprSimHypsDefs loweringPosts bodySim fragExec compileEnv vyperInterpreter

  typedCopyOriginPtr typedMemoryCopy exprSimCopy exprSimAggregateChildren
  exprSimTypedAlloc robustCopyTransportPtr externalReturnNormalizeMem
  exprSimAlloc exprSimOperands rawCallBufferPtr

  abiEncoderSourceRobust abiEncoderWindowJoint externalReturnPlan
  externalReturnEncoderSites fragGasPathFrameMem bodyMemAggregatePath
  externalReturnSourceWindow registeredAllocationWindow allocaSiteResource
  decoderOriginAllocationFrame[qualified,ignore_grammar]
  exprSimAbiEncodeExecFrame[qualified,ignore_grammar]
  bodyFullIntCallReturnHalt[qualified,ignore_grammar]
  fragGasEmitCtrl instMemFrontier fragGasOriginPtrLoop
  fragGasOriginPtr[qualified,ignore_grammar]
  abiEncodeMaterialize aggregateEvaluatedLayout exprSimAbiEncodeArgsPhysicalCapacity
  externalReturnSupport placeRelayoutSemantic retAbiPlanProps externalReturnBufferedMetadata

  vyperLoweringCorrect

Theorem valued_return_code_extends[local]:
  compile_external_return rv prim raw ei msz nr nkey ut iv st = ((),st') ==>
  cs_extends st st'
Proof
  strip_tac >>
  first_assum (fn eq => mp_tac
    (PART_MATCH (rand o rand) (cj 3 ci_mono_return_helpers) (lhs (concl eq)))) >>
  simp[ci_mono_def]
QED

Theorem valued_return_result_unlock[local]:
  state_rel H func ce cx mid t /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  (nr ==> is_view_mut mut = (mut = View)) /\
  (nr /\ mut <> View ==> cx.nonreentrant_slot = SOME nkey) /\
  ss.vs_accounts = t.vs_accounts /\
  ss.vs_transient =
    (if nr /\ mut <> View then (tstore (n2w nkey) 0w t).vs_transient
     else t.vs_transient) /\
  ss.vs_logs = t.vs_logs /\ ss.vs_requests = t.vs_requests /\
  ss.vs_pending_deletions = t.vs_pending_deletions /\
  (if lookup_raw_return_or_F (NONE:num option) tx.function_name External tops
   then raw_return_bytes v = SOME ss.vs_returndata
   else return_bytes tops ret v ss.vs_returndata) ==>
  ?us. unlock_if_nr cx nr (is_view_mut mut)
    (mid with <|scopes := []; gas_obs := tail|>) = (INL (),us) /\
    external_call_result_rel H tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state am.sources am.exports am.layouts us),
       us.requests) (Halt ss)
Proof
  strip_tac >>
  qabbrev_tac `ee = mid with <|scopes := []; gas_obs := tail|>` >>
  `state_rel H func ce cx ee t` by
    (simp[Abbr `ee`] >> metis_tac[state_rel_scopes_nil,loweringStateRelDefsTheory.state_rel_gas_obs]) >>
  `unlock_if_nr cx nr (is_view_mut mut) =
    (if nr /\ mut <> View then release_nonreentrant_lock cx.txn.target nkey
     else vyperState$return ())` by
    (Cases_on `nr` >> Cases_on `mut = View` >>
     gvs[unlock_if_nr_def]) >>
  `?us. (if nr /\ mut <> View then release_nonreentrant_lock cx.txn.target nkey
          else vyperState$return ()) ee = (INL (),us)` by
    (Cases_on `nr /\ mut <> View` >>
     simp[nonreentrantEquivTheory.release_nonreentrant_lock_execution,
       vyperStateTheory.return_def]) >>
  pop_assum strip_assume_tac >>
  qexists_tac `us` >> conj_tac
  >- (qpat_assum `unlock_if_nr _ _ _ = _`
        (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
      first_assum ACCEPT_TAC) >>
  qspecl_then [`H`,`func`,`ce`,`cx`,`ee`,`us`,`t`,`ss`,`nr`,`nkey`,
    `mut = View`,`tops`,`tx`,`am.sources`,`am.exports`,`am.layouts`]
    mp_tac external_halt_success_unlock >>
  impl_tac >- (fs[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[external_call_result_rel_def]
QED

Theorem return_selected_valued_frag_full_core[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops ut nkey_map
      (mut,nr,rr,tx.function_name,args,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut,iv,fbody,rt) /\
  cenv with ce_vars := cenv0.ce_vars = cenv0 /\
  same_frame cenv ce /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  get_tenv cx = type_env tops /\
  (nr ==> is_view_mut mut = (mut = View)) /\
  (nr /\ mut <> View ==> ut /\ ~cx.txn.is_static /\
    cx.nonreentrant_slot = SOME nkey /\ nkey < dimword (:256)) /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (!ty. expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
          ce cx ty e es /\
        expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
          ce cx ty e es) /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\
  cx.txn.target = tx.target ==>
  stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cx lctx
    (\H v ee gt r. ?tv v' us. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),us) /\
      external_call_result_rel H tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts us),
         us.requests) r)
    ce (stmt_env ce lctx ret (Return (SOME e)))
    (stmt_env (gas_shadow_env T ce) lctx ret (Return (SOME (gas_shadow_expr e))))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >>
  drule return_package_target_inversion >> strip_tac >>
  drule return_package_metadata >> strip_tac >>
  qpat_assum `cenv with ce_vars := _ = cenv0`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_env_component_equality]) >>
  drule return_same_frame_metadata >> strip_tac >>
  `ce.ce_raw_return = rr /\
   ce.ce_struct_fields = make_struct_fields_map tops /\
   ce.ce_type_env = type_env tops /\
   ce.ce_nonreentrant = (nr,nkey,ut,mut = View) /\
   ce.ce_is_external /\ ~ce.ce_is_ctor /\
   ce.ce_return_pc = NONE /\ ce.ce_target = target` by simp[] >>
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `lower_value compile_expr ce ret e sa` >>
  rename1 `lower_value compile_expr ce ret e sa = (op,sm)` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T ce) ret
              (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value compile_expr _ ret (gas_shadow_expr e) shadow_sa =
             (shadow_op,shadow_sm)` >>
  `op = shadow_op /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (lower_value compile_expr ce ret e)
        (lower_value compile_expr (gas_shadow_env T ce) ret (gas_shadow_expr e))`
       by irule gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sa`, `shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  qpat_x_assum `op = shadow_op` (SUBST_ALL_TAC o SYM) >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    metis_tac[return_value_code_prefix] >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    (conj_tac
     >- (qspecl_then [`ce`, `ret`, `e`, `sa`] mp_tac
           (cj 2 ci_mono_compile_expr_sa) >> simp[ci_mono_def]) >>
     qspecl_then [`gas_shadow_env T ce`, `ret`, `gas_shadow_expr e`, `shadow_sa`]
       mp_tac (cj 2 ci_mono_compile_expr_sa) >> simp[ci_mono_def]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[return_forced_admissible] >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by simp[] >>
  qpat_x_assum `!ty. _` (qspec_then `ret` strip_assume_tac) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                           `op`, `s0`, `G0`, `tn0`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `eval_stmt cx (Return (SOME e)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_raise]
  >~ [`gas_marked_exec`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >> metis_tac[])
  >~ [`gas_exempt_cert _ _ _ (bind _ _)`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res mid G1 tn1 t. ?v. res = INL v /\
     expr_post H ctx func ce cx e es sa sm s0 mid v op t /\
     expr_store_bound cx (post_value_type ce e) v op t /\
     s0.vs_alloca_next <= t.vs_alloca_next /\
     ghost_inv_at (DF H) lo d ce cx mid G1 tn1 t /\
     ptr_val_ok cx (post_value_type ce e) v op G1 tn1 t /\
     (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G1 t) /\
     alloca_history func t /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> fs[] >>
      Cases_on `res`
      >- (qpat_assum `expr_exit (INL _) _` mp_tac >>
          simp_tac bool_ss [expr_exit_INL]) >>
      fs[stmt_exit_ptr_def, halt_exit_def,
         GSYM (Q.INST_TYPE [`:'a` |-> `:value`] expr_exit_INR_type)] >>
      rpt strip_tac >> gvs[] >>
      rename1 `expr_exit (INR exc) (IntRet _ _)` >>
      qpat_assum `expr_exit (INR exc) (IntRet _ _)` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      Cases_on `exc` >> simp[expr_exit_def] >>
      rename1 `expr_exit (INR (Error err)) (IntRet _ _)` >>
      Cases_on `err` >> simp[expr_exit_def]) >>
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  first_assum (drule_then strip_assume_tac) >>
  pop_assum (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  suspend "joint_return_suffix"
QED

Resume return_selected_valued_frag_full_core[joint_return_suffix]:
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o PURE_REWRITE_RULE [listTheory.APPEND_NIL])) >>
  `expr_sim_inv ce cx env
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  qpat_assum `bind _ _ (es with gas_obs := _) = _`
    (mp_then Any mp_tac
      (CONV_RULE (DEPTH_CONV ETA_CONV) return_site_value_semantics)) >>
  disch_then (qspecl_then [`ret`,`env`,`ce`] mp_tac) >>
  simp[] >> strip_tac >>
  `well_typed_expr env e` by
    (qpat_assum `IS_SOME (type_stmt env ret (Return (SOME e)))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[type_stmt_def, AllCaseEqs()]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e)` by
    metis_tac[post_value_type_widens] >>
  `type_widens_to (get_tenv cx) (post_value_type ce e) ret` by
    metis_tac[assignRelayoutCallerTheory.type_widens_to_trans] >>
  `?ptv. evaluate_type (type_env tops) (post_value_type ce e) = SOME ptv /\
         value_has_type ptv v` by
    (Cases_on `post_value_type ce e = expr_type e`
     >- metis_tac[] >>
     `?ann fid args drv. e = Call ann (IntCall fid) args drv` by
       metis_tac[post_value_type_not_int_call] >>
     gvs[] >>
     `~is_word_type ann /\ ~is_bytestring_type ann` by
       (CCONTR_TAC >> gvs[post_value_type_def, vyperASTTheory.expr_type_def]) >>
     qpat_assum `bind _ _ (es with gas_obs := _) = _`
       (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV) return_intcall_physical_typed)) >>
     disch_then (qspecl_then [`env`,`ce`] mp_tac) >>
     simp[post_value_type_def]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `evaluate_type _ (expr_type e) = SOME atv` kall_tac >>
  qpat_x_assum `value_has_type atv v` kall_tac >>
  Cases_on `ce.ce_raw_return`
  >- (`lookup_raw_return_or_F (NONE:num option) tx.function_name External tops`
        by fs[] >>
      drule_all source_typing_raw_return_type >> strip_tac >>
      suspend "raw_typed_copy") >>
  Cases_on `is_word_type ret`
  >- suspend "word_terminal" >>
  suspend "buffered_return"
QED

Resume return_selected_valued_frag_full_core[buffered_return]:
  qpat_assum `expr_post _ ctx func ce cx e es sa sm s0 mid v op t`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_assum `ghost_inv_at _ lo d ce cx mid G1 tn1 t`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  suspend "buffered_physical_type"
QED

Resume return_selected_valued_frag_full_core[buffered_physical_type]:
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_sim_inv_physical_type] >>
  `arg_type_fits (expr_type e) ret` by
    (qpat_assum `type_widens_to (type_env tops) (expr_type e) ret` mp_tac >>
     PURE_REWRITE_TAC [type_widens_to_def] >>
     disch_then (DISJ_CASES_THEN2 SUBST1_TAC strip_assume_tac)
     >- MATCH_ACCEPT_TAC (cj 1 vyperTypeSystemTheory.arg_type_fits_refl) >>
     first_assum ACCEPT_TAC) >>
  qabbrev_tac `physical_ty = lowered_value_type ce e` >>
  `arg_type_fits physical_ty ret` by
    (qspecl_then [`physical_ty`,`expr_type e`] mp_tac
       (cj 1 assignRelayoutCallerTheory.arg_type_fits_trans) >>
     simp[] >> disch_then (qspec_then `ret` ACCEPT_TAC)) >>
  `~is_word_type (expr_type e) /\ ~is_word_type physical_ty` by
    (qspecl_then [`expr_type e`,`ret`] mp_tac arg_type_fits_word_type >>
     qspecl_then [`physical_ty`,`ret`] mp_tac arg_type_fits_word_type >> simp[]) >>
  Q.SUBGOAL_THEN `post_value_type ce e = physical_ty \/
    is_bytestring_type (post_value_type ce e) /\ is_bytestring_type physical_ty` ASSUME_TAC
  >- (qspecl_then [`ce`,`e`] mp_tac materialize_post_lowered_classify >> simp[]) >>
  `alloc_limits_expr ce e` by
    (qpat_assum `stmt_exprs_ok ce (Return (SOME e))`
       (ACCEPT_TAC o cj 2 o REWRITE_RULE [stmt_exprs_ok_def,
          allocLimitsTheory.alloc_limits_stmt_def, allocLimitsTheory.alloc_limits_expr_def])) >>
  `value_runtime_typed env physical_ty v` by
    (simp[Abbr `physical_ty`] >>
     qspecl_then [`ce`,`e`,`env`,`cx`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,`v`,
       `mid with gas_obs := []`] mp_tac
       expr_sim_inv_read_lowered_typed >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  qpat_x_assum `value_runtime_typed env physical_ty v` mp_tac >>
  PURE_REWRITE_TAC [vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  disch_then (qx_choose_then `physical_tv` strip_assume_tac) >>
  `evaluate_type (get_tenv cx) physical_ty = SOME physical_tv /\
   evaluate_type (type_env tops) physical_ty = SOME physical_tv /\
   val_wf physical_tv v /\ safe_cast physical_tv v = SOME v` by
    (imp_res_tac valueTypingMemoryPropsTheory.value_has_type_memory_wf >>
     imp_res_tac vyperTypingTheory.safe_cast_well_typed >>
     qpat_assum `get_tenv cx = type_env tops`
       (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
     qpat_assum `env.type_defs = get_tenv cx`
       (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `needs_external_call_wrap physical_ty = needs_external_call_wrap ret /\
   vyper_to_abi_type (type_env tops) physical_ty = vyper_to_abi_type (type_env tops) ret /\
   vyper_to_abi (type_env tops) physical_ty v = vyper_to_abi (type_env tops) ret v` by
    (conj_tac >- (irule return_wrap_fits >> first_assum ACCEPT_TAC) >>
     conj_tac >- (irule (cj 1 abi_args_fits_abi_type) >> first_assum ACCEPT_TAC) >>
     qspecl_then [`physical_ty`,`ret`,`physical_tv`,`dtv`] mp_tac
       (Q.INST [`tenv` |-> `type_env tops`] (cj 1 abi_args_fits_conversion)) >>
     simp[] >> disch_then (qspec_then `v` ACCEPT_TAC)) >>
  suspend "buffered_metadata"
QED

Resume return_selected_valued_frag_full_core[buffered_metadata]:
  `ret <> NoneT` by
    (qpat_assum `IS_SOME (type_stmt env ret (Return (SOME e)))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[type_stmt_def, AllCaseEqs()]) >>
  qabbrev_tac `abi_ce = if physical_ty = ret then ce else update_cenv_ret_abi ce physical_ty` >>
  `ce.ce_max_return_size = (update_cenv_ret_abi ce ret).ce_max_return_size` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ce.ce_max_return_size = cenv.ce_max_return_size`,
        `cenv.ce_max_return_size = cenv0.ce_max_return_size`,
        `_.ce_max_return_size = if ret = NoneT then 0 else _`,
        `cenv0 = _ with ce_target := target`,
        `ce.ce_struct_fields = make_struct_fields_map tops`, `ret <> NoneT`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt disch_tac >>
     gvs[compileVyperTheory.update_cenv_ret_abi_def,
         compileVyperTheory.build_compile_env_ce_struct_fields]) >>
  `abi_ce.ce_max_return_size <= ce.ce_max_return_size` by
    (Cases_on `physical_ty = ret` >> simp[Abbr `abi_ce`] >>
     metis_tac[return_abi_size_fits]) >>
  `ce.ce_max_return_size < dimword (:256)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`stmt_exprs_ok ce (Return (SOME e))`,`ce.ce_is_external`,
        `~ce.ce_raw_return`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[stmt_exprs_ok_def, compileVyperTheory.stmt_valued_return_def,
          compileVyperTheory.return_buffer_ok_def, wordsTheory.dimword_def] >>
     rpt strip_tac >> gvs[]) >>
  `abi_ce.ce_max_return_size < dimword (:256)` by decide_tac >>
  suspend "buffered_encode"
QED

Resume return_selected_valued_frag_full_core[buffered_encode]:
  Q.SUBGOAL_THEN `!src_st src_state Gs ts (src:operand) own_start own_end.
   compile_external_return (SOME src) F F abi_ce.ce_ret_enc_info
     abi_ce.ce_max_return_size nr nkey ut (mut=View) src_st = ((),sb) /\
   fn_has_code src_st sb func /\ local_ptrs_reserved ce src_st /\
   (!x. src=Var x ==> not_fresh_at src_st x) /\
   own_end.cs_next_id <= src_st.cs_next_id /\
   stmt_state_rel (storage_trace_horizon mid.storage_trace)
     ctx func ce cx mid src_state /\
   expr_val_at ce cx physical_ty own_start own_end mid v src src_state /\
   ptr_val_ok cx physical_ty v src Gs ts src_state /\
   ~src_state.vs_halted /\
   src_state.vs_current_bb=src_st.cs_current_bb /\
   src_state.vs_inst_idx=LENGTH src_st.cs_current_insts /\
   allocas_from lo src_state /\ lo<=src_state.vs_alloca_next /\
   src_state.vs_accounts=t.vs_accounts /\
   src_state.vs_transient=t.vs_transient /\
   src_state.vs_immutables=t.vs_immutables /\
   src_state.vs_logs=t.vs_logs /\
   src_state.vs_requests=t.vs_requests /\
   src_state.vs_pending_deletions=t.vs_pending_deletions /\
   src_state.vs_call_ctx=t.vs_call_ctx /\
   (!D. stor_taint_ok_at D ts src_state <=> stor_taint_ok_at D tn1 t) /\
   (!D. stor_taint_ok_at D tn1 t ==>
      gas_origin_ptr_path
        (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK src_state,Gs,ts)) ==>
   ?ss Gf tf av.
     vyper_to_abi (type_env tops) ret v=SOME av /\
     ss.vs_returndata =
       (if needs_external_call_wrap ret /\
           is_dynamic (vyper_to_abi_type (type_env tops) ret)
        then contractABI$enc
          (Tuple [vyper_to_abi_type (type_env tops) ret])
          (contractABI$ListV [av])
        else contractABI$enc (vyper_to_abi_type (type_env tops) ret) av) /\
     ss.vs_accounts=t.vs_accounts /\
     ss.vs_transient=
       (if nr /\ mut <> View then (tstore (n2w nkey) 0w t).vs_transient
        else t.vs_transient) /\
     ss.vs_immutables=t.vs_immutables /\
     ss.vs_logs=t.vs_logs /\ ss.vs_requests=t.vs_requests /\
     ss.vs_pending_deletions=t.vs_pending_deletions /\
     ss.vs_call_ctx=t.vs_call_ctx /\
     (!H. stor_taint_ok_at (DF H) tn1 t ==>
       gas_origin_ptr_path
         (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (t,G1,tn1) [] (Halt ss,Gf,tf))` ASSUME_TAC
  >- (rpt gen_tac >> strip_tac >> suspend "buffered_shared_entry") >>
  (fn g =>
    qpat_assum `!src_st src_state Gs ts src own_start own_end. _`
      (fn shared =>
        let
          val (witnesses,packet) = strip_exists
            (snd (dest_imp (snd (strip_forall (concl shared)))))
          val outputs = ListPair.map
            (fn (name,v) => mk_var (name,type_of v))
            (["buffered_ss","buffered_Gf","buffered_tf","buffered_av"],witnesses)
          val replacements = ListPair.map
            (fn (v,w) => {redex=v,residue=w}) (witnesses,outputs)
        in
          SUBGOAL_THEN (list_mk_forall (outputs,
            mk_imp (subst replacements packet,snd g))) ASSUME_TAC
        end) g)
  >- (rpt gen_tac >> strip_tac >> suspend "buffered_finish") >>
  `(!x. op = Var x ==> not_fresh_at sm x)` by
    metis_tac[compile_lower_value_var] >>
  `fn_has_code sm sb func` by metis_tac[fn_has_code_split] >>
  `compile_external_return (SOME op) F F abi_ce.ce_ret_enc_info
    abi_ce.ce_max_return_size nr nkey ut (mut = View) sm = ((),sb)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`stmt_env ce lctx ret (Return (SOME e)) sa = _`,
        `lower_value compile_expr ce ret e sa = (op,sm)`,
        `Abbrev (physical_ty = _)`, `Abbrev (abi_ce = _)`,
        `arg_type_fits physical_ty ret`, `~ce.ce_raw_return`,
        `~is_word_type ret`, `ce.ce_nonreentrant = _`,
        `ce.ce_return_pc = NONE`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `compile_external_return (SOME op) F F abi_ce.ce_ret_enc_info
       abi_ce.ce_max_return_size nr nkey ut (mut = View) sm` >>
     Cases_on `physical_ty = ret` >>
     fs[stmt_env_def,declare_stmt_local_def,Once compile_stmt_def,
        comp_bind_def,comp_ignore_bind_def,comp_return_def,LET_THM,
        pairTheory.UNCURRY, return_source_abi_fields, markerTheory.Abbrev_def] >>
     gvs[comp_bind_def,comp_return_def,return_source_abi_fields,oneTheory.one]) >>
  suspend "buffered_direct_dispatch"
QED

Resume return_selected_valued_frag_full_core[buffered_direct_dispatch]:
  Q.SUBGOAL_THEN `expr_val_at ce cx physical_ty sa sm mid v op t /\
    ptr_val_ok cx physical_ty v op G1 tn1 t` ASSUME_TAC
  >- (Cases_on `post_value_type ce e=physical_ty`
      >- (qpat_assum `post_value_type ce e=physical_ty`
            (fn th => PURE_REWRITE_TAC [GSYM th]) >>
          conj_tac >> first_assum ACCEPT_TAC) >>
      suspend "buffered_direct_widened_source") >>
  suspend "buffered_direct_ret_ready"
QED

Resume return_selected_valued_frag_full_core[buffered_direct_ret_ready]:
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspecl_then [`ce`,`ret`,`e`,`sa`] mp_tac
      (cj 2 ci_mono_compile_expr_sa) >> simp[ci_mono_def]) >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!D. stor_taint_ok_at D tn1 t ==>
    gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK t,G1,tn1)` by
    (rpt strip_tac >> irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `!src_st src_state Gs ts src own_start own_end. _`
    (qspecl_then [`sm`,`t`,`G1`,`tn1`,`op`,`sa`,`sm`] mp_tac) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >>
  disch_then (qx_choose_then `buffered_ss` (qx_choose_then `buffered_Gf`
    (qx_choose_then `buffered_tf` (qx_choose_then `buffered_av` strip_assume_tac)))) >>
  qpat_assum `!buffered_ss buffered_Gf buffered_tf buffered_av. _`
    (qspecl_then [`buffered_ss`,`buffered_Gf`,`buffered_tf`,`buffered_av`]
      MATCH_MP_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume return_selected_valued_frag_full_core[buffered_direct_widened_source]:
  `is_bytestring_type (post_value_type ce e) /\ is_bytestring_type physical_ty` by metis_tac[] >>
  `evaluate_type (get_tenv cx) (post_value_type ce e)=SOME ptv /\
   evaluate_type (get_tenv cx) physical_ty=SOME physical_tv` by
    (qpat_assum `get_tenv cx=type_env tops`
       (fn th => PURE_REWRITE_TAC [th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `val_footprint ptv v=val_footprint physical_tv v` by
    (qspecl_then [`get_tenv cx`,`post_value_type ce e`,`physical_ty`,
      `ptv`,`physical_tv`,`v`] mp_tac valueCopyBytesTheory.bytestring_val_footprint_eq >>
     simp[]) >>
  `val_store_size ptv v=val_store_size physical_tv v` by
    (qspecl_then [`get_tenv cx`,`post_value_type ce e`,`physical_ty`,
      `ptv`,`physical_tv`,`v`] mp_tac valueCopyBytesTheory.bytestring_val_store_size_eq >>
     simp[]) >>
  `!addr mem. val_in_memory ptv v addr mem ==> val_in_memory physical_tv v addr mem` by
    (rpt strip_tac >>
     qspecl_then [`get_tenv cx`,`post_value_type ce e`,`physical_ty`,
       `ptv`,`physical_tv`,`v`,`addr`,`mem`] mp_tac
       valueCopyBytesTheory.bytestring_val_in_memory_transfer >> simp[]) >>
  `val_wf ptv v` by
    (qpat_assum `value_has_type ptv v`
       (ACCEPT_TAC o MATCH_MP valueTypingMemoryPropsTheory.value_has_type_memory_wf)) >>
  `?sbt. ptv = BaseTV sbt` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`is_bytestring_type (post_value_type ce e)`,
        `evaluate_type (get_tenv cx) (post_value_type ce e)=SOME ptv`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule_all valueCopyBytesTheory.bytestring_type_value >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `?dbt. physical_tv = BaseTV dbt` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`is_bytestring_type physical_ty`,`evaluate_type (get_tenv cx) physical_ty=SOME physical_tv`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule_all valueCopyBytesTheory.bytestring_type_value >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `!name offset. local_val_at ce cx name offset ptv v ==>
     local_val_at ce cx name offset physical_tv v` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ptv = BaseTV sbt`,`physical_tv = BaseTV dbt`,`val_wf ptv v`,
        `val_footprint ptv v = val_footprint physical_tv v`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     metis_tac[exprSimPropsTheory.local_val_at_base,
       arithmeticTheory.LESS_EQ_REFL]) >>
  `expr_val_at ce cx physical_ty sa sm mid v op t` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`expr_val_at ce cx (post_value_type ce e) sa sm mid v op t`,
       `evaluate_type (get_tenv cx) (post_value_type ce e)=SOME ptv`,
       `evaluate_type (get_tenv cx) physical_ty=SOME physical_tv`,
       `~is_word_type (post_value_type ce e)`,`~is_word_type physical_ty`,
       `val_wf physical_tv v`,`val_footprint ptv v=val_footprint physical_tv v`,
       `!name offset. local_val_at ce cx name offset ptv v ==> _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [expr_val_at_def] >>
     rpt disch_tac >> gen_tac >> strip_tac >>
     `tv = physical_tv` by metis_tac[optionTheory.SOME_11] >>
     pop_assum SUBST_ALL_TAC >> conj_tac
     >- first_assum ACCEPT_TAC >>
     qpat_assum `!tv. SOME ptv = SOME tv ==> _`
       (qspec_then `ptv` mp_tac) >>
     impl_tac >- simp[] >>
     disch_then (CONJUNCTS_THEN2 ASSUME_TAC
       (qx_choose_then `source_w` strip_assume_tac)) >>
     qexists_tac `source_w` >> (conj_tac >- first_assum ACCEPT_TAC)
     >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> gvs[] >>
         first_assum ACCEPT_TAC)
     >- (disj2_tac >> disj1_tac >> qexistsl_tac [`n`,`b`,`sz`] >> gvs[] >>
         first_assum MATCH_MP_TAC >> first_assum ACCEPT_TAC) >>
     disj2_tac >> disj2_tac >> gvs[]) >>
  `ptr_val_ok cx physical_ty v op G1 tn1 t` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`ptr_val_ok cx (post_value_type ce e) v op G1 tn1 t`,
       `evaluate_type (get_tenv cx) (post_value_type ce e)=SOME ptv`,
       `evaluate_type (get_tenv cx) physical_ty=SOME physical_tv`,
       `~is_word_type (post_value_type ce e)`,`~is_word_type physical_ty`,
       `val_footprint ptv v=val_footprint physical_tv v`,
       `val_store_size ptv v=val_store_size physical_tv v`,
       `!addr mem. val_in_memory ptv v addr mem ==> val_in_memory physical_tv v addr mem`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ptr_val_ok_def,ptr_mem_ok_def] >>
     rpt disch_tac >> metis_tac[optionTheory.SOME_11]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume return_selected_valued_frag_full_core[buffered_finish]:
  rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (ReturnException v)`,`mid`,`Halt buffered_ss`,
    `buffered_Gf`,`buffered_tf`] >>
  conj_tac >- simp[vyperStateTheory.raise_def,gas_explicit_def] >>
  conj_tac
  >- (qpat_assum `cx = initial_evaluation_context am.sources am.layouts tx NONE`
        (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `cx = initial_evaluation_context am.sources am.layouts tx NONE`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
      (strip_assume_tac o BETA_RULE o MATCH_MP th)) >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (t,G1,tn1) [] (Halt buffered_ss,buffered_Gf,buffered_tf)` by
    (first_assum (qspec_then `H` MATCH_MP_TAC) >>
     metis_tac[ghost_inv_at_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[fragExecTheory.exit_result_def,stmt_exit_ptr_def,expr_exit_def,halt_exit_def] >>
  reverse conj_tac >-
    (qpat_assum `gas_origin_ptr_path _ _ _ (Halt _,_,_)`
       (ACCEPT_TAC o MATCH_MP bodyFullIntCallReturnHaltTheory.gas_origin_ptr_path_halt_fmp)) >>
  qx_gen_tac `tail` >> suspend "buffered_post"
QED

Resume return_selected_valued_frag_full_core[buffered_post]:
  `state_rel H func ce cx mid t` by
    (qpat_assum `expr_post H ctx func ce cx e es sa sm s0 mid _ op t`
      (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [stmt_state_rel_def] o
       CONJUNCT1 o REWRITE_RULE [expr_post_def])) >>
  `~lookup_raw_return_or_F (NONE:num option) tx.function_name External tops` by
    (qpat_assum `ce.ce_raw_return = lookup_raw_return_or_F
       (NONE:num option) tx.function_name External tops`
       (fn th => qpat_assum `~ce.ce_raw_return`
         (ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
  qspecl_then [`tops`,`ret`,`v`,
    `if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then contractABI$ListV [buffered_av] else buffered_av`] mp_tac
    vyperLoweringCorrectTheory.chosen_return_abi_bytes >>
  impl_tac
  >- (IF_CASES_TAC >> simp[vyperABITheory.vyper_to_abi_def]) >> strip_tac >>
  `return_bytes tops ret v buffered_ss.vs_returndata` by
    (qpat_assum `return_bytes tops ret v (contractABI$enc _ _)` mp_tac >>
     qpat_assum `buffered_ss.vs_returndata = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `needs_external_call_wrap ret /\
       is_dynamic (vyper_to_abi_type (type_env tops) ret)` >>
     gvs[vyperABITheory.vyper_to_abi_type_def]) >>
  `?us. unlock_if_nr cx nr (is_view_mut mut)
    (mid with <|scopes := []; gas_obs := tail|>) = (INL (),us) /\
    external_call_result_rel H tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state am.sources am.exports am.layouts us),
       us.requests) (Halt buffered_ss)` by
    (match_mp_tac (Q.INST
       [`func` |-> `func`, `ce` |-> `ce`, `nkey` |-> `nkey`,
        `t` |-> `t`] valued_return_result_unlock) >> simp[]) >>
  pop_assum strip_assume_tac >>
  qexists_tac `us` >> conj_tac
  >- (qpat_assum `nr /\ mut <> View ==> _` mp_tac >>
      qpat_assum `unlock_if_nr cx nr (is_view_mut mut) _ = (INL (),us)` mp_tac >>
      qpat_assum `cx.txn.target = tx.target` (fn target =>
        qpat_assum `nkey = nkey_map tx.function_name` (fn key =>
          simp[NoAsms, unlock_if_nr_def, vyperInterpreterTheory.is_view_mut_def,
               target, key])) >>
      Cases_on `nr` >> Cases_on `mut` >> simp[]) >>
  qpat_assum `INL v = INL v'` (fn value =>
    qpat_assum `external_call_result_rel H tops ret tx (INL v,_,_) (Halt buffered_ss)`
      (mp_tac o REWRITE_RULE [value])) >>
  simp[NoAsms]
QED

Resume return_selected_valued_frag_full_core[buffered_shared_entry]:
  `alloca_history func src_state` by suspend "buffered_shared_history" >>
  `compile_external_return (SOME src) F F abi_ce.ce_ret_enc_info
      abi_ce.ce_max_return_size nr nkey T (mut = View) src_st = ((),sb)` by
    (`nr /\ ~(mut = View) ==> ut` by simp[] >>
     pop_assum (ONCE_REWRITE_TAC o single o GSYM o
       MATCH_MP valued_return_compiler_transient) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `compile_external_return _ F F _ _ nr _ T _ src_st = _`
    (strip_assume_tac o MATCH_MP (SPEC_ALL compile_external_return_unlock)) >>
  rename1 `compile_external_return _ F F _ _ F _ T _ unlock_st = _` >>
  `cs_extends src_st unlock_st /\ unlock_st.cs_next_var = src_st.cs_next_var /\
    src_st.cs_next_id <= unlock_st.cs_next_id` by
    (mp_tac (Q.INST [`st` |-> `src_st`,`st'` |-> `unlock_st`,`ut` |-> `T`,
       `iv` |-> `mut = View`] (SPEC_ALL optional_unlock_code)) >>
     impl_tac >- asm_rewrite_tac[] >>
     Cases_on `nr /\ mut <> View` >> ASM_REWRITE_TAC[] >>
     disch_then SUBST1_TAC >> simp[cs_extends_refl] >>
     irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends unlock_st sb` by
    (qpat_assum `compile_external_return _ _ _ _ _ F _ T _ unlock_st = _`
       (ACCEPT_TAC o MATCH_MP valued_return_code_extends)) >>
  `fn_has_code src_st unlock_st func /\ fn_has_code unlock_st sb func` by
    (match_mp_tac (Q.SPECL [`src_st`,`unlock_st`,`sb`,`func`] fn_has_code_split) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `nr /\ mut <> View ==> ~src_state.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def,loweringStateRelDefsTheory.state_rel_def,loweringStateRelDefsTheory.call_ctx_rel_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp src_state` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx mid src_state`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  mp_tac (Q.INST [`iv` |-> `mut = View`,`st` |-> `src_st`,`st'` |-> `unlock_st`,
      `s` |-> `src_state`,`G` |-> `Gs`,`tn` |-> `ts`]
    (SPEC_ALL optional_transient_unlock_paths_joint)) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`unlocked`,`unlock_tn`] strip_assume_tac) >>
  `?prepared_es. unlock_if_nr cx nr (is_view_mut mut) mid = (INL (),prepared_es)` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `nr /\ ~is_view_mut mut`
     >- (Cases_on `cx.nonreentrant_slot` >>
         simp[unlock_if_nr_def,vyperStateTheory.return_def,
              nonreentrantEquivTheory.release_nonreentrant_lock_execution]) >>
     simp[unlock_if_nr_def,vyperStateTheory.return_def]) >>
  pop_assum strip_assume_tac >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace)
     ctx func ce cx prepared_es unlocked` by
    (match_mp_tac (Q.INST [`es` |-> `mid`, `s` |-> `src_state`,
       `iv` |-> `is_view_mut mut`, `n` |-> `LENGTH unlock_st.cs_current_insts`]
       (SPEC_ALL optional_transient_unlock_stmt_state_rel)) >>
     simp[] >> Cases_on `nr` >> simp[] >>
     Cases_on `mut = Pure` >> fs[]) >>
  suspend "buffered_unlock_resources"
QED

Resume return_selected_valued_frag_full_core[buffered_unlock_resources]:
  `prepared_es.scopes = mid.scopes /\ unlocked.vs_vars = src_state.vs_vars /\
    unlocked.vs_accounts = src_state.vs_accounts /\
    unlocked.vs_transient =
      (if nr /\ mut <> View then (tstore (n2w nkey) 0w t).vs_transient
       else t.vs_transient) /\
    unlocked.vs_immutables = src_state.vs_immutables /\
    unlocked.vs_logs = src_state.vs_logs /\
    unlocked.vs_requests = src_state.vs_requests /\
    unlocked.vs_pending_deletions = src_state.vs_pending_deletions /\
    unlocked.vs_call_ctx = src_state.vs_call_ctx` by
    (conj_tac
     >- (qpat_assum `unlock_if_nr cx _ _ mid = _`
           (ACCEPT_TAC o MATCH_MP vyperLocalAccessFrameTheory.unlock_if_nr_scopes)) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`unlocked = _`, `src_state.vs_transient = t.vs_transient`,
        `src_state.vs_call_ctx = t.vs_call_ctx`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qpat_assum `unlocked = _` SUBST1_TAC >>
     Cases_on `nr /\ mut <> View` >> simp[venomStateTheory.tstore_def]) >>
  `expr_val_at ce cx physical_ty own_start own_end prepared_es v src unlocked /\
    ptr_val_ok cx physical_ty v src Gs unlock_tn unlocked` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`expr_val_at ce cx physical_ty own_start own_end mid v src src_state`,
        `ptr_val_ok cx physical_ty v src Gs ts src_state`,
        `prepared_es.scopes = mid.scopes`, `unlocked.vs_vars = src_state.vs_vars`,
        `unlocked.vs_allocas = src_state.vs_allocas`,
        `unlocked.vs_memory = src_state.vs_memory`, `unlock_tn.t_mem = ts.t_mem`,
        `!op. eval_operand op unlocked = eval_operand op src_state`,
        `!op. op_taint unlock_tn op = op_taint ts op`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 7 strip_tac >>
     simp[expr_val_at_def, ptr_val_ok_def, ptr_mem_ok_def,
          loweringStateRelDefsTheory.local_region_def, venomStateTheory.lookup_var_def] >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved ce unlock_st /\
    (!x. src=Var x ==> not_fresh_at unlock_st x) /\
    own_end.cs_next_id <= unlock_st.cs_next_id /\
    allocas_from lo unlocked /\ lo <= unlocked.vs_alloca_next` by
    (conj_tac
     >- (match_mp_tac (Q.SPECL [`ce`,`src_st`,`unlock_st`]
           local_ptrs_reserved_next_var) >> simp[]) >>
     conj_tac
     >- (gen_tac >> strip_tac >>
         irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `src_st` >>
         simp[]) >>
     conj_tac
     >- (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `src_st.cs_next_id` >> simp[]) >>
     conj_tac
     >- (qpat_assum `unlocked.vs_allocas = src_state.vs_allocas`
           (fn eq => simp_tac bool_ss [ptrDisciplineTheory.allocas_from_def,eq]) >>
         qpat_assum `allocas_from lo src_state`
           (ACCEPT_TAC o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def])) >>
     simp[]) >>
  `alloca_history func unlocked` by
    (match_mp_tac (Q.INST [`ctx` |-> `ctx`,`s` |-> `src_state`]
       (SPEC_ALL fragGasPathFrameMemTheory.gas_path_mem_zero_history)) >>
     simp[] >> rpt strip_tac >>
     drule bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >>
     fs[stmt_state_rel_def]) >>
  `!H. stor_taint_ok_at (DF H) tn1 t ==> stor_taint_ok_at (DF H) unlock_tn unlocked` by
    (gen_tac >> strip_tac >>
     irule optional_transient_unlock_stor_taint >> metis_tac[]) >>
  qpat_assum `compile_external_return _ F F _ _ F _ T _ unlock_st = _`
    (mp_tac o MATCH_MP
      (REWRITE_RULE [] (Q.INST [`nr` |-> `F`]
        (SPEC_ALL compile_external_return_abi_parts)))) >>
  strip_tac >>
  suspend "buffered_shared_allocation"
QED

Resume return_selected_valued_frag_full_core[buffered_shared_history]:
  `alloca_inv t` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx mid t` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[stmt_state_rel_def]) >>
  `gas_origin_ptr_path
    (<|d_stor:=K(K UNIV); d_trans:=K(K UNIV); d_imm:=K UNIV|>,
     lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (t,G1,tn1) [] (OK src_state,Gs,ts)` by
    (qpat_assum `!D. stor_taint_ok_at D tn1 t ==>
      gas_origin_ptr_path _ (t,G1,tn1) [] (OK src_state,Gs,ts)`
       MATCH_MP_TAC >> simp[stor_taint_ok_at_def]) >>
  drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >> strip_tac >>
  drule fragGasOriginTheory.gas_origin_path_erase >>
  disch_then (assume_tac o SIMP_RULE (srw_ss())
    [fragGasModeTheory.gas_marked_path_def]) >>
  `!u. gas_path_mem ctx func t 0 (OK u) ==> alloca_inv u` by
    (rpt strip_tac >>
     irule bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`fn_inst_ids_distinct func`,`alloca_history func t`,
     `gas_path_mem ctx func t 0 (OK src_state)`,
     `!u. gas_path_mem ctx func t 0 (OK u) ==> alloca_inv u`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  metis_tac[fragGasPathFrameMemTheory.gas_path_mem_zero_history]
QED

Resume return_selected_valued_frag_full_core[buffered_shared_allocation]:
  rename1 `compile_alloc_buffer abi_ce.ce_max_return_size unlock_st = (retbuf,renc_st)` >>
  rename1 `compile_abi_encode_to_buf retbuf.buf_operand src abi_ce.ce_ret_enc_info
    renc_st = (renc_len,renc_en)` >>
  `ci_mono unlock_st renc_st` by
    (qspecl_then [`abi_ce.ce_max_return_size`,`unlock_st`] mp_tac
      ci_mono_compile_alloc_buffer >> simp[]) >>
  `cs_extends unlock_st renc_st /\ cs_extends renc_st renc_en /\
   cs_extends renc_en sb` by
    metis_tac[ci_mono_def,abiEncoderAppendTheory.cs_extends_abi_encode,
      cs_extends_emit_inst] >>
  `fn_has_code unlock_st renc_st func /\ fn_has_code renc_st renc_en func /\
   fn_has_code renc_en sb func` by metis_tac[fn_has_code_split,cs_extends_trans] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp unlocked)` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx _ unlocked`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  qpat_assum `stmt_state_rel _ ctx func ce cx prepared_es unlocked`
    (fn pre =>
      let
        val target_h = hd (snd (strip_comb (concl pre)))
        val alloc_th = bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path
        val (_,packet) = strip_exists (snd (dest_imp (concl alloc_th)))
        val frame_h = fst (dest_forall (List.nth (strip_conj packet,6)))
        val alloc_at_h = INST_TYPE
          (match_type (type_of frame_h) (type_of target_h)) alloc_th
      in
        drule_all (Q.INST
          [`G` |-> `Gs`,`tn` |-> `unlock_tn`,
           `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] alloc_at_h)
      end) >>
  disch_then (qspecl_then [`unlock_tn`,`shadow_ctx`,`PG`,`Gs`] strip_assume_tac) >>
  suspend "buffered_allocated"
QED

Resume return_selected_valued_frag_full_core[buffered_allocated]:
  rename1 `retbuf.buf_operand = Var rdst` >>
  rename1 `lookup_var rdst ra = SOME rw` >>
  rename1 `ptr_covers rG rtn rdst ra abi_ce.ce_max_return_size` >>
  `ra.vs_memory=unlocked.vs_memory /\ ra.vs_halted=unlocked.vs_halted /\
   ra.vs_labels=unlocked.vs_labels` by
    (qpat_assum `ra with <|vs_vars := unlocked.vs_vars; vs_allocas := unlocked.vs_allocas;
       vs_alloca_next := unlocked.vs_alloca_next; vs_inst_idx := unlocked.vs_inst_idx|> = unlocked` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `eval_operand src ra=eval_operand src unlocked` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ra.vs_labels=unlocked.vs_labels`,`!x. src=Var x ==> not_fresh_at unlock_st x`,
        `!x. not_fresh_at unlock_st x ==> lookup_var x ra=lookup_var x unlocked /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `src` >> simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `!name b sz. local_region ce prepared_es.scopes ra name b sz <=>
    local_region ce prepared_es.scopes unlocked name b sz` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`local_ptrs_reserved ce unlock_st`,
        `!x. not_fresh_at unlock_st x ==> lookup_var x ra=lookup_var x unlocked /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> rpt gen_tac >>
     irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     rpt strip_tac >>
     `not_fresh_at unlock_st p` by
       metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     metis_tac[]) >>
  `expr_val_at ce cx physical_ty own_start own_end prepared_es v src ra` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`expr_val_at ce cx physical_ty own_start own_end prepared_es v src unlocked`,
        `eval_operand src ra=eval_operand src unlocked`,
        `!aid entry. FLOOKUP unlocked.vs_allocas aid=SOME entry ==> _`,
        `!name b sz. local_region ce prepared_es.scopes ra name b sz <=> _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [expr_val_at_def] >> rpt disch_tac >>
     gen_tac >> strip_tac >>
     qpat_assum `!tv. evaluate_type (get_tenv cx) physical_ty = SOME tv /\ _ ==> _`
       (qspec_then `tv` mp_tac) >>
     qpat_assum `evaluate_type (get_tenv cx) physical_ty = SOME tv`
       (fn ev => qpat_assum `~is_word_type physical_ty`
         (fn nw => simp_tac bool_ss [ev,nw])) >>
     disch_then (CONJUNCTS_THEN2 ASSUME_TAC
       (qx_choose_then `source_addr` strip_assume_tac)) >>
     asm_rewrite_tac[] >> qexists_tac `source_addr` >>
     asm_rewrite_tac[]
     >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >>
         asm_rewrite_tac[] >> first_assum MATCH_MP_TAC >> first_assum ACCEPT_TAC) >>
     disj2_tac >> disj1_tac >> qexistsl_tac [`n`,`b`,`sz`] >>
     asm_rewrite_tac[]) >>
  suspend "buffered_shared_source_prepare"
QED

Resume return_selected_valued_frag_full_core[buffered_shared_source_prepare]:
  `evaluate_type (get_tenv cx) physical_ty = SOME physical_tv` by metis_tac[] >>
  `?source_w. eval_operand src unlocked = SOME source_w` by
    (qpat_assum `expr_val_at ce cx physical_ty own_start own_end prepared_es v src unlocked` mp_tac >>
     qpat_assum `~is_word_type physical_ty` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) physical_ty=SOME physical_tv` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[expr_val_at_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside unlock_tn.t_mem unlocked.vs_memory mem ==>
    val_in_memory physical_tv v (w2n source_w) mem` by
    (qpat_assum `ptr_val_ok cx physical_ty v src Gs unlock_tn unlocked` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`~is_word_type physical_ty`,
        `evaluate_type (get_tenv cx) physical_ty = SOME physical_tv`,
        `eval_operand src unlocked = SOME source_w`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ptr_val_ok_def,ptr_mem_ok_def] >> metis_tac[]) >>
  `0 < val_footprint physical_tv v ==>
    w2n source_w + val_footprint physical_tv v <= unlocked.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`stmt_state_rel _ ctx func ce cx prepared_es unlocked`,
        `expr_val_at ce cx physical_ty own_start own_end prepared_es v src unlocked`,
        `evaluate_type (get_tenv cx) physical_ty = SOME physical_tv`,
        `~is_word_type physical_ty`,`eval_operand src unlocked = SOME source_w`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule_all (Q.INST [`ty` |-> `physical_ty`,`s` |-> `unlocked`,`tv` |-> `physical_tv`]
       expr_val_at_frontier) >>
     disch_then (qx_choose_then `front_w` strip_assume_tac) >>
     `front_w=source_w` by metis_tac[optionTheory.SOME_11] >>
     gvs[] >> decide_tac) >>
  suspend "buffered_source_plan"
QED

Resume return_selected_valued_frag_full_core[buffered_source_plan]:
  `abi_encoder_admissible abi_ce.ce_ret_enc_info` by
    (Cases_on `physical_ty = ret`
     >- (simp[Abbr `abi_ce`] >>
         `ce.ce_ret_enc_info =
           (update_cenv_ret_abi
             ((build_compile_env tops External mut tx.function_name args ret fbody ut)
               with ce_raw_return := rr) ret).ce_ret_enc_info` by
           (map_every (fn pat => qpat_assum pat mp_tac)
              [`ce.ce_ret_enc_info = cenv.ce_ret_enc_info`,
               `cenv.ce_ret_enc_info = cenv0.ce_ret_enc_info`,
               `cenv0 = cenv0' with ce_target := target`,
               `cenv0'.ce_ret_enc_info = _`, `ret <> NoneT`] >>
            POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
         pop_assum SUBST1_TAC >>
         simp[externalReturnWindowResourcesTheory.return_plan_encoder_admissible]) >>
     simp[Abbr `abi_ce`, externalReturnWindowResourcesTheory.return_plan_encoder_admissible]) >>
  `abi_enc_plan (type_env tops)
    (if needs_external_call_wrap physical_ty /\
       is_dynamic (vyper_to_abi_type (type_env tops) physical_ty)
     then TupleT [physical_ty] else physical_ty) abi_ce.ce_ret_enc_info /\
   vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap physical_ty /\
       is_dynamic (vyper_to_abi_type (type_env tops) physical_ty)
     then TupleT [physical_ty] else physical_ty) <= abi_ce.ce_max_return_size` by
    (Cases_on `physical_ty = ret`
     >- (drule_all return_selected_plan_nr >> strip_tac >>
         qpat_assum `physical_ty = ret`
           (fn th => simp_tac bool_ss [Abbr `abi_ce`, th]) >>
         conj_tac
         >- (irule return_same_frame_plan >> qexists_tac `cenv` >>
             rpt conj_tac >> first_assum ACCEPT_TAC) >>
         irule return_same_frame_capacity >> qexists_tac `cenv` >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `assignable_type (type_env tops) ret` by
       (drule_all return_selected_type_assignable >> simp[]) >>
     `assignable_type (type_env tops) physical_ty` by
       (qspecl_then [`physical_ty`,`ret`] mp_tac (cj 1 arg_type_fits_source_assignable) >>
        simp[] >> disch_then (qspec_then `type_env tops` mp_tac) >>
        simp[well_formed_type_def]) >>
     drule return_source_type_keys >> strip_tac >>
     qspecl_then [`tops`,`ce`,`physical_ty`] mp_tac update_cenv_ret_abi_plan >>
     simp[Abbr `abi_ce`]) >>
  `?abi_v. vyper_to_abi (type_env tops) physical_ty v = SOME abi_v` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`evaluate_type (type_env tops) physical_ty = SOME physical_tv`,`value_has_type physical_tv v`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[cj 1 vyperTypeABITheory.vyper_to_abi_total]) >>
  Q.SUBGOAL_THEN
    `?ct rv.
      contractABI$enc ct rv =
        (if needs_external_call_wrap physical_ty /\
            is_dynamic (vyper_to_abi_type (type_env tops) physical_ty)
         then contractABI$enc
           (Tuple [vyper_to_abi_type (type_env tops) physical_ty])
           (contractABI$ListV [abi_v])
         else contractABI$enc (vyper_to_abi_type (type_env tops) physical_ty) abi_v) /\
      LENGTH (contractABI$enc ct rv) <= abi_ce.ce_max_return_size /\
      (!mem. mem_agree_outside unlock_tn.t_mem unlocked.vs_memory mem ==>
        abi_encoder_window_input abi_ce.ce_ret_enc_info ct rv
          (w2n (source_w:bytes32)) (val_footprint physical_tv v) mem)`
    (qx_choose_then `ct` (qx_choose_then `rv` strip_assume_tac))
  >- (map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_enc_plan (type_env tops) (if _ then _ else _) _`,
        `vyper_abi_size_bound (type_env tops) (if _ then _ else _) <= _`,
        `evaluate_type (type_env tops) physical_ty = SOME physical_tv`,
        `value_has_type physical_tv v`,`safe_cast physical_tv v = SOME v`,
        `vyper_to_abi (type_env tops) physical_ty v = SOME abi_v`,
        `!mem. mem_agree_outside unlock_tn.t_mem unlocked.vs_memory mem ==> val_in_memory _ _ _ _`] >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
      Cases_on `needs_external_call_wrap physical_ty /\
        is_dynamic (vyper_to_abi_type (type_env tops) physical_ty)`
      >- suspend "buffered_shared_wrapped" >>
      `abi_enc_plan (type_env tops) physical_ty abi_ce.ce_ret_enc_info /\
       vyper_abi_size_bound (type_env tops) physical_ty <= abi_ce.ce_max_return_size` by
        metis_tac[] >>
      asm_rewrite_tac[] >>
      suspend "buffered_shared_unwrapped") >>
  qabbrev_tac `cap=val_footprint physical_tv v` >>
  `!i. i<cap ==> (w2n source_w+i IN rtn.t_mem <=>
    w2n source_w+i IN unlock_tn.t_mem)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!i. i IN rtn.t_mem <=> _`,
        `0<cap ==> _`,`Abbrev (cap = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     gen_tac >> strip_tac >>
     `0<cap /\ w2n source_w+i<unlocked.vs_alloca_next` by
       (fs[Abbr `cap`] >> decide_tac) >>
     `~(unlocked.vs_alloca_next <= w2n source_w+i)` by decide_tac >>
     asm_simp_tac bool_ss []) >>
  `!mem. mem_agree_outside rtn.t_mem ra.vs_memory mem ==>
    abi_encoder_window_input abi_ce.ce_ret_enc_info ct rv
      (w2n source_w) cap mem` by
    (gen_tac >> strip_tac >>
     mp_tac (Q.SPECL [`unlock_tn.t_mem`,`rtn.t_mem`,`unlocked.vs_memory`,`ra.vs_memory`,
       `w2n (source_w:bytes32)`,`w2n (source_w:bytes32)`,`cap`,`mem`]
       robustCopyTransportPtrTheory.copied_window_agree_witness) >>
     impl_tac >- asm_rewrite_tac[] >>
     disch_then (qx_choose_then `mix` strip_assume_tac) >>
     `abi_encoder_window_input abi_ce.ce_ret_enc_info ct rv
       (w2n source_w) cap mix` by
       (simp_tac bool_ss [Abbr `cap`] >>
        qpat_assum `!mem. mem_agree_outside unlock_tn.t_mem unlocked.vs_memory mem ==>
          abi_encoder_window_input _ _ _ _ _ _`
          MATCH_MP_TAC >> first_assum ACCEPT_TAC) >>
     irule abiEncoderWindowTheory.abi_encoder_window_input_mem_agree >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  suspend "buffered_generic_resources"
QED

Resume return_selected_valued_frag_full_core[buffered_shared_unwrapped]:
  mp_tac (Q.INST
    [`env` |-> `type_env tops`,`ty` |-> `physical_ty`,`ei` |-> `abi_ce.ce_ret_enc_info`,
     `tv` |-> `physical_tv`,`v` |-> `v`,`av` |-> `abi_v`,
     `tainted` |-> `unlock_tn.t_mem`,`initial_mem` |-> `unlocked.vs_memory`,
     `sb` |-> `w2n (source_w:bytes32)`]
    abiEncoderSourceRobustTheory.abi_encoder_source_window_robust) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choose_then `ct` (qx_choose_then `rv` strip_assume_tac)) >>
  qexistsl_tac [`ct`,`rv`] >>
  asm_rewrite_tac[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]

QED

Resume return_selected_valued_frag_full_core[buffered_generic_resources]:
  `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func ce cx prepared_es ra` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx prepared_es unlocked`
      (fn pre => first_assum (fn frame =>
        ACCEPT_TAC (MATCH_MP
          (SPEC (hd (snd (strip_comb (concl pre)))) frame) pre)))) >>
  `alloca_inv ra /\ alloca_room ctx func ra` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx prepared_es ra` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[stmt_state_rel_def]) >>
  `eval_operand src ra=SOME (n2w (w2n source_w)) /\
   eval_operand retbuf.buf_operand ra=SOME (n2w (w2n rw))` by
    asm_simp_tac (srw_ss()) [venomStateTheory.eval_operand_def,wordsTheory.n2w_w2n] >>
  `ptr_val_ok cx physical_ty v src Gs unlock_tn unlocked` by metis_tac[] >>
  `op_taint unlock_tn src={}` by
    (qpat_assum `ptr_val_ok cx physical_ty v src Gs unlock_tn unlocked` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ptr_val_ok_def]) >>
  `op_taint rtn src={}` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`op_taint unlock_tn src={}`,`!x. src=Var x ==> not_fresh_at unlock_st x`,
        `!x. not_fresh_at unlock_st x ==> lookup_var x ra=lookup_var x unlocked /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `src` >> fs[ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `op_taint rtn retbuf.buf_operand={}` by
    (qpat_assum `ptr_covers rG rtn rdst ra abi_ce.ce_max_return_size` mp_tac >>
     qpat_assum `retbuf.buf_operand=Var rdst` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ptr_covers_def]) >>
  `!x. src=Var x \/ retbuf.buf_operand=Var x ==> not_fresh_at renc_st x` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. src=Var x ==> not_fresh_at unlock_st x`,`retbuf.buf_operand=Var rdst`,
        `not_fresh_at renc_st rdst`,`ci_mono unlock_st renc_st`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ci_mono_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `0<cap ==> ?p. src=Var p /\ ptr_covers rG rtn p ra cap` by
    (strip_tac >> `val_footprint physical_tv v<>0` by fs[Abbr `cap`] >>
     mp_tac (Q.SPECL [`cx`,`physical_ty`,`v`,`src`,`Gs`,`unlock_tn`,`unlocked`,
       `physical_tv`,`source_w:bytes32`,`cap`]
       representationCleanPtrTheory.ptr_val_ok_read_covers) >>
     impl_tac >- (asm_rewrite_tac[] >> simp[Abbr `cap`]) >>
     disch_then (qx_choose_then `source_var` strip_assume_tac) >>
     qexists_tac `source_var` >> asm_rewrite_tac[] >>
     irule (Q.INST [`sa` |-> `unlock_st`,`s` |-> `unlocked`,`s'` |-> `ra`,
       `G` |-> `Gs`,`tn` |-> `unlock_tn`,`G'` |-> `rG`,`tn'` |-> `rtn`]
       appendStorageGhostPtrTheory.ptr_covers_old_transport) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers Gs unlock_tn source_var unlocked cap`,
        `src=Var source_var`,`!x. src=Var x ==> not_fresh_at unlock_st x`,
        `!x. not_fresh_at unlock_st x ==> lookup_var x ra=lookup_var x unlocked /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `w2n rw+LENGTH (contractABI$enc ct rv)<=ra.vs_alloca_next` by decide_tac >>
  `0<LENGTH (contractABI$enc ct rv) ==> ?p.
    retbuf.buf_operand=Var p /\ ptr_covers rG rtn p ra (LENGTH (contractABI$enc ct rv))` by
    (strip_tac >> qexists_tac `rdst` >> conj_tac
     >- first_assum ACCEPT_TAC >>
     irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  suspend "buffered_generic_output_resources"
QED

Resume return_selected_valued_frag_full_core[buffered_generic_output_resources]:
  `local_ptrs_reserved ce renc_st` by
    metis_tac[local_ptrs_reserved_next_var,ci_mono_def] >>
  drule_at (Pat `compile_alloc_buffer _ unlock_st = _`) compile_alloc_buffer_parts >>
  strip_tac >>
  `rdst=STRING #"%" (toString unlock_st.cs_next_var)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`retbuf.buf_operand=Var rdst`,
       `retbuf.buf_operand=Var (STRING #"%" (toString unlock_st.cs_next_var))`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `MEM (mk_inst unlock_st.cs_next_id ALLOCA
      [Lit (n2w abi_ce.ce_max_return_size)] [rdst]) (fn_insts func)` by
    (drule_all exprSimAllocTheory.buffer_alloc_code >>
     asm_simp_tac bool_ss []) >>
  `not_local_ptr ce prepared_es.scopes rdst` by
    (qpat_assum `local_ptrs_reserved ce unlock_st` mp_tac >>
     qpat_assum `rdst=STRING #"%" (toString unlock_st.cs_next_var)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> asm_rewrite_tac[] >>
     irule (Q.SPECL [`ce`,`unlock_st`,`prepared_es.scopes`,`unlock_st.cs_next_var`]
       local_ptrs_reserved_fresh) >> simp[]) >>
  `expr_val_at ce cx physical_ty own_start own_end prepared_es v src ra` by
    first_assum ACCEPT_TAC >>
  `eval_operand src ra=SOME source_w /\ cap<=val_footprint physical_tv v` by
    asm_simp_tac (srw_ss()) [Abbr `cap`,wordsTheory.n2w_w2n] >>
  `(mk_inst unlock_st.cs_next_id ALLOCA
      [Lit (n2w abi_ce.ce_max_return_size)] [rdst]).inst_outputs=[rdst] /\
   own_end.cs_next_id <=
     (mk_inst unlock_st.cs_next_id ALLOCA
       [Lit (n2w abi_ce.ce_max_return_size)] [rdst]).inst_id /\
   FLOOKUP ra.vs_allocas
     (mk_inst unlock_st.cs_next_id ALLOCA
       [Lit (n2w abi_ce.ce_max_return_size)] [rdst]).inst_id=
       SOME (w2n rw,abi_ce.ce_max_return_size)` by
    asm_simp_tac (srw_ss()) [venomInstTheory.mk_inst_def] >>
  `venomMemDefs$regions_disjoint
    (w2n source_w,cap) (w2n rw,abi_ce.ce_max_return_size)` by
    (drule_all (Q.INST
      [`s` |-> `ra`,`ty` |-> `physical_ty`,`sa` |-> `own_start`,`sb` |-> `own_end`,
       `v` |-> `v`,`src` |-> `(src:operand)`,`tv` |-> `physical_tv`,
       `p` |-> `(source_w:bytes32)`,`cap` |-> `cap`,
       `inst` |-> `mk_inst unlock_st.cs_next_id ALLOCA
          [Lit (n2w abi_ce.ce_max_return_size)] [rdst]`,
       `x` |-> `rdst`,`b` |-> `w2n (rw:bytes32)`,`sz` |-> `abi_ce.ce_max_return_size`]
      externalReturnSourceWindowTheory.expression_source_window_disjoint) >>
     disch_then ACCEPT_TAC) >>
  `0<cap ==> w2n source_w+cap<=ra.vs_alloca_next /\
    venomMemDefs$regions_disjoint
      (w2n source_w,cap) (w2n rw,LENGTH (contractABI$enc ct rv)) /\
    ?p. src=Var p /\ ptr_covers rG rtn p ra cap` by
    (strip_tac >> rpt conj_tac
     >- (map_every (fn pat => qpat_assum pat mp_tac)
           [`0<cap ==> w2n source_w+cap<=unlocked.vs_alloca_next`,
            `unlocked.vs_alloca_next<=ra.vs_alloca_next`,`0<cap`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)
     >- (map_every (fn pat => qpat_assum pat mp_tac)
          [`venomMemDefs$regions_disjoint (w2n source_w,cap) _`,
           `LENGTH (contractABI$enc ct rv)<=abi_ce.ce_max_return_size`] >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
     first_assum MATCH_MP_TAC >> first_assum ACCEPT_TAC) >>
  `unlock_st.cs_next_id NOTIN frag_ids renc_st renc_en` by
    (irule externalReturnEncoderSitesTheory.allocated_encoder_site_excluded >>
     qexistsl_tac [`retbuf`,`abi_ce.ce_max_return_size`] >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST
    [`s` |-> `ra`,`parent` |-> `unlock_st.cs_next_id`,
     `p` |-> `w2n (rw:bytes32)`,`n` |-> `abi_ce.ce_max_return_size`,
     `ids` |-> `frag_ids renc_st renc_en`,
     `k` |-> `LENGTH (contractABI$enc ct rv)`]
    registeredAllocationWindowTheory.registered_allocation_subwindow_disjoint) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  suspend "buffered_generic_scratch"
QED

Resume return_selected_valued_frag_full_core[buffered_generic_scratch]:
  `!inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode=ALLOCA /\
    inst.inst_id IN frag_ids renc_st renc_en /\
    FLOOKUP ra.vs_allocas inst.inst_id=SOME (b,sz) ==>
    sz=32 /\
    (0<cap ==> venomMemDefs$regions_disjoint (w2n source_w,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint
      (w2n rw,LENGTH (contractABI$enc ct rv)) (b,sz)` by
    (rpt gen_tac >> strip_tac >>
     drule_all (Q.INST [`cenv` |-> `ce`,`scopes` |-> `prepared_es.scopes`]
       externalReturnEncoderSitesTheory.encoder_function_alloca_nonlocal) >>
     disch_then (qspec_then `prepared_es` (CONJUNCTS_THEN2 ASSUME_TAC
       (qx_choose_then `scratch_var` strip_assume_tac))) >>
     `sz=32` by
       (qpat_assum `stmt_state_rel _ ctx func ce cx prepared_es ra`
         (mp_tac o REWRITE_RULE [stmt_state_rel_def]) >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`MEM inst (fn_insts func)`,`inst.inst_opcode=ALLOCA`,
           `inst.inst_operands=[Lit 32w]`,
           `FLOOKUP ra.vs_allocas inst.inst_id=SOME (b,sz)`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        first_x_assum (qspecl_then [`inst`,`32w`,`b`,`sz`] mp_tac) >>
        asm_simp_tac (srw_ss()) [wordsTheory.dimword_def,
          fcpLib.INDEX_CONV ``dimindex (:256)``]) >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (strip_tac >>
         `cap<=val_footprint physical_tv v /\ own_end.cs_next_id<=inst.inst_id` by
           (asm_simp_tac (srw_ss()) [Abbr `cap`] >>
            qpat_assum `inst.inst_id IN frag_ids renc_st renc_en` mp_tac >>
            qpat_assum `own_end.cs_next_id<=unlock_st.cs_next_id` mp_tac >>
            qpat_assum `ci_mono unlock_st renc_st` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >>
            simp[abiEncoderPropsTheory.frag_ids_def,ci_mono_def] >> decide_tac) >>
         drule_all (Q.INST
           [`ctx` |-> `ctx`,`func` |-> `func`,`ce` |-> `ce`,`cx` |-> `cx`,
            `es` |-> `prepared_es`,`s` |-> `ra`,`ty` |-> `physical_ty`,
            `sa` |-> `own_start`,`sb` |-> `own_end`,`v` |-> `v`,`src` |-> `(src:operand)`,
            `tv` |-> `physical_tv`,`p` |-> `(source_w:bytes32)`,`cap` |-> `cap`,
            `inst` |-> `inst`,`x` |-> `scratch_var`,`b` |-> `b`,`sz` |-> `sz`]
           externalReturnSourceWindowTheory.expression_source_window_disjoint) >>
         disch_then ACCEPT_TAC) >>
     qpat_assum `!id b sz. id IN frag_ids renc_st renc_en /\ _ ==> _`
       (qspecl_then [`inst.inst_id`,`b`,`sz`] MATCH_MP_TAC) >>
     asm_rewrite_tac[]) >>
  suspend "buffered_generic_call"
QED

Resume return_selected_valued_frag_full_core[buffered_generic_call]:
  `lo<=ra.vs_alloca_next` by
    (qpat_assum `lo<=unlocked.vs_alloca_next` mp_tac >>
     qpat_assum `unlocked.vs_alloca_next<=ra.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `~ra.vs_halted` by asm_rewrite_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp ra /\
    ra.vs_alloca_next + pending_alloca_size func ra <= w2n ra.vs_initial_fmp` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx prepared_es ra` (fn related =>
       mp_tac (MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp related) >>
       mp_tac (MATCH_MP stateRelProjTheory.stmt_state_rel_fmp_room related)) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[exprLoweringPropsTheory.fmp_room_def] >> decide_tac) >>
  mp_tac (Q.INST
    [`window_dst` |-> `retbuf.buf_operand`,`window_src` |-> `(src:operand)`,
     `ei` |-> `abi_ce.ce_ret_enc_info`,`st` |-> `renc_st`,
     `out` |-> `renc_len`,`en` |-> `renc_en`,`ctx` |-> `ctx`,`func` |-> `func`,
     `s` |-> `ra`,`at` |-> `ct`,`av` |-> `rv`,
     `sb` |-> `w2n (source_w:bytes32)`,`cap` |-> `cap`,
     `d` |-> `w2n (rw:bytes32)`,`G` |-> `rG`,`tn` |-> `rtn`,`lo` |-> `lo`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,`PG` |-> `PG`]
    (Q.INST [`dst` |-> `window_dst`,`src` |-> `window_src`]
      (SPEC_ALL abiEncoderWindowJointTheory.compile_abi_encode_to_buf_window_joint))) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `rencoded` (qx_choose_then `rGenc`
    (qx_choose_then `rtenc` strip_assume_tac))) >>
  suspend "buffered_encoded_endpoint"
QED

Resume return_selected_valued_frag_full_core[buffered_encoded_endpoint]:
  `mem_bytes_at (w2n rw) (LENGTH (contractABI$enc ct rv)) rencoded.vs_memory =
      contractABI$enc ct rv /\
   eval_operand renc_len rencoded=SOME (n2w (LENGTH (contractABI$enc ct rv))) /\
   alloca_inv rencoded /\ alloca_room ctx func rencoded /\
   (!x w. not_fresh_at renc_st x /\ lookup_var x ra=SOME w ==>
      lookup_var x rencoded=SOME w) /\
   ~rencoded.vs_halted /\ rencoded.vs_current_bb=renc_en.cs_current_bb /\
   rencoded.vs_inst_idx=LENGTH renc_en.cs_current_insts` by
    (qpat_assum `window_strong_result ctx func renc_st renc_en renc_len
       ct rv (w2n rw) ra rencoded` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abiEncoderWindowContractTheory.window_strong_result_def,
       abiEncoderWindowContractTheory.abi_encoder_window_result_def] >>
     rpt strip_tac >> asm_rewrite_tac[]) >>
  `abi_encoder_registered_effect (frag_ids renc_st renc_en)
      [(w2n rw,LENGTH (contractABI$enc ct rv))] ra rencoded /\
   window_alloca_growth ra rencoded` by
    (qpat_assum `window_strong_result ctx func renc_st renc_en renc_len
       ct rv (w2n rw) ra rencoded` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abiEncoderWindowContractTheory.window_strong_result_def,
       abiEncoderWindowContractTheory.abi_encoder_window_result_def] >>
     rpt strip_tac >> asm_rewrite_tac[]) >>
  `lookup_var rdst rencoded=SOME rw` by
    (first_assum MATCH_MP_TAC >> conj_tac >> first_assum ACCEPT_TAC) >>
  `FLOOKUP rGenc rdst=FLOOKUP rG rdst /\
   op_taint rtenc (Var rdst)=op_taint rtn (Var rdst)` by
    (qpat_assum `!x. not_fresh_at renc_st x ==> _ /\ _`
       (qspec_then `rdst` MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
  `eval_operand retbuf.buf_operand rencoded=SOME rw /\
   op_taint rtenc retbuf.buf_operand={}` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`retbuf.buf_operand=Var rdst`,`lookup_var rdst rencoded=SOME rw`,
       `op_taint rtenc (Var rdst)=op_taint rtn (Var rdst)`,
       `op_taint rtn retbuf.buf_operand={}`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[venomStateTheory.eval_operand_def] >>
     metis_tac[]) >>
  `ptr_covers rGenc rtenc rdst rencoded abi_ce.ce_max_return_size` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`ptr_covers rG rtn rdst ra abi_ce.ce_max_return_size`,
       `lookup_var rdst ra=SOME rw`,`lookup_var rdst rencoded=SOME rw`,
       `FLOOKUP rGenc rdst=FLOOKUP rG rdst`,
       `op_taint rtenc (Var rdst)=op_taint rtn (Var rdst)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ptr_covers_def] >> metis_tac[]) >>
  `ra.vs_alloca_next<=rencoded.vs_alloca_next` by
    (qpat_assum `window_alloca_growth ra rencoded` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiEncoderWindowContractTheory.window_alloca_growth_def]) >>
  `lo<=rencoded.vs_alloca_next /\
   w2n rw+LENGTH (contractABI$enc ct rv)<=rencoded.vs_alloca_next /\
   LENGTH (contractABI$enc ct rv)<dimword (:256)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`lo<=ra.vs_alloca_next`,`ra.vs_alloca_next<=rencoded.vs_alloca_next`,
       `w2n rw+LENGTH (contractABI$enc ct rv)<=ra.vs_alloca_next`,
       `LENGTH (contractABI$enc ct rv)<=abi_ce.ce_max_return_size`,
       `abi_ce.ce_max_return_size<dimword (:256)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  suspend "buffered_encoded_resources"
QED

Resume return_selected_valued_frag_full_core[buffered_encoded_resources]:
  `!i r. FLOOKUP ra.vs_allocas i=SOME r ==>
    FLOOKUP rencoded.vs_allocas i=SOME r` by
    (qpat_assum `abi_encoder_registered_effect (frag_ids renc_st renc_en)
      [(w2n rw,LENGTH (contractABI$enc ct rv))] ra rencoded` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated]) >>
  `allocas_from lo rencoded` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`allocas_from lo ra`,`lo<=ra.vs_alloca_next`,
       `window_alloca_growth ra rencoded`,
       `!i r. FLOOKUP ra.vs_allocas i=SOME r ==> _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [ptrDisciplineTheory.allocas_from_def,
       abiEncoderWindowContractTheory.window_alloca_growth_def] >>
     rpt disch_tac >> rpt strip_tac >> Cases_on `FLOOKUP ra.vs_allocas aid` >>
     metis_tac[optionTheory.SOME_11,arithmeticTheory.LESS_EQ_TRANS]) >>
  `ra.vs_accounts=unlocked.vs_accounts /\
   ra.vs_transient=unlocked.vs_transient /\
   ra.vs_immutables=unlocked.vs_immutables /\ ra.vs_logs=unlocked.vs_logs /\
   ra.vs_requests=unlocked.vs_requests /\
   ra.vs_pending_deletions=unlocked.vs_pending_deletions /\
   ra.vs_call_ctx=unlocked.vs_call_ctx` by
    (qpat_assum `ra with <|vs_vars:=unlocked.vs_vars;
       vs_allocas:=unlocked.vs_allocas;vs_alloca_next:=unlocked.vs_alloca_next;
       vs_inst_idx:=unlocked.vs_inst_idx|> = unlocked`
       (mp_tac o AP_TERM ``\u:venom_state.
         (u.vs_accounts,u.vs_transient,u.vs_immutables,u.vs_logs,
          u.vs_requests,u.vs_pending_deletions,u.vs_call_ctx)``) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `rencoded.vs_accounts=unlocked.vs_accounts /\
   rencoded.vs_transient=unlocked.vs_transient /\
   rencoded.vs_immutables=unlocked.vs_immutables /\
   rencoded.vs_logs=unlocked.vs_logs /\
   rencoded.vs_requests=unlocked.vs_requests /\
   rencoded.vs_pending_deletions=unlocked.vs_pending_deletions /\
   rencoded.vs_call_ctx=unlocked.vs_call_ctx` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`abi_encoder_registered_effect (frag_ids renc_st renc_en)
          [(w2n rw,LENGTH (contractABI$enc ct rv))] ra rencoded`,
       `abi_encode_exec_frame func ra rencoded`,
       `ra.vs_accounts=unlocked.vs_accounts`,
       `ra.vs_transient=unlocked.vs_transient`,
       `ra.vs_immutables=unlocked.vs_immutables`,
       `ra.vs_logs=unlocked.vs_logs`,`ra.vs_requests=unlocked.vs_requests`,
       `ra.vs_pending_deletions=unlocked.vs_pending_deletions`,
       `ra.vs_call_ctx=unlocked.vs_call_ctx`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss
       [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def,
        exprSimAbiEncodeExecFrameTheory.abi_encode_exec_frame_def] >>
     rpt strip_tac >> asm_rewrite_tac[]) >>
  `!D. stor_taint_ok_at D rtenc rencoded <=> stor_taint_ok_at D unlock_tn unlocked` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`rtenc.t_stor=rtn.t_stor`,`rtenc.t_trans=rtn.t_trans`,
       `rtenc.t_imm=rtn.t_imm`,`rtn.t_stor=unlock_tn.t_stor`,
       `rtn.t_trans=unlock_tn.t_trans`,`rtn.t_imm=unlock_tn.t_imm`,
       `rencoded.vs_accounts=unlocked.vs_accounts`,
       `rencoded.vs_transient=unlocked.vs_transient`,
       `rencoded.vs_immutables=unlocked.vs_immutables`,
       `rencoded.vs_call_ctx=unlocked.vs_call_ctx`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[stor_taint_ok_at_def]) >>
  suspend "buffered_return_prepare"
QED

Resume return_selected_valued_frag_full_core[buffered_return_prepare]:
  qabbrev_tac `ret_inst=mk_inst renc_en.cs_next_id RETURN
    [retbuf.buf_operand;renc_len] []` >>
  qabbrev_tac `ret_ss=halt_state
    (set_returndata (contractABI$enc ct rv) rencoded)` >>
  `read_memory (w2n rw) (LENGTH (contractABI$enc ct rv)) rencoded=
    contractABI$enc ct rv` by
    (qpat_assum `mem_bytes_at (w2n rw) (LENGTH (contractABI$enc ct rv))
       rencoded.vs_memory=contractABI$enc ct rv` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomStateTheory.read_memory_def,valueEncodingDefsTheory.mem_bytes_at_def]) >>
  `w2n (n2w (LENGTH (contractABI$enc ct rv)):bytes32)=
    LENGTH (contractABI$enc ct rv)` by
    (qpat_assum `LENGTH (contractABI$enc ct rv)<dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD]) >>
  drule_all emitHelperPropsTheory.emitted_insts_emit_inst >> strip_tac >>
  drule_all emitHelperPropsTheory.inst_extends_emit_inst >> strip_tac >>
  `sb.cs_current_bb=renc_en.cs_current_bb /\
   sb.cs_current_insts=renc_en.cs_current_insts++[ret_inst]` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`sb.cs_current_bb=renc_en.cs_current_bb`,
       `inst_extends renc_en sb`,`emitted_insts renc_en sb=_`,
       `Abbrev (ret_inst=_)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     fs[emitHelperPropsTheory.inst_extends_def,Abbr `ret_inst`]) >>
  mp_tac (Q.SPECL [`renc_en`,`sb`,`func`,`[ret_inst]`]
    fragExecTheory.fn_has_code_same_block) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `ret_bb` strip_assume_tac) >>
  qpat_assum `!i. i<LENGTH [ret_inst] ==> _`
    (qspec_then `0` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `step_inst_base ret_inst rencoded=Halt ret_ss` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`eval_operand retbuf.buf_operand rencoded=SOME rw`,
       `eval_operand renc_len rencoded=SOME (n2w (LENGTH (contractABI$enc ct rv)))`,
       `read_memory (w2n rw) (LENGTH (contractABI$enc ct rv)) rencoded=contractABI$enc ct rv`,
       `w2n (n2w (LENGTH (contractABI$enc ct rv)):bytes32)=LENGTH (contractABI$enc ct rv)`,
       `Abbrev (ret_inst=_)`,`Abbrev (ret_ss=_)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qspecl_then [`retbuf.buf_operand`,`renc_len`,`rw`,
       `(n2w (LENGTH (contractABI$enc ct rv)):bytes32)`,
       `renc_en.cs_next_id`,`rencoded`] mp_tac
       emitHelperPropsTheory.step_RETURN >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     asm_simp_tac (srw_ss()) [Abbr `ret_inst`,Abbr `ret_ss`,
       GSYM venomStateTheory.read_memory_def]) >>
  suspend "buffered_return_pointer"
QED

Resume return_selected_valued_frag_full_core[buffered_return_pointer]:
  `ptr_covers rGenc rtenc rdst rencoded (LENGTH (contractABI$enc ct rv))` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  `access_ok lo rGenc func ret_inst rencoded` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`ptr_covers rGenc rtenc rdst rencoded (LENGTH (contractABI$enc ct rv))`,
       `retbuf.buf_operand=Var rdst`,
       `eval_operand retbuf.buf_operand rencoded=SOME rw`,
       `eval_operand renc_len rencoded=SOME (n2w (LENGTH (contractABI$enc ct rv)))`,
       `w2n (n2w (LENGTH (contractABI$enc ct rv)):bytes32)=LENGTH (contractABI$enc ct rv)`,
       `Abbrev (ret_inst=_)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     fs[Abbr `ret_inst`,ptr_covers_def,ptrDisciplineTheory.access_ok_def,
       venomInstTheory.mk_inst_def,contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.memory_range_of_operands_def,
       memLocDefsTheory.mem_read_ops_def,memLocDefsTheory.mem_write_ops_def,
       venomStateTheory.eval_operand_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `inst_mem_below_frontier ret_inst rencoded /\
   inst_dload_in_section ret_inst rencoded` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`eval_operand retbuf.buf_operand rencoded=SOME rw`,
       `eval_operand renc_len rencoded=SOME (n2w (LENGTH (contractABI$enc ct rv)))`,
       `w2n (n2w (LENGTH (contractABI$enc ct rv)):bytes32)=LENGTH (contractABI$enc ct rv)`,
       `w2n rw+LENGTH (contractABI$enc ct rv)<=rencoded.vs_alloca_next`,
       `Abbrev (ret_inst=_)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> conj_tac
     >- asm_simp_tac (srw_ss()) [Abbr `ret_inst`,instMemFrontierTheory.below_frontier_RETURN] >>
     simp[Abbr `ret_inst`,memSafeRunTheory.inst_dload_in_section_def,
       venomInstTheory.mk_inst_def]) >>
  `ret_inst.inst_opcode=RETURN` by
    simp[Abbr `ret_inst`,venomInstTheory.mk_inst_def] >>
  `!fuel. step_inst fuel ctx ret_inst rencoded=Halt ret_ss` by
    asm_simp_tac (srw_ss()) [venomExecSemanticsTheory.step_inst_non_invoke] >>
  `mem_safe_step 0 ctx ret_inst rencoded` by
    asm_simp_tac (srw_ss()) [memSafeRunTheory.mem_safe_step_non_invoke] >>
  suspend "buffered_return_path"
QED

Resume return_selected_valued_frag_full_core[buffered_return_path]:
  `!H. stor_taint_ok_at (DF H) tn1 t ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (rencoded,rGenc,rtenc) [] (Halt ret_ss,rGenc,rtenc)` by
    (gen_tac >> strip_tac >>
     `stor_taint_ok_at (DF H) rtenc rencoded` by
       (qpat_assum `!D. stor_taint_ok_at D rtenc rencoded <=> _`
          (qspec_then `DF H` mp_tac) >>
        qpat_assum `!H. stor_taint_ok_at (DF H) tn1 t ==> stor_taint_ok_at (DF H) unlock_tn unlocked`
          (qspec_then `H` mp_tac) >>
        qpat_assum `stor_taint_ok_at (DF H) tn1 t` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `ctx_has_dalloca ctx ==> allocas_below_fmp rencoded` by
       (strip_tac >>
        `rencoded.vs_fmp = ra.vs_fmp` by
          (qpat_assum `abi_encode_exec_frame func ra rencoded`
             (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o
              PURE_REWRITE_RULE [exprSimAbiEncodeExecFrameTheory.abi_encode_exec_frame_def])) >>
        qpat_assum `!D. gas_origin_ptr_path _ (ra,rG,rtn) [] (OK rencoded,rGenc,rtenc)`
          (qspec_then `DF H` assume_tac) >>
        drule_all decoderOriginAllocationFrameTheory.decoder_origin_path_room >> simp[]) >>
     `ptr_inst_ok (DF H) lo 0 ctx func rGenc rtenc ret_inst rencoded` by
       (qunabbrev_tac `ret_inst` >>
        mp_tac (Q.INST
          [`a` |-> `retbuf.buf_operand`,`n` |-> `renc_len`,
           `s` |-> `rencoded`,`G` |-> `rGenc`,`tn` |-> `rtenc`,
           `w` |-> `(rw:bytes32)`,
           `k` |-> `(n2w (LENGTH (contractABI$enc ct rv)):bytes32)`,
           `lo` |-> `lo`,`ctx` |-> `ctx`,`fn` |-> `func`,`D` |-> `DF (H : (bool # bytes32 # type_value) list # num list)`,
           `id` |-> `renc_en.cs_next_id`]
          (SPEC_ALL externalReturnRawJointTheory.raw_return_operand_check)) >>
        impl_tac >-
          (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
           qpat_assum `w2n (n2w (LENGTH (contractABI$enc ct rv)):bytes32) = _`
             (fn eq => PURE_ONCE_REWRITE_TAC [eq]) >>
           first_assum ACCEPT_TAC) >>
        disch_then ACCEPT_TAC) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`lookup_block renc_en.cs_current_bb func.fn_blocks=SOME ret_bb`,
        `get_instruction ret_bb (LENGTH renc_en.cs_current_insts)=SOME ret_inst`,
        `rencoded.vs_current_bb=renc_en.cs_current_bb`,
        `rencoded.vs_inst_idx=LENGTH renc_en.cs_current_insts`,
        `~rencoded.vs_halted`,`ret_inst.inst_opcode=RETURN`,
        `!fuel. step_inst fuel ctx ret_inst rencoded=Halt ret_ss`,
        `ptr_inst_ok (DF H) lo 0 ctx func rGenc rtenc ret_inst rencoded`,
        `mem_safe_step 0 ctx ret_inst rencoded`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule (Q.INST [`bb` |-> `ret_bb`,`i` |-> `ret_inst`]
       (SPEC_ALL fragGasEmitCtrlTheory.exit_inst_origin_ptr)) >>
     asm_simp_tac (srw_ss()) [gasEventsTheory.gas_events_step_def,
       gasCountTheory.gas_count_step_def,fragExecTheory.exit_result_def]) >>
  suspend "buffered_return_finish"
QED

Resume return_selected_valued_frag_full_core[buffered_return_finish]:
  qexistsl_tac [`ret_ss`,`rGenc`,`rtenc`,`abi_v`] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qpat_assum `contractABI$enc ct rv = _` mp_tac >>
      qpat_assum `Abbrev (ret_ss=_)` mp_tac >>
      qpat_assum `needs_external_call_wrap physical_ty = needs_external_call_wrap ret` mp_tac >>
      qpat_assum `vyper_to_abi_type (type_env tops) physical_ty = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
      asm_simp_tac bool_ss [Abbr `ret_ss`,venomStateTheory.halt_state_def,
        venomStateTheory.set_returndata_def,
        venomStateTheory.venom_state_accfupds,
        venomStateTheory.venom_state_accessors,combinTheory.K_THM] >>
      Cases_on `needs_external_call_wrap ret` >>
      Cases_on `is_dynamic (vyper_to_abi_type (type_env tops) ret)` >>
      fs[contractABITheory.enc_def,LET_THM]) >>
  `rencoded.vs_accounts=t.vs_accounts /\
   rencoded.vs_transient=
      (if nr /\ mut <> View then (tstore (n2w nkey) 0w t).vs_transient
       else t.vs_transient) /\
   rencoded.vs_immutables=t.vs_immutables /\
   rencoded.vs_logs=t.vs_logs /\ rencoded.vs_requests=t.vs_requests /\
   rencoded.vs_pending_deletions=t.vs_pending_deletions /\
   rencoded.vs_call_ctx=t.vs_call_ctx` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`rencoded.vs_accounts=unlocked.vs_accounts`,
        `rencoded.vs_transient=unlocked.vs_transient`,
        `rencoded.vs_immutables=unlocked.vs_immutables`,
        `rencoded.vs_logs=unlocked.vs_logs`,
        `rencoded.vs_requests=unlocked.vs_requests`,
        `rencoded.vs_pending_deletions=unlocked.vs_pending_deletions`,
        `rencoded.vs_call_ctx=unlocked.vs_call_ctx`,
        `unlocked.vs_accounts=src_state.vs_accounts`,
        `unlocked.vs_transient=_`,
        `unlocked.vs_immutables=src_state.vs_immutables`,
        `unlocked.vs_logs=src_state.vs_logs`,
        `unlocked.vs_requests=src_state.vs_requests`,
        `unlocked.vs_pending_deletions=src_state.vs_pending_deletions`,
        `unlocked.vs_call_ctx=src_state.vs_call_ctx`,
        `src_state.vs_accounts=t.vs_accounts`,
        `src_state.vs_immutables=t.vs_immutables`,
        `src_state.vs_logs=t.vs_logs`,
        `src_state.vs_requests=t.vs_requests`,
        `src_state.vs_pending_deletions=t.vs_pending_deletions`,
        `src_state.vs_call_ctx=t.vs_call_ctx`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  rpt (conj_tac >-
    (simp_tac (srw_ss()) [Abbr `ret_ss`,
       venomStateTheory.halt_state_def,venomStateTheory.set_returndata_def] >>
     first_assum ACCEPT_TAC)) >>
  gen_tac >> strip_tac >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (t,G1,tn1) [] (OK unlocked,Gs,unlock_tn)` by
    (qpat_assum `!D. stor_taint_ok_at D tn1 t ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `DF H` mp_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (src_state,Gs,ts) [] _`
       (qspecl_then [`DF H`,`gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
     qpat_assum `stor_taint_ok_at (DF H) tn1 t` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  qpat_assum `!D. gas_origin_ptr_path _ (unlocked,Gs,unlock_tn) [] (OK ra,rG,rtn)`
    (qspec_then `DF H` assume_tac) >>
  qpat_assum `!D. gas_origin_ptr_path _ (ra,rG,rtn) [] (OK rencoded,rGenc,rtenc)`
    (qspec_then `DF H` assume_tac) >>
  qpat_assum `!H. stor_taint_ok_at (DF H) tn1 t ==>
    gas_origin_ptr_path _ (rencoded,rGenc,rtenc) [] (Halt ret_ss,rGenc,rtenc)`
    (qspec_then `H` (fn th => qpat_assum `stor_taint_ok_at (DF H) tn1 t`
      (assume_tac o MATCH_MP th))) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK unlocked,Gs,unlock_tn)`,
     `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (unlocked,Gs,unlock_tn) [] (OK ra,rG,rtn)`,
     `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (ra,rG,rtn) [] (OK rencoded,rGenc,rtenc)`,
     `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (rencoded,rGenc,rtenc) [] (Halt ret_ss,rGenc,rtenc)`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]
QED


Resume return_selected_valued_frag_full_core[buffered_shared_wrapped]:
  `abi_enc_plan (type_env tops) (TupleT [physical_ty]) abi_ce.ce_ret_enc_info /\
   vyper_abi_size_bound (type_env tops) (TupleT [physical_ty]) <= abi_ce.ce_max_return_size` by
    metis_tac[] >>
  asm_rewrite_tac[] >>
  qspecl_then [`type_env tops`,`physical_ty`,`physical_tv`,`v`,`v`,`T`]
    (mp_tac o PURE_REWRITE_RULE [boolTheory.COND_CLAUSES])
    vyperLoweringCorrectTheory.return_abi_value_package >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choose_then `wrapped_tv` (qx_choose_then `wrapped_value`
    (qx_choose_then `wrapped_av` strip_assume_tac))) >>
  `wrapped_value=ArrayV (TupleV [v])` by fs[] >>
  `wrapped_av=contractABI$ListV [abi_v]` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`vyper_to_abi (type_env tops) (TupleT [physical_ty]) wrapped_value=SOME wrapped_av`,
       `wrapped_value=ArrayV (TupleV [v])`,
       `vyper_to_abi (type_env tops) physical_ty v=SOME abi_v`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[vyperABITheory.vyper_to_abi_def]) >>
  `LENGTH (contractABI$enc
      (Tuple [vyper_to_abi_type (type_env tops) physical_ty])
      (contractABI$ListV [abi_v])) <= abi_ce.ce_max_return_size` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`LENGTH (contractABI$enc
          (vyper_to_abi_type (type_env tops) (TupleT [physical_ty]))
          wrapped_av) <= _`,
       `wrapped_av=contractABI$ListV [abi_v]`,
       `vyper_abi_size_bound (type_env tops) (TupleT [physical_ty]) <= abi_ce.ce_max_return_size`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[vyperABITheory.vyper_to_abi_type_def] >> rpt strip_tac >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  Cases_on `val_footprint physical_tv v=type_memory_size physical_tv`
  >- suspend "buffered_shared_wrapped_nominal" >>
  suspend "buffered_shared_wrapped_packed"
QED

Resume return_selected_valued_frag_full_core[buffered_shared_wrapped_nominal]:
  `!mem. mem_agree_outside unlock_tn.t_mem unlocked.vs_memory mem ==>
     val_in_memory wrapped_tv wrapped_value (w2n source_w) mem` by metis_tac[] >>
  `val_footprint wrapped_tv wrapped_value=val_footprint physical_tv v` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`wrapped_value=ArrayV (TupleV [v])`,
       `type_memory_size wrapped_tv=type_memory_size physical_tv`,
       `val_footprint physical_tv v=type_memory_size physical_tv`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[loweringPostsTheory.val_footprint_def]) >>
  drule_all (Q.INST [`env` |-> `type_env tops`,`ty` |-> `TupleT [physical_ty]`,
    `ei` |-> `abi_ce.ce_ret_enc_info`,`tv` |-> `wrapped_tv`,`v` |-> `wrapped_value`,
    `av` |-> `wrapped_av`,`sb` |-> `w2n (source_w:bytes32)`,
    `tainted` |-> `unlock_tn.t_mem`,`initial_mem` |-> `unlocked.vs_memory`]
    abiEncoderSourceRobustTheory.abi_encoder_source_window_robust) >>
  disch_then (qx_choose_then `wrapped_ct` (qx_choose_then `wrapped_rv` strip_assume_tac)) >>
  `contractABI$enc wrapped_ct wrapped_rv=contractABI$enc
    (Tuple [vyper_to_abi_type (type_env tops) physical_ty]) (contractABI$ListV [abi_v])` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`contractABI$enc wrapped_ct wrapped_rv=_`,
       `wrapped_av=contractABI$ListV [abi_v]`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [vyperABITheory.vyper_to_abi_type_def]) >>
  `LENGTH (contractABI$enc wrapped_ct wrapped_rv)<=abi_ce.ce_max_return_size` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`LENGTH (contractABI$enc wrapped_ct wrapped_rv)<=_`,
       `vyper_abi_size_bound (type_env tops) (TupleT [physical_ty])<=abi_ce.ce_max_return_size`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!mem. mem_agree_outside unlock_tn.t_mem unlocked.vs_memory mem ==>
    abi_encoder_window_input abi_ce.ce_ret_enc_info wrapped_ct wrapped_rv
      (w2n source_w) (val_footprint physical_tv v) mem` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!mem. mem_agree_outside unlock_tn.t_mem unlocked.vs_memory mem ==>
         abi_encoder_window_input abi_ce.ce_ret_enc_info wrapped_ct wrapped_rv _ _ mem`,
       `val_footprint wrapped_tv wrapped_value=val_footprint physical_tv v`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  qexistsl_tac [`wrapped_ct`,`wrapped_rv`] >> asm_rewrite_tac[]
QED

Resume return_selected_valued_frag_full_core[buffered_shared_wrapped_packed]:
  drule_all abiEncoderLiveSourceTheory.abi_source_non_nominal_forms >>
  strip_tac
  >- suspend "buffered_shared_wrapped_bytes" >>
  suspend "buffered_shared_wrapped_string"
QED

Resume return_selected_valued_frag_full_core[buffered_shared_wrapped_bytes]:
  qpat_x_assum `physical_ty=BaseT (BytesT (Dynamic _))` SUBST_ALL_TAC >>
  qpat_x_assum `physical_tv=BaseTV (BytesT (Dynamic _))` SUBST_ALL_TAC >>
  qpat_x_assum `v=vyperValue$BytesV _` SUBST_ALL_TAC >>
  rename1 `value_has_type (BaseTV (BytesT (Dynamic packed_n))) (vyperValue$BytesV packed_bs)` >>
  `abi_ce.ce_ret_enc_info=AbiComplex
    [(AbiBytestring packed_n,32,type_memory_size (BaseTV (BytesT (Dynamic packed_n))),T)]` by
    (qpat_assum `abi_enc_plan (type_env tops)
       (TupleT [BaseT (BytesT (Dynamic packed_n))]) abi_ce.ce_ret_enc_info` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     ntac 3 (simp[Once abiEncoderPropsTheory.abi_enc_plan_cases,vyperABITheory.vyper_to_abi_type_def,
       vyperABITheory.vyper_base_to_abi_type_def,contractABITheory.is_dynamic_def,
       is_word_type_def,vyperValueTheory.evaluate_type_def]) >>
     strip_tac >> gvs[Once abiEncoderPropsTheory.abi_enc_plan_cases]) >>
  `abi_v=contractABI$BytesV (packed_bs)` by
    (qpat_assum `vyper_to_abi (type_env tops) (BaseT (BytesT (Dynamic packed_n)))
       (vyperValue$BytesV packed_bs)=SOME abi_v` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [vyperABITheory.vyper_to_abi_def,
       vyperABITheory.vyper_to_abi_base_def,optionTheory.SOME_11] >> metis_tac[]) >>
  qpat_assum `abi_v=contractABI$BytesV (packed_bs)` (fn av =>
    qpat_assum `LENGTH (contractABI$enc
      (Tuple [vyper_to_abi_type (type_env tops) (BaseT (BytesT (Dynamic packed_n)))])
      (contractABI$ListV [abi_v]))<=abi_ce.ce_max_return_size`
      (ASSUME_TAC o PURE_REWRITE_RULE [av,vyperABITheory.vyper_to_abi_type_def,
        vyperABITheory.vyper_base_to_abi_type_def])) >>
  qexistsl_tac [`Tuple [Bytes NONE]`,`contractABI$ListV [contractABI$BytesV packed_bs]`] >>
  PURE_REWRITE_TAC [vyperABITheory.vyper_to_abi_type_def,
    vyperABITheory.vyper_base_to_abi_type_def,loweringPostsTheory.val_footprint_def] >>
  asm_rewrite_tac[] >>
  rpt strip_tac >>
  mp_tac (Q.INST [`env` |-> `type_env tops`,
    `tv` |-> `BaseTV (BytesT (Dynamic packed_n))`,
    `v` |-> `vyperValue$BytesV packed_bs`,`n` |-> `packed_n`,`bs` |-> `packed_bs`,
    `sb` |-> `w2n (source_w:bytes32)`,`mem` |-> `mem`]
    abiEncoderWindowSourceTheory.abi_encoder_window_bytes_singleton_source) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [vyperABITheory.vyper_to_abi_def] >> metis_tac[]) >>
  simp_tac (srw_ss()) []
QED

Resume return_selected_valued_frag_full_core[buffered_shared_wrapped_string]:
  qpat_x_assum `physical_ty=BaseT (StringT _)` SUBST_ALL_TAC >>
  qpat_x_assum `physical_tv=BaseTV (StringT _)` SUBST_ALL_TAC >>
  qpat_x_assum `v=StringV _` SUBST_ALL_TAC >>
  rename1 `value_has_type (BaseTV (StringT packed_n)) (StringV packed_str)` >>
  `abi_ce.ce_ret_enc_info=AbiComplex
    [(AbiBytestring packed_n,32,type_memory_size (BaseTV (StringT packed_n)),T)]` by
    (qpat_assum `abi_enc_plan (type_env tops)
       (TupleT [BaseT (StringT packed_n)]) abi_ce.ce_ret_enc_info` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     ntac 4 (simp[Once abiEncoderPropsTheory.abi_enc_plan_cases,vyperABITheory.vyper_to_abi_type_def,
       vyperABITheory.vyper_base_to_abi_type_def,contractABITheory.is_dynamic_def,
       is_word_type_def,vyperValueTheory.evaluate_type_def]) >>
     strip_tac >> gvs[Once abiEncoderPropsTheory.abi_enc_plan_cases]) >>
  `abi_v=contractABI$BytesV (MAP n2w_o_ORD packed_str)` by
    (qpat_assum `vyper_to_abi (type_env tops) (BaseT (StringT packed_n))
       (StringV packed_str)=SOME abi_v` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [vyperABITheory.vyper_to_abi_def,
       vyperABITheory.vyper_to_abi_base_def,optionTheory.SOME_11] >> metis_tac[]) >>
  qpat_assum `abi_v=contractABI$BytesV (MAP n2w_o_ORD packed_str)` (fn av =>
    qpat_assum `LENGTH (contractABI$enc
      (Tuple [vyper_to_abi_type (type_env tops) (BaseT (StringT packed_n))])
      (contractABI$ListV [abi_v]))<=abi_ce.ce_max_return_size`
      (ASSUME_TAC o PURE_REWRITE_RULE [av,vyperABITheory.vyper_to_abi_type_def,
        vyperABITheory.vyper_base_to_abi_type_def])) >>
  qexistsl_tac [`Tuple [String]`,
    `contractABI$ListV [contractABI$BytesV (MAP n2w_o_ORD packed_str)]`] >>
  PURE_REWRITE_TAC [vyperABITheory.vyper_to_abi_type_def,
    vyperABITheory.vyper_base_to_abi_type_def,loweringPostsTheory.val_footprint_def] >>
  asm_rewrite_tac[] >>
  rpt strip_tac >>
  mp_tac (Q.INST [`env` |-> `type_env tops`,`tv` |-> `BaseTV (StringT packed_n)`,
    `v` |-> `StringV packed_str`,`n` |-> `packed_n`,
    `bs` |-> `MAP n2w_o_ORD packed_str`,
    `sb` |-> `w2n (source_w:bytes32)`,`mem` |-> `mem`]
    abiEncoderWindowSourceTheory.abi_encoder_window_string_singleton_source) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [vyperABITheory.vyper_to_abi_def] >> metis_tac[]) >>
  simp_tac (srw_ss()) []
QED


Resume return_selected_valued_frag_full_core[word_terminal]:
  `compile_external_return (SOME op) T F ce.ce_ret_enc_info
     ce.ce_max_return_size nr nkey ut (mut = View) sm = ((),sb)` by
    (qpat_assum `stmt_env ce lctx ret (Return (SOME e)) sa = _` mp_tac >>
     simp_tac (srw_ss()) [stmt_env_def, declare_stmt_local_def,
       Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`lower_value compile_expr ce ret e sa = (op,sm)`,
        `is_word_type ret`, `~ce.ce_raw_return`, `ce.ce_return_pc = NONE`,
        `ce.ce_nonreentrant = (nr,nkey,ut,mut = View)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 5 disch_tac >>
     asm_simp_tac (srw_ss()) [comp_bind_def, comp_return_def, LET_THM] >>
     Cases_on `compile_external_return (SOME op) T F ce.ce_ret_enc_info
       ce.ce_max_return_size nr nkey ut (mut = View) sm` >> simp[]) >>
  `post_value_type ce e = ret` by metis_tac[type_widens_to_word] >>
  `(!x. op = Var x ==> not_fresh_at sm x)` by
    metis_tac[compile_lower_value_var] >>
  `fn_has_code sm sb func` by metis_tac[fn_has_code_split] >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `?tv. evaluate_type (type_env tops) ret = SOME tv /\
        safe_cast tv v = SOME v /\
        eval_operand op t = SOME (typed_val_to_w256 tv v)` by
    (fs[expr_val_rel_def] >> metis_tac[]) >>
  suspend "word_resources"
QED

Resume return_selected_valued_frag_full_core[word_resources]:
  `32 < dimword (:256)` by
    simp_tac (srw_ss()) [wordsTheory.dimword_def,
      fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  qpat_assum `ghost_inv_at _ lo d ce cx mid G1 tn1 t`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  qpat_assum `stmt_state_rel _ ctx func ce cx mid t`
    (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def]) >>
  `op_taint tn1 op = {}` by fs[ptr_val_ok_def] >>
  `compile_external_return (SOME op) T F ce.ce_ret_enc_info
    ce.ce_max_return_size nr nkey T (mut = View) sm = ((),sb)` by
    (`nr /\ ~(mut = View) ==> ut` by simp[] >>
     pop_assum (ONCE_REWRITE_TAC o single o GSYM o
       MATCH_MP valued_return_compiler_transient) >>
     first_assum ACCEPT_TAC) >>
  `nr /\ mut <> View ==> ~t.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def,loweringStateRelDefsTheory.state_rel_def,loweringStateRelDefsTheory.call_ctx_rel_def] >>
  qpat_assum `compile_external_return _ T F _ _ nr _ T _ sm = _`
    (strip_assume_tac o MATCH_MP (SPEC_ALL compile_external_return_unlock)) >>
  `st1.cs_next_id = sm.cs_next_id + (if nr /\ mut <> View then 1 else 0) /\
    cs_extends sm st1` by
    (mp_tac (Q.INST [`st` |-> `sm`,`st'` |-> `st1`,`ut` |-> `T`,
       `iv` |-> `mut = View`] (SPEC_ALL optional_unlock_code)) >>
     impl_tac >- asm_rewrite_tac[] >>
     Cases_on `nr /\ mut <> View` >> ASM_REWRITE_TAC[] >>
     disch_then SUBST1_TAC >> simp[cs_extends_refl] >>
     irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends st1 sb` by
    (qpat_assum `compile_external_return _ T F _ _ F _ T _ st1 = _`
       (ACCEPT_TAC o MATCH_MP valued_return_code_extends)) >>
  `fn_has_code st1 sb func` by
    (mp_tac (Q.SPECL [`sm`,`st1`,`sb`,`func`] fn_has_code_split) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  qpat_assum `compile_external_return _ T F _ _ F _ T _ st1 = _`
    (mp_tac o MATCH_MP (REWRITE_RULE [] (Q.INST [`nr` |-> `F`]
      (SPEC_ALL compile_external_return_word_parts)))) >>
  strip_tac >>
  `MEM (mk_inst st1.cs_next_id ALLOCA [Lit 32w] [buf]) (fn_insts func)` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
     drule_all fragFuelTheory.lookup_block_get_instruction_fn_insts >>
     disch_then ACCEPT_TAC) >>
  `(!b sz. FLOOKUP t.vs_allocas
      (sm.cs_next_id + (if nr /\ mut <> View then 1 else 0)) =
      SOME (b,sz) ==> sz = 32)` by
    (rpt gen_tac >> strip_tac >>
     metis_tac[stmt_state_rel_alloca_site_bound]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t /\
    t.vs_alloca_next + pending_alloca_size func t <= w2n t.vs_initial_fmp` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx mid t` (fn related =>
       mp_tac (MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp related) >>
       mp_tac (MATCH_MP stateRelProjTheory.stmt_state_rel_fmp_room related)) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[exprLoweringPropsTheory.fmp_room_def] >> decide_tac) >>
  mp_tac (Q.INST [`ei` |-> `ce.ce_ret_enc_info`,
      `msz` |-> `ce.ce_max_return_size`,`iv` |-> `mut = View`,
      `st` |-> `sm`,`st'` |-> `sb`,`x` |-> `()`,
      `s` |-> `t`,`w` |-> `typed_val_to_w256 tv v`,
      `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
      `cenv` |-> `ce`,`PG` |-> `PG`,`G` |-> `G1`,`tn` |-> `tn1`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] compile_external_return_word_unlock_joint))) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> suspend "word_finish"
QED

Resume return_selected_valued_frag_full_core[word_finish]:
  rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (ReturnException v)`,`mid`,`Halt ss`,`G'`,`tn'`] >>
  conj_tac
  >- simp[vyperStateTheory.raise_def, gas_explicit_def] >>
  conj_tac
  >- (qpat_assum `cx = initial_evaluation_context am.sources am.layouts tx NONE`
        (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
      first_assum ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `cx = initial_evaluation_context am.sources am.layouts tx NONE`
      (fn th => PURE_ONCE_REWRITE_TAC [th]) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
      (strip_assume_tac o BETA_RULE o MATCH_MP th)) >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (t,G1,tn1) [] (Halt ss,G',tn')` by
    (first_assum (qspec_then `H` MATCH_MP_TAC) >>
     metis_tac[ghost_inv_at_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[NoAsms, fragExecTheory.exit_result_def, stmt_exit_ptr_def,
    expr_exit_def, halt_exit_def] >>
  reverse conj_tac >-
    (qpat_assum `gas_origin_ptr_path _ _ _ (Halt _,_,_)`
       (ACCEPT_TAC o MATCH_MP bodyFullIntCallReturnHaltTheory.gas_origin_ptr_path_halt_fmp)) >>
  qx_gen_tac `tail` >> suspend "word_post"
QED

Resume return_selected_valued_frag_full_core[word_post]:
  `state_rel H func ce cx mid t` by
    (qpat_assum `expr_post H ctx func ce cx e es sa sm s0 mid _ op t`
      (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [stmt_state_rel_def] o
       CONJUNCT1 o REWRITE_RULE [expr_post_def])) >>
  `~lookup_raw_return_or_F (NONE:num option) tx.function_name External tops` by
    (qpat_assum `ce.ce_raw_return = lookup_raw_return_or_F
       (NONE:num option) tx.function_name External tops`
      (fn th => qpat_assum `~ce.ce_raw_return`
        (ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
  qspecl_then [`tops`,`type_env tops`,`ret`,`tv`,`v`,`v`] mp_tac
    return_bytes_prim_value >> impl_tac >- simp[] >> strip_tac >>
  `return_bytes tops ret v ss.vs_returndata` by simp[] >>
  `?us. unlock_if_nr cx nr (is_view_mut mut)
    (mid with <|scopes := []; gas_obs := tail|>) = (INL (),us) /\
    external_call_result_rel H tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state am.sources am.exports am.layouts us),
       us.requests) (Halt ss)` by
    (match_mp_tac (Q.INST
       [`func` |-> `func`, `ce` |-> `ce`, `nkey` |-> `nkey`,
        `t` |-> `t`] valued_return_result_unlock) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     FIRST [
       qpat_assum `nr /\ mut <> View ==> ut /\ _`
         (fn th => disch_then (ACCEPT_TAC o cj 3 o MATCH_MP th)),
       qpat_assum `~lookup_raw_return_or_F _ _ _ _`
         (fn th => simp[NoAsms, th]) >> first_assum ACCEPT_TAC]) >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`tv`,`v`,`us`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`unlock_if_nr cx nr (is_view_mut mut) _ = (INL (),us)`,
     `nr /\ mut <> View ==> ut /\ _`, `cx.txn.target = tx.target`,
     `nkey = nkey_map tx.function_name`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  Cases_on `nr` >> Cases_on `mut` >>
  gvs[unlock_if_nr_def, vyperInterpreterTheory.is_view_mut_def]
QED

Resume return_selected_valued_frag_full_core[raw_typed_copy]:
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) ret` by
    (qpat_assum `IS_SOME (type_stmt env ret (Return (SOME e)))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()]) >>
  `is_bytestring_type ret /\ ~is_word_type ret` by
    simp[is_bytestring_type_def, is_word_type_def] >>
  `is_bytestring_type (expr_type e)` by
    metis_tac[vyperTypeSystemTheory.type_widens_to_def,
              compileEnvTheory.arg_type_fits_bytestring_source] >>
  `is_bytestring_type (lowered_value_type ce e)` by
    (Cases_on `?ann ctgt cargs drv. e = Call ann ctgt cargs drv`
     >- (gvs[] >> rename1 `well_typed_expr env (Call ann ctgt cargs drv)` >>
         Cases_on `ctgt` >>
         fs[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def] >>
         rename1 `well_typed_expr env (Call ann (IntCall fid) cargs drv)` >>
         mp_tac (Q.INST [`ce` |-> `ce`,
           `cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`,
           `env` |-> `env`, `es` |-> `es`, `ty` |-> `ann`,
           `fid` |-> `fid`, `args` |-> `cargs`, `drv` |-> `drv`]
           return_intcall_lowered_widens) >>
         impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
         fs[exprLoweringTheory.lowered_value_type_def, vyperTypeSystemTheory.type_widens_to_def,
            vyperASTTheory.expr_type_def] >>
         metis_tac[compileEnvTheory.arg_type_fits_bytestring_source]) >>
     `!ann ctgt cargs drv. e <> Call ann ctgt cargs drv` by metis_tac[] >>
     drule_all lowered_value_type_bytestring_iff >> simp[]) >>
  `(!x. op = Var x ==> not_fresh_at sm x)` by metis_tac[compile_lower_value_var] >>
  `fn_has_code sm sb func` by metis_tac[fn_has_code_split] >>
  Cases_on `(if nr then compile_nonreentrant_unlock nkey ut (mut = View)
             else comp_return ()) sm` >>
  rename1 `(if nr then compile_nonreentrant_unlock nkey ut (mut = View)
            else comp_return ()) sm = (ur,su)` >>
  Cases_on `ur` >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce ret) su` >>
  rename1 `compile_alloc_buffer (type_memory_bytes ce ret) su = (raw_buf,sr)` >>
  Cases_on `compile_store_memory_typed ce raw_buf.buf_operand ret op
    (lowered_value_type ce e) sr` >>
  rename1 `compile_store_memory_typed ce raw_buf.buf_operand ret op
    (lowered_value_type ce e) sr = (copy_result,sc)` >>
  Cases_on `copy_result` >>
  `compile_external_return (SOME raw_buf.buf_operand) F T ce.ce_ret_enc_info
     ce.ce_max_return_size F nkey ut (mut = View) sc = ((),sb)` by
    (qpat_assum `stmt_env ce lctx ret (Return (SOME e)) sa = _` mp_tac >>
     qpat_assum `lower_value compile_expr ce ret e sa = _` mp_tac >>
     qpat_assum `(if nr then compile_nonreentrant_unlock nkey ut (mut = View)
                  else comp_return ()) sm = ((),su)` mp_tac >>
     qpat_assum `compile_alloc_buffer _ su = _` mp_tac >>
     qpat_assum `compile_store_memory_typed _ _ _ _ _ sr = _` mp_tac >>
     qpat_assum `ret = BaseT (BytesT (Dynamic _))` mp_tac >>
     qpat_assum `ce.ce_nonreentrant = _` mp_tac >>
     qpat_assum `ce.ce_return_pc = NONE` mp_tac >>
     qpat_assum `ce.ce_raw_return` mp_tac >>
     qpat_assum `is_bytestring_type (lowered_value_type ce e)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[stmt_env_def, declare_stmt_local_def, Once compile_stmt_def,
       is_word_type_def, is_bytestring_type_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
     Cases_on `compile_external_return (SOME raw_buf.buf_operand) F T ce.ce_ret_enc_info
       ce.ce_max_return_size F nkey ut (mut = View) sc` >>
     gvs[pairTheory.UNCURRY]) >>
  suspend "raw_allocation"
QED

Resume return_selected_valued_frag_full_core[raw_allocation]:
  `type_memory_bytes ce ret < 2 ** 64` by
    (irule return_selected_lookup_size >> metis_tac[]) >>
  `type_memory_bytes ce ret < dimword (:256)` by
    (qpat_assum `type_memory_bytes ce ret < 2 ** 64` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp_tac (srw_ss()) [wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >> decide_tac) >>
  `ci_mono su sr` by
    (qspecl_then [`type_memory_bytes ce ret`,`su`] mp_tac
      ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sr sc` by
    (qspecl_then [`ce`,`raw_buf.buf_operand`,`ret`,`op`,
       `lowered_value_type ce e`,`sr`] mp_tac
      (cj 1 ci_mono_typed_memory_family) >> simp[]) >>
  `ci_mono sc sb` by
    (qspecl_then [`SOME raw_buf.buf_operand`,`F`,`T`,`ce.ce_ret_enc_info`,
       `ce.ce_max_return_size`,`F`,`nkey`,`ut`,`mut = View`,`sc`] mp_tac
      (cj 3 ci_mono_return_helpers) >> simp[]) >>
  `cs_extends su sr /\ cs_extends sr sc /\ cs_extends sc sb` by
    (rpt conj_tac >> first_assum
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [ci_mono_def])) >>
  suspend "raw_unlock"
QED

Resume return_selected_valued_frag_full_core[raw_unlock]:
  `nr /\ mut <> View ==> ut` by
    (qpat_assum `nr /\ mut <> View ==> ut /\ _`
      (fn th => disch_then (ACCEPT_TAC o CONJUNCT1 o MATCH_MP th))) >>
  `cs_extends sm su /\ su.cs_next_var = sm.cs_next_var` by
    (mp_tac (Q.INST [`st` |-> `sm`,`st'` |-> `su`,
       `iv` |-> `mut = View`] (SPEC_ALL optional_unlock_code)) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     Cases_on `nr /\ mut <> View` >>
     pop_assum (fn th => simp[NoAsms, th]) >> disch_then SUBST1_TAC >>
     simp[NoAsms, cs_extends_refl] >>
     irule cs_extends_same_block >> simp[NoAsms, rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sm su func /\ fn_has_code su sr func /\
   fn_has_code sr sc func /\ fn_has_code sc sb func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspecl_then [`ce`,`ret`,`e`,`sa`] mp_tac
      (cj 2 ci_mono_compile_expr_sa) >> simp[ci_mono_def]) >>
  `local_ptrs_reserved ce su` by metis_tac[local_ptrs_reserved_next_var] >>
  qpat_assum `ghost_inv_at _ lo d ce cx mid G1 tn1 t`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  qpat_assum `expr_post _ ctx func ce cx e es sa sm s0 mid v op t`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `(if nr then compile_nonreentrant_unlock nkey T (mut = View)
    else comp_return ()) sm = ((),su)` by
    (qpat_assum `nr /\ mut <> View ==> ut` mp_tac >>
     qpat_assum `(if nr then compile_nonreentrant_unlock nkey ut (mut = View)
                  else comp_return ()) sm = ((),su)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `nr` >> Cases_on `mut = View` >>
     gvs[contextTheory.compile_nonreentrant_unlock_def]) >>
  `nr /\ mut <> View ==> ~t.vs_call_ctx.cc_static /\ allocas_from lo t` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`nr /\ mut <> View ==> ut /\ _`, `allocas_from lo t`,
        `stmt_state_rel _ ctx func ce cx mid t`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
       loweringStateRelDefsTheory.call_ctx_rel_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx _ t`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  mp_tac (Q.INST [`iv` |-> `mut = View`,`st` |-> `sm`,`st'` |-> `su`,
      `s` |-> `t`,`G` |-> `G1`,`tn` |-> `tn1`]
    (SPEC_ALL optional_transient_unlock_paths_joint)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`raw_u`,`raw_utn`] strip_assume_tac) >>
  suspend "raw_unlocked_allocation"
QED

Resume return_selected_valued_frag_full_core[raw_unlocked_allocation]:
  `?prepared_es. unlock_if_nr cx nr (is_view_mut mut) mid = (INL (),prepared_es)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rewrite_tac[unlock_if_nr_def] >>
     IF_CASES_TAC >-
       (Cases_on `cx.nonreentrant_slot` >>
        simp[vyperStateTheory.return_def,
          nonreentrantEquivTheory.release_nonreentrant_lock_execution]) >>
     simp[vyperStateTheory.return_def]) >>
  rename1 `unlock_if_nr cx nr (is_view_mut mut) mid = (INL (),prepared_es)` >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace)
     ctx func ce cx prepared_es raw_u` by
    (match_mp_tac (Q.INST [`es` |-> `mid`, `s` |-> `t`,
       `iv` |-> `is_view_mut mut`, `n` |-> `LENGTH su.cs_current_insts`]
       (SPEC_ALL optional_transient_unlock_stmt_state_rel)) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`unlock_if_nr cx nr _ mid = _`, `nr ==> _`,
        `nr /\ mut <> View ==> ut /\ _`, `raw_u = _`,
        `stmt_state_rel _ ctx func ce cx mid t`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `nr` >> gvs[]) >>
  `allocas_from lo raw_u /\ lo <= raw_u.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`allocas_from lo t`, `lo <= t.vs_alloca_next`,
        `raw_u.vs_allocas = t.vs_allocas`, `raw_u.vs_alloca_next = t.vs_alloca_next`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ptrDisciplineTheory.allocas_from_def]) >>
  `alloca_inv t` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx mid t` mp_tac >>
     simp[NoAsms, stmt_state_rel_def]) >>
  `!u. gas_path_mem ctx func t 0 (OK u) ==> alloca_inv u` by
    (rpt strip_tac >>
     irule bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  `alloca_history func raw_u` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`fn_inst_ids_distinct func`,`alloca_history func t`,
        `gas_path_mem ctx func t 0 (OK raw_u)`,
        `!u. gas_path_mem ctx func t 0 (OK u) ==> alloca_inv u`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     metis_tac[fragGasPathFrameMemTheory.gas_path_mem_zero_history]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp raw_u)` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx _ raw_u`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  qpat_assum `stmt_state_rel _ ctx func ce cx prepared_es raw_u`
    (fn pre =>
      let
        val target_h = hd (snd (strip_comb (concl pre)))
        val alloc_th = bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path
        val (_,packet) = strip_exists (snd (dest_imp (concl alloc_th)))
        val frame_h = fst (dest_forall (List.nth (strip_conj packet,6)))
      in
        drule_all (Q.INST
          [`G` |-> `G1`,`tn` |-> `raw_utn`,
           `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
          (INST_TYPE (match_type (type_of frame_h) (type_of target_h)) alloc_th))
      end) >>
  disch_then (qspecl_then [`shadow_ctx`,`raw_utn`,`PG`,`G1`]
    (qx_choosel_then [`raw_dst`,`raw_w`,`raw_alloc`,`raw_G`,`raw_tn`]
      strip_assume_tac)) >>
  suspend "raw_copy_resources"
QED

Resume return_selected_valued_frag_full_core[raw_copy_resources]:
  rename1 `raw_buf.buf_operand = Var raw_dst` >>
  rename1 `lookup_var raw_dst raw_alloc = SOME raw_w` >>
  rename1 `ptr_covers raw_G raw_tn raw_dst raw_alloc (type_memory_bytes ce ret)` >>
  `?bs. v = BytesV bs` by
    (qpat_assum `ret = BaseT (BytesT (Dynamic _))` mp_tac >>
     qpat_assum `evaluate_type (type_env tops) ret = SOME dtv` mp_tac >>
     qpat_assum `value_has_type dtv v` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[vyperValueTheory.evaluate_type_def] >> Cases_on `v` >>
     gvs[vyperTypingTheory.value_has_type_def]) >>
  `post_value_type ce e = expr_type e` by simp[] >>
  `evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv` by metis_tac[] >>
  `?source_w. eval_operand op t = SOME source_w` by fs[expr_val_rel_def] >>
  `ptv <> BaseTV AddressT /\ (!k. ptv <> BaseTV (BytesT (Fixed k)))` by
    (qspecl_then [`get_tenv cx`,`post_value_type ce e`,`ptv`] mp_tac
       valueCopyBytesTheory.bytestring_type_value >>
     simp[] >> strip_tac >> simp[]) >>
  suspend "raw_padded_resources"
QED

Resume return_selected_valued_frag_full_core[raw_padded_resources]:
  `~is_word_type (post_value_type ce e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  rev_drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)
    expr_val_at_raw_return_resources >>
  disch_then (qspecl_then [`post_value_type ce e`,`sa`,`sm`,`v`,`op`,
    `ptv`,`source_w`,`G1`,`tn1`,`LENGTH bs`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `val_store_size ptv v = val_store_size dtv v` by
    (qspecl_then [`type_env tops`,`post_value_type ce e`,`ret`,`ptv`,`dtv`,`v`]
       mp_tac valueCopyBytesTheory.bytestring_val_store_size_eq >> simp[]) >>
  `val_store_size dtv v = 32 + 32 * word_size (LENGTH bs)` by
    (qpat_assum `ret = BaseT (BytesT (Dynamic _))` mp_tac >>
     qpat_assum `evaluate_type (type_env tops) ret = SOME dtv` mp_tac >>
     qpat_assum `v = BytesV bs` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[vyperValueTheory.evaluate_type_def,exprSimPropsTheory.val_store_size_def]) >>
  suspend "raw_padded_cover"
QED

Resume return_selected_valued_frag_full_core[raw_padded_cover]:
  rename1 `op = Var raw_src` >>
  `type_memory_bytes ce ret = type_memory_size dtv` by
    (qpat_assum `ret = BaseT (BytesT (Dynamic _))` mp_tac >>
     qpat_assum `evaluate_type (type_env tops) ret = SOME dtv` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[typeLayoutPropsTheory.type_memory_bytes_base_evaluated]) >>
  `val_store_size ptv v <= type_memory_bytes ce ret` by
    metis_tac[exprSimPropsTheory.val_store_size_le] >>
  `val_wf ptv v` by
    metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `32 + LENGTH bs <= val_footprint ptv v` by
    metis_tac[raw_val_footprint_covers] >>
  `val_footprint ptv v <> 0` by decide_tac >>
  `ptr_mem_ok cx (post_value_type ce e) v op G1 tn1 t /\
   op_taint tn1 op = {}` by
    (qpat_assum `ptr_val_ok cx (post_value_type ce e) v op G1 tn1 t` mp_tac >>
     qpat_assum `~is_word_type (post_value_type ce e)` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[ptr_val_ok_def]) >>
  `?p. op = Var p /\ ptr_covers G1 tn1 p t (val_store_size ptv v)` by
    metis_tac[ptr_mem_ok_read_covers,arithmeticTheory.LESS_EQ_REFL] >>
  `ptr_covers G1 tn1 raw_src t (32 + 32 * word_size (LENGTH bs))` by
    (qpat_assum `ptr_covers G1 tn1 _ t (val_store_size ptv v)` mp_tac >>
     qpat_assum `val_store_size ptv v = val_store_size dtv v` mp_tac >>
     qpat_assum `val_store_size dtv v = 32 + 32 * word_size (LENGTH bs)` mp_tac >>
     qpat_assum `op = Var raw_src` mp_tac >>
     qpat_assum `op = Var _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]) >>
  `evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
   ~is_word_type (post_value_type ce e)` by metis_tac[] >>
  `w2n source_w + (32 + 32 * word_size (LENGTH bs)) <= t.vs_alloca_next` by
    (qpat_assum `expr_store_bound cx (post_value_type ce e) v op t` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv` mp_tac >>
     qpat_assum `~is_word_type (post_value_type ce e)` mp_tac >>
     qpat_assum `eval_operand op t = SOME source_w` mp_tac >>
     qpat_assum `val_store_size ptv v = val_store_size dtv v` mp_tac >>
     qpat_assum `val_store_size dtv v = 32 + 32 * word_size (LENGTH bs)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     qpat_assum `expr_store_bound cx (post_value_type ce e) v op t`
       (mp_tac o REWRITE_RULE [exprSimMemDefsTheory.expr_store_bound_def]) >>
     disch_then (qspecl_then [`ptv`,`source_w`] mp_tac) >> simp[]) >>
  suspend "raw_copy_prepare"
QED

Resume return_selected_valued_frag_full_core[raw_copy_prepare]:
  `not_fresh_at sm raw_src` by metis_tac[] >>
  `not_fresh_at sr raw_src` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono,ci_mono_def] >>
  `compile_store_bytestring (Var raw_src) (Var raw_dst) sr = ((),sc)` by
    (qpat_assum `compile_store_memory_typed ce raw_buf.buf_operand ret op
       (lowered_value_type ce e) sr = ((),sc)` mp_tac >>
     qpat_assum `is_bytestring_type ret` mp_tac >>
     qpat_assum `is_bytestring_type (lowered_value_type ce e)` mp_tac >>
     qpat_assum `raw_buf.buf_operand = Var raw_dst` mp_tac >>
     qpat_assum `op = Var raw_src` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     mp_tac (Q.INST
       [`dst_ty` |-> `ret`, `src_ty` |-> `lowered_value_type ce e`,
        `cenv` |-> `ce`, `dst` |-> `raw_buf.buf_operand`, `src` |-> `op`]
       typedCopyAgreementTheory.compile_store_memory_typed_bytes) >>
     impl_tac >- simp[] >> disch_tac >> gvs[]) >>
  `not_fresh_at su raw_src` by
    (qpat_assum `su.cs_next_var = sm.cs_next_var` mp_tac >>
     qpat_assum `not_fresh_at sm raw_src` mp_tac >>
     simp[NoAsms, loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `raw_alloc.vs_memory = t.vs_memory /\ ~raw_alloc.vs_halted` by
    (qpat_assum `raw_alloc with <| vs_vars := raw_u.vs_vars;
       vs_allocas := raw_u.vs_allocas; vs_alloca_next := raw_u.vs_alloca_next;
       vs_inst_idx := raw_u.vs_inst_idx |> = raw_u`
       (mp_tac o AP_TERM ``\z:venom_state. (z.vs_memory,z.vs_halted)``) >>
     qpat_assum `raw_u.vs_memory = t.vs_memory` mp_tac >>
     qpat_assum `~raw_u.vs_halted` mp_tac >>
     simp[NoAsms] >> metis_tac[]) >>
  `lookup_var raw_src raw_alloc = SOME source_w /\
   FLOOKUP raw_G raw_src = FLOOKUP G1 raw_src /\
   op_taint raw_tn (Var raw_src) = op_taint tn1 (Var raw_src)` by
    (qpat_assum `!x. not_fresh_at su x ==> lookup_var x raw_alloc = _ /\ _`
       (qspec_then `raw_src` mp_tac) >>
     map_every (fn pat => qpat_assum pat (qspec_then `Var raw_src` mp_tac))
       [`!op. eval_operand op raw_u = eval_operand op t`,
        `!op. op_taint raw_utn op = op_taint tn1 op`] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`not_fresh_at su raw_src`, `lookup_var raw_src t = SOME source_w`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  suspend "raw_copy_memory"
QED

Resume return_selected_valued_frag_full_core[raw_copy_memory]:
  `ptr_covers raw_G raw_tn raw_src raw_alloc
      (32 + 32 * word_size (LENGTH bs))` by
    (qpat_assum `ptr_covers G1 tn1 raw_src t
       (32 + 32 * word_size (LENGTH bs))` mp_tac >>
     qpat_assum `lookup_var raw_src raw_alloc = SOME source_w` mp_tac >>
     qpat_assum `lookup_var raw_src t = SOME source_w` mp_tac >>
     qpat_assum `FLOOKUP raw_G raw_src = FLOOKUP G1 raw_src` mp_tac >>
     qpat_assum `op_taint raw_tn (Var raw_src) = op_taint tn1 (Var raw_src)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ptr_covers_def]) >>
  `32 + 32 * word_size (LENGTH bs) <= type_memory_bytes ce ret` by
    metis_tac[] >>
  `ptr_covers raw_G raw_tn raw_dst raw_alloc
      (32 + 32 * word_size (LENGTH bs))` by
    metis_tac[reasonCopySourcePtrTheory.ptr_covers_mono] >>
  `32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
   LENGTH bs + 31 < dimword (:256)` by
    (qspec_then `LENGTH bs` assume_tac exprSimPropsTheory.le_word_size_mul >>
     decide_tac) >>
  `mload (w2n source_w) raw_alloc = n2w (LENGTH bs)` by
    metis_tac[valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `w2n source_w + (32 + 32 * word_size (LENGTH bs)) <=
       raw_alloc.vs_alloca_next /\
   w2n raw_w + (32 + 32 * word_size (LENGTH bs)) <=
       raw_alloc.vs_alloca_next` by decide_tac >>
  `!i. w2n source_w <= i /\ i < w2n source_w + 32 + LENGTH bs ==>
       i NOTIN raw_tn.t_mem` by
    (qpat_assum `!i. i IN raw_tn.t_mem <=> _` mp_tac >>
     qpat_assum `!i. w2n source_w <= i /\
       i < w2n source_w + 32 + LENGTH bs ==> i NOTIN tn1.t_mem` mp_tac >>
     qpat_assum `w2n source_w + (32 + 32 * word_size (LENGTH bs)) <=
       t.vs_alloca_next` mp_tac >>
     qpat_assum `raw_u.vs_alloca_next = t.vs_alloca_next` mp_tac >>
     qpat_assum `raw_utn.t_mem = tn1.t_mem` mp_tac >>
     qspec_then `LENGTH bs` mp_tac exprSimPropsTheory.le_word_size_mul >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qpat_assum `!j. j IN raw_tn.t_mem <=> _` (qspec_then `i` mp_tac) >>
     qpat_assum `!j. _ ==> j NOTIN tn1.t_mem` (qspec_then `i` mp_tac) >>
     impl_tac >- decide_tac >> simp[] >> decide_tac) >>
  suspend "raw_copy_path"
QED

Resume return_selected_valued_frag_full_core[raw_copy_path]:
  `!x. Var raw_src = Var x \/ Var raw_dst = Var x ==> not_fresh_at sr x` by
    (qpat_assum `not_fresh_at sr raw_src` mp_tac >>
     qpat_assum `not_fresh_at sr raw_dst` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]) >>
  `eval_operand (Var raw_src) raw_alloc = SOME source_w /\
   eval_operand (Var raw_dst) raw_alloc = SOME raw_w` by
    simp[venomStateTheory.eval_operand_def] >>
  `run_inst_seq_mem_ok (emitted_insts sr sc) raw_alloc` by
    (mp_tac (Q.INST
       [`src` |-> `Var raw_src`, `dst` |-> `Var raw_dst`,
        `sa` |-> `sr`, `sb` |-> `sc`, `s` |-> `raw_alloc`,
        `w` |-> `source_w`, `d` |-> `raw_w`, `len` |-> `LENGTH (bs:byte list)`]
       bodyCopyMemoryBaseTheory.compile_store_bytestring_body_mem_ok) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  qspecl_then [`Var raw_src`,`Var raw_dst`,`sr`,`sc`] mp_tac
    exprSimBufferStoreTheory.buffer_store_bytestring_shape >>
  simp[] >> strip_tac >>
  `?raw_bb. lookup_block raw_alloc.vs_current_bb func.fn_blocks = SOME raw_bb /\
    isPREFIX (emitted_insts sr sc)
      (DROP raw_alloc.vs_inst_idx raw_bb.bb_instructions)` by
    (qpat_assum `fn_has_code sr sc func` mp_tac >>
     qpat_assum `same_blocks sr sc` mp_tac >>
     qpat_assum `sc.cs_current_insts = sr.cs_current_insts ++ emitted_insts sr sc` mp_tac >>
     qpat_assum `raw_alloc.vs_current_bb = sr.cs_current_bb` mp_tac >>
     qpat_assum `raw_alloc.vs_inst_idx = LENGTH sr.cs_current_insts` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[fn_has_code_def,same_blocks_def] >>
     rename1 `lookup_block sc.cs_current_bb func.fn_blocks = SOME raw_code_bb` >>
     qexists_tac `raw_code_bb` >> conj_tac >- metis_tac[] >>
     simp[] >>
     qpat_x_assum `isPREFIX sc.cs_current_insts raw_code_bb.bb_instructions`
       (strip_assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM listTheory.APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND] >>
     metis_tac[]) >>
  suspend "raw_copy_joint"
QED

Resume return_selected_valued_frag_full_core[raw_copy_joint]:
  `lo <= raw_alloc.vs_alloca_next /\ ~raw_alloc.vs_halted` by
    (conj_tac >- decide_tac >> metis_tac[]) >>
  `32 + 32 * word_size (LENGTH bs) =
   32 + 32 * ((LENGTH bs + 31) DIV 32)` by
    simp[vfmConstantsTheory.word_size_def] >>
  `!i. w2n source_w <= i /\ i < w2n source_w + 32 ==>
       i NOTIN raw_tn.t_mem` by
    (rpt strip_tac >>
     qpat_assum `!i. w2n source_w <= i /\
       i < w2n source_w + 32 + LENGTH bs ==> i NOTIN raw_tn.t_mem`
       (qspec_then `i` mp_tac) >>
     impl_tac >- decide_tac >> simp[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp raw_alloc)` by
    (qpat_assum `!H'. stmt_state_rel H' ctx func ce cx prepared_es raw_u ==> _`
       (fn transfer => qpat_assum `stmt_state_rel _ ctx func ce cx prepared_es raw_u`
         (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp
          o MATCH_MP (SPEC_ALL transfer)))) >>
  qspecl_then [`lo`,`gas_explicit_sites ctx shadow_ctx`,`ctx`,`func`,`PG`,
    `sr`,`sc`,`raw_src`,`raw_dst`,`raw_G`,`raw_tn`,`raw_alloc`,
    `source_w`,`raw_w`,`LENGTH bs`,`32 + 32 * word_size (LENGTH bs)`,`raw_bb`]
    mp_tac bodyFullAllocGenericTheory.compile_store_bytestring_origin_ptr_path >>
  impl_tac
  >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `raw_copy_G` (qx_choose_then `raw_copy_tn`
    (qx_choose_then `raw_copy_state` strip_assume_tac))) >>
  suspend "raw_copy_finish_resources"
QED

Resume return_selected_valued_frag_full_core[raw_copy_finish_resources]:
  qspecl_then [`Var raw_src`,`Var raw_dst`,`sr`,`sc`,`raw_alloc`,
    `source_w`,`raw_w`,`LENGTH bs`] mp_tac
    exprSimBufferStoreTheory.buffer_store_bytestring_run >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `raw_frame_state` strip_assume_tac) >>
  `raw_frame_state = raw_copy_state` by
    (qpat_assum `run_inst_seq (emitted_insts sr sc) raw_alloc = OK raw_frame_state` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sr sc) raw_alloc = OK raw_copy_state` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  qpat_x_assum `raw_frame_state = raw_copy_state` SUBST_ALL_TAC >>
  `val_in_memory ptv v (w2n source_w) raw_alloc.vs_memory` by
    (qpat_assum `expr_val_rel cx (post_value_type ce e) v op t` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv` mp_tac >>
     qpat_assum `~is_word_type (post_value_type ce e)` mp_tac >>
     qpat_assum `eval_operand op t = SOME source_w` mp_tac >>
     qpat_assum `raw_alloc.vs_memory = t.vs_memory` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[expr_val_rel_def]) >>
  `val_footprint ptv v <= 32 + 32 * word_size (LENGTH bs)` by
    metis_tac[exprSimPropsTheory.val_footprint_le_store_size] >>
  `val_in_memory ptv v (w2n raw_w) raw_copy_state.vs_memory` by
    (qpat_assum `raw_copy_state.vs_memory =
       (mcopy (w2n raw_w) (w2n source_w)
         (32 + 32 * word_size (LENGTH bs)) raw_alloc).vs_memory` SUBST1_TAC >>
     irule valueCopyTheory.mcopy_val_in_memory >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `w2n raw_w + val_footprint ptv v <= dimword (:256)` by decide_tac >>
  `is_bytestring_type (post_value_type ce e)` by
    (qpat_assum `post_value_type ce e = expr_type e`
       (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  qspecl_then [`get_tenv cx`,`post_value_type ce e`,`ptv`,`v`,
    `raw_w`,`raw_copy_state`] mp_tac rawReturnValueTheory.raw_return_value_read >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `raw_payload` strip_assume_tac) >>
  `raw_payload = bs` by
    (qpat_assum `raw_return_bytes v = SOME raw_payload` mp_tac >>
     qpat_assum `v = BytesV bs` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  qpat_x_assum `raw_payload = bs` SUBST_ALL_TAC >>
  suspend "raw_terminal_resources"
QED

Resume return_selected_valued_frag_full_core[raw_terminal_resources]:
  qabbrev_tac `raw_end = raw_copy_state with vs_inst_idx :=
    raw_alloc.vs_inst_idx + LENGTH (emitted_insts sr sc)` >>
  `raw_copy_state.vs_allocas = raw_alloc.vs_allocas /\
   raw_copy_state.vs_alloca_next = raw_alloc.vs_alloca_next /\
   raw_copy_state.vs_current_bb = raw_alloc.vs_current_bb /\
   raw_copy_state.vs_halted = raw_alloc.vs_halted` by
    (qpat_assum `raw_copy_state with <|vs_vars := raw_alloc.vs_vars;
       vs_memory := raw_alloc.vs_memory|> = raw_alloc`
       (mp_tac o AP_TERM ``\z:venom_state.
         (z.vs_allocas,z.vs_alloca_next,z.vs_current_bb,z.vs_halted)``) >> simp[]) >>
  `allocas_from lo raw_end /\ ~raw_end.vs_halted /\
   raw_end.vs_current_bb = sc.cs_current_bb /\
   raw_end.vs_inst_idx = LENGTH sc.cs_current_insts` by
    (qpat_assum `allocas_from lo raw_alloc` mp_tac >>
     qpat_assum `~raw_alloc.vs_halted` mp_tac >>
     qpat_assum `same_blocks sr sc` mp_tac >>
     qpat_assum `sc.cs_current_insts = sr.cs_current_insts ++ emitted_insts sr sc` mp_tac >>
     simp[Abbr `raw_end`,ptrDisciplineTheory.allocas_from_def,same_blocks_def] >>
     fs[ptrDisciplineTheory.allocas_from_def,same_blocks_def] >>
     first_assum ACCEPT_TAC) >>
  `not_fresh_at sc raw_dst` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono,ci_mono_def] >>
  `lookup_var raw_dst raw_copy_state = lookup_var raw_dst raw_alloc /\
   FLOOKUP raw_copy_G raw_dst = FLOOKUP raw_G raw_dst /\
   op_taint raw_copy_tn (Var raw_dst) = op_taint raw_tn (Var raw_dst)` by
    (qpat_assum `!p. not_fresh_at sr p ==>
       lookup_var p raw_copy_state = lookup_var p raw_alloc /\
       FLOOKUP raw_copy_G p = FLOOKUP raw_G p /\
       op_taint raw_copy_tn (Var p) = op_taint raw_tn (Var p)`
       (qspec_then `raw_dst` mp_tac) >> simp[]) >>
  `ptr_covers raw_copy_G raw_copy_tn raw_dst raw_copy_state
     (32 + 32 * word_size (LENGTH bs))` by
    (qpat_assum `ptr_covers raw_G raw_tn raw_dst raw_alloc
       (32 + 32 * word_size (LENGTH bs))` mp_tac >>
     qpat_assum `lookup_var raw_dst raw_copy_state = lookup_var raw_dst raw_alloc` mp_tac >>
     qpat_assum `FLOOKUP raw_copy_G raw_dst = FLOOKUP raw_G raw_dst` mp_tac >>
     qpat_assum `op_taint raw_copy_tn (Var raw_dst) = op_taint raw_tn (Var raw_dst)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ptr_covers_def]) >>
  `ptr_covers raw_copy_G raw_copy_tn raw_dst raw_end (32 + LENGTH bs)` by
    (`32 + LENGTH bs <= 32 + 32 * word_size (LENGTH bs)` by
       simp[exprSimPropsTheory.le_word_size_mul] >>
     `ptr_covers raw_copy_G raw_copy_tn raw_dst raw_copy_state (32 + LENGTH bs)` by
       metis_tac[reasonCopySourcePtrTheory.ptr_covers_mono] >>
     fs[Abbr `raw_end`,ptr_covers_def,venomStateTheory.lookup_var_def]) >>
  suspend "raw_terminal_clean"
QED

Resume return_selected_valued_frag_full_core[raw_terminal_clean]:
  `!i. w2n raw_w <= i /\ i < w2n raw_w + 32 + LENGTH bs ==>
       i NOTIN raw_copy_tn.t_mem` by
    (qpat_assum `!i. w2n source_w <= i /\
       i < w2n source_w + 32 + LENGTH bs ==> i NOTIN raw_tn.t_mem` mp_tac >>
     qpat_assum `raw_copy_tn.t_mem =
       (raw_tn.t_mem DIFF {i | w2n raw_w <= i /\
         i < w2n raw_w + (32 + 32 * word_size (LENGTH bs))}) UNION
       {w2n raw_w + i | i < 32 + 32 * word_size (LENGTH bs) /\
         w2n source_w + i IN raw_tn.t_mem}` mp_tac >>
     rpt (pop_assum kall_tac) >> disch_tac >> disch_tac >>
     gen_tac >> disch_tac >>
     `LENGTH bs <= 32 * word_size (LENGTH bs)` by
       simp[exprSimPropsTheory.le_word_size_mul] >>
     simp[pred_setTheory.IN_UNION,pred_setTheory.IN_DIFF,
       pred_setTheory.GSPECIFICATION]) >>
  `eval_operand (Var raw_dst) raw_end = SOME raw_w` by
    (qunabbrev_tac `raw_end` >>
     qpat_assum `lookup_var raw_dst raw_copy_state = lookup_var raw_dst raw_alloc` mp_tac >>
     qpat_assum `lookup_var raw_dst raw_alloc = SOME raw_w` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def]) >>
  `mload (w2n raw_w) raw_end = n2w (LENGTH bs) /\
   read_memory (w2n (raw_w + 32w)) (LENGTH bs) raw_end = bs` by
    (qunabbrev_tac `raw_end` >>
     qpat_assum `mload (w2n raw_w) raw_copy_state = n2w (LENGTH bs)` mp_tac >>
     qpat_assum `read_memory (w2n (raw_w + 32w)) (LENGTH bs) raw_copy_state = bs` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[venomStateTheory.mload_def,venomStateTheory.read_memory_def]) >>
  `w2n raw_w + 32 + LENGTH bs <= raw_end.vs_alloca_next /\
   w2n raw_w + 32 + LENGTH bs <= dimword (:256)` by
    (simp[Abbr `raw_end`] >>
     qspec_then `LENGTH (bs:byte list)` assume_tac exprSimPropsTheory.le_word_size_mul >>
     decide_tac) >>
  `compile_external_return (SOME (Var raw_dst)) F T ce.ce_ret_enc_info
     ce.ce_max_return_size F nkey ut (mut = View) sc = ((),sb)` by
    (qpat_assum `compile_external_return (SOME raw_buf.buf_operand) F T ce.ce_ret_enc_info
       ce.ce_max_return_size F nkey ut (mut = View) sc = ((),sb)` mp_tac >>
     qpat_assum `raw_buf.buf_operand = Var raw_dst` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]) >>
  suspend "raw_terminal_joint"
QED

Resume return_selected_valued_frag_full_core[raw_terminal_joint]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp raw_end` by
    (qpat_assum `raw_copy_state with <|vs_vars := raw_alloc.vs_vars;
       vs_memory := raw_alloc.vs_memory|> = raw_alloc`
       (mp_tac o AP_TERM ``\z:venom_state. (z.vs_allocas,z.vs_initial_fmp,z.vs_fmp)``) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp raw_alloc` mp_tac >>
     qpat_assum `Abbrev (raw_end = _)`
       (PURE_ONCE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     simp[NoAsms,ptrDisciplineTheory.allocas_below_fmp_def] >> tautLib.TAUT_TAC) >>
  drule_all externalReturnRawJointTheory.compile_external_return_raw_joint >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`]
    (qx_choose_then `raw_ss` (qx_choose_then `raw_final_G`
      (qx_choose_then `raw_final_tn` strip_assume_tac)))) >>
  `raw_end.vs_accounts = raw_u.vs_accounts /\
   raw_end.vs_transient = raw_u.vs_transient /\
   raw_end.vs_immutables = raw_u.vs_immutables /\
   raw_end.vs_logs = raw_u.vs_logs /\ raw_end.vs_requests = raw_u.vs_requests /\
   raw_end.vs_pending_deletions = raw_u.vs_pending_deletions /\
   raw_end.vs_call_ctx = raw_u.vs_call_ctx` by
    (qunabbrev_tac `raw_end` >>
     let val project = mp_tac o AP_TERM ``\z:venom_state.
       (z.vs_accounts,z.vs_transient,z.vs_immutables,z.vs_logs,
        z.vs_requests,z.vs_pending_deletions,z.vs_call_ctx)``
     in
       qpat_assum `raw_alloc with <| vs_vars := raw_u.vs_vars;
         vs_allocas := raw_u.vs_allocas; vs_alloca_next := raw_u.vs_alloca_next;
         vs_inst_idx := raw_u.vs_inst_idx |> = raw_u` project >>
       qpat_assum `raw_copy_state with <|vs_vars := raw_alloc.vs_vars;
         vs_memory := raw_alloc.vs_memory|> = raw_alloc` project
     end >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> rpt strip_tac >> gvs[]) >>
  `!D. stor_taint_ok_at D raw_copy_tn raw_end <=>
       stor_taint_ok_at D raw_utn raw_u` by simp[stor_taint_ok_at_def] >>
  `raw_ss.vs_accounts = t.vs_accounts /\
   raw_ss.vs_transient =
     (if nr /\ mut <> View then (tstore (n2w nkey) 0w t).vs_transient
      else t.vs_transient) /\
   raw_ss.vs_logs = t.vs_logs /\ raw_ss.vs_requests = t.vs_requests /\
   raw_ss.vs_pending_deletions = t.vs_pending_deletions` by
    (simp[Abbr `raw_end`] >>
     qpat_assum `raw_u = _` (fn th => simp[NoAsms, th]) >>
     Cases_on `nr /\ mut <> View` >> simp[venomStateTheory.tstore_def]) >>
  suspend "raw_path_compose"
QED

Resume return_selected_valued_frag_full_core[raw_path_compose]:
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (raw_alloc,raw_G,raw_tn) [] (OK raw_end,raw_copy_G,raw_copy_tn)` by
    (qunabbrev_tac `raw_end` >> first_assum ACCEPT_TAC) >>
  `!H. stor_taint_ok_at (DF H) tn1 t ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (Halt raw_ss,raw_final_G,raw_final_tn)` by
    (gen_tac >> strip_tac >>
     `dead_lo_ok H (DF H) lo ce cx` by (first_assum (qspec_then `H` ACCEPT_TAC)) >>
     `stor_taint_ok_at (DF H) raw_utn raw_u` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`raw_u = _`, `raw_utn = _`, `dead_lo_ok H (DF H) lo ce cx`,
           `stor_taint_ok_at (DF H) tn1 t`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
        irule optional_transient_unlock_stor_taint >> metis_tac[]) >>
     `stor_taint_ok_at (DF H) raw_copy_tn raw_end` by simp[] >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (t,G1,tn1) [] _`
       (qspecl_then [`DF H`,`gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (raw_u,G1,raw_utn) [] _`
       (qspec_then `DF H` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (raw_alloc,raw_G,raw_tn) []
       (OK raw_end,raw_copy_G,raw_copy_tn)` (qspec_then `DF H` mp_tac) >>
     qpat_assum `!D. stor_taint_ok_at D raw_copy_tn raw_end ==> _`
       (qspec_then `DF H` drule) >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  suspend "raw_finish"
QED

Resume return_selected_valued_frag_full_core[raw_finish]:
  rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (ReturnException v)`,`mid`,`Halt raw_ss`,
    `raw_final_G`,`raw_final_tn`] >>
  conj_tac >- simp[vyperStateTheory.raise_def,gas_explicit_def] >>
  conj_tac
  >- (qpat_assum `cx = initial_evaluation_context am.sources am.layouts tx NONE`
        (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `cx = initial_evaluation_context am.sources am.layouts tx NONE`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
      (strip_assume_tac o BETA_RULE o MATCH_MP th)) >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (t,G1,tn1) [] (Halt raw_ss,raw_final_G,raw_final_tn)` by
    (first_assum (qspec_then `H` MATCH_MP_TAC) >>
     metis_tac[ghost_inv_at_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[NoAsms,fragExecTheory.exit_result_def,stmt_exit_ptr_def,expr_exit_def,halt_exit_def] >>
  reverse conj_tac >-
    (qpat_assum `gas_origin_ptr_path _ _ _ (Halt _,_,_)`
       (ACCEPT_TAC o MATCH_MP bodyFullIntCallReturnHaltTheory.gas_origin_ptr_path_halt_fmp)) >>
  qx_gen_tac `tail` >> suspend "raw_post"
QED

Resume return_selected_valued_frag_full_core[raw_post]:
  `state_rel H func ce cx mid t` by
    (qpat_assum `expr_post H ctx func ce cx e es sa sm s0 mid _ op t`
      (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [stmt_state_rel_def] o
       CONJUNCT1 o REWRITE_RULE [expr_post_def])) >>
  `lookup_raw_return_or_F (NONE:num option) tx.function_name External tops` by
    (qpat_assum `ce.ce_raw_return = lookup_raw_return_or_F
       (NONE:num option) tx.function_name External tops`
       (fn th => qpat_assum `ce.ce_raw_return` (ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
  `raw_return_bytes v = SOME raw_ss.vs_returndata` by
    metis_tac[] >>
  `?us. unlock_if_nr cx nr (is_view_mut mut)
    (mid with <|scopes := []; gas_obs := tail|>) = (INL (),us) /\
    external_call_result_rel H tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state am.sources am.exports am.layouts us),
       us.requests) (Halt raw_ss)` by
    (match_mp_tac (Q.INST
       [`func` |-> `func`, `ce` |-> `ce`, `nkey` |-> `nkey`,
        `t` |-> `t`] valued_return_result_unlock) >> simp[]) >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`v`,`us`] >> conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- (qpat_assum `ret = BaseT (BytesT (Dynamic n))` (SUBST1_TAC o SYM) >>
      first_assum ACCEPT_TAC) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`unlock_if_nr cx nr (is_view_mut mut) _ = (INL (),us)`,
     `nr /\ mut <> View ==> ut /\ _`, `cx.txn.target = tx.target`,
     `nkey = nkey_map tx.function_name`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  Cases_on `nr` >> Cases_on `mut` >>
  gvs[unlock_if_nr_def,vyperInterpreterTheory.is_view_mut_def]
QED

Finalise return_selected_valued_frag_full_core

Theorem return_selected_valued_frag_full:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  ~ctx_has_dalloca ctx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops ut nkey_map
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  get_tenv cx = type_env tops /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (!ty. expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
          ce cx ty e es /\
        expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
          ce cx ty e es) /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\
  cx.txn.target = tx.target ==>
  stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cx lctx
    (\H v ee gt r. ?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel H tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
    ce (stmt_env ce lctx ret (Return (SOME e)))
    (stmt_env (gas_shadow_env T ce) lctx ret (Return (SOME (gas_shadow_expr e))))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >>
  `cenv with ce_vars := cenv0.ce_vars = cenv0` by
    (drule entryStateRelTheory.compile_register_positional_args_cenv >> simp[compile_env_component_equality]) >>
  mp_tac (SIMP_RULE (srw_ss()) [unlock_if_nr_def,vyperStateTheory.return_def]
    (Q.INST [`nr` |-> `F`, `dflts` |-> `[]:expr list`, `rpolicy` |-> `rpolicy`,
      `unit` |-> `unit`, `mut` |-> `mut`, `args` |-> `args`, `fbody` |-> `fbody`,
      `target` |-> `target`, `ut` |-> `ut`, `nkey_map` |-> `nkey_map`, `rr` |-> `rr`,
      `lbl` |-> `lbl`, `cenv0` |-> `cenv0`, `pos_args` |-> `pos_args`,
      `min_cds` |-> `min_cds`, `is_payable` |-> `is_payable`, `nkey` |-> `nkey`,
      `iv` |-> `iv`, `rt` |-> `rt`, `cenv` |-> `cenv`, `env` |-> `env`,
      `tops` |-> `tops`, `am` |-> `am`, `tx` |-> `tx`, `ret` |-> `ret`,
      `DF` |-> `DF`, `lo` |-> `lo`, `d` |-> `d`, `ctx` |-> `ctx`,
      `shadow_ctx` |-> `shadow_ctx`, `PG` |-> `PG`, `func` |-> `func`,
      `shadow_func` |-> `shadow_func`, `cx` |-> `cx`, `lctx` |-> `lctx`,
      `ce` |-> `ce`, `e` |-> `e`, `es` |-> `es`]
      (SPEC_ALL return_selected_valued_frag_full_core))) >>
  fs[compileVyperTheory.package_external_fn_def]
QED

Theorem return_selected_valued_frag_full_nr:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,rr,tx.function_name,args,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut,iv,fbody,rt) /\
  cenv with ce_vars := cenv0.ce_vars = cenv0 /\
  same_frame cenv ce /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  get_tenv cx = type_env tops /\
  (nr /\ mut <> View ==> ~cx.txn.is_static) /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (!ty. expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
          ce cx ty e es /\
        expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
          ce cx ty e es) /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\
  cx.txn.target = tx.target ==>
  stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cx lctx
    (\H v ee gt r. ?tv v' us. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),us) /\
      external_call_result_rel H tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts us),
         us.requests) r)
    ce (stmt_env ce lctx ret (Return (SOME e)))
    (stmt_env (gas_shadow_env T ce) lctx ret (Return (SOME (gas_shadow_expr e))))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >>
  `ut /\ nkey = global_nonreentrant_slot` by
    (drule return_package_target_inversion >> strip_tac >>
     drule return_package_metadata >> simp[]) >>
  `nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
          is_view_mut mut = (mut = View)` by
    (Cases_on `nr` >> simp[] >>
     drule_all selected_nonreentrant_lock_metadata >> simp[]) >>
  `global_nonreentrant_slot < dimword (:256)` by
    simp[contextTheory.global_nonreentrant_slot_def,wordsTheory.dimword_def] >>
  `nr ==> is_view_mut mut = (mut = View)` by metis_tac[] >>
  `nr /\ mut <> View ==> T /\ ~cx.txn.is_static /\
     cx.nonreentrant_slot = SOME nkey /\ nkey < dimword (:256)` by metis_tac[] >>
  qpat_x_assum `ut` (SUBST_ALL_TAC o EQT_INTRO) >>
  drule_all (Q.INST [`ut` |-> `T`, `nkey_map` |-> `K global_nonreentrant_slot`]
    (SPEC_ALL return_selected_valued_frag_full_core)) >> simp[]
QED
