Theory bodyFullAbiEncodeNonwordFull
Ancestors
  bodyFullPreds bodySimFull bodyInvNoDalloca bodyFullAbiEncodeArgStep
  bodyFullAbiEncodeSetupTail bodyFullAbiEncodeFinish bodyFullAbiEncodeAllocOrigin
  bodyFullAbiEncodeSuffix bodyFullAbiEncodeUniformTranslation
  exprSimAbiEncodeNonwordCase exprSimAbiEncodeRuntimeInputs
  exprSimAbiEncodeNonwordResources exprSimAbiEncodeCapacity
  exprSimAbiEncodeNonwordResult bodyFullAbiEncodeReadResources
  exprSimIfExpWidenedPhysicalType
  exprSimHyps exprSimSource gasOutcomeFullCompose gasShadowCompile
  gasShadowCompileStmtHelpers exprLowering compileEnv

Theorem abi_encode_nonword_vv_full_from_packaging:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  body_expr_full_ok cx e /\ ~is_word_type (expr_type e)
  ==> expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  strip_tac >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `expr_body_pre ce cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr ce cty (TypeBuiltin ann _ _ _) sa = _` mp_tac >>
  simp[compile_abi_encode_nonword_shape] >>
  pairarg_tac >> rename1 `lower_value _ _ _ _ sa = (op,sm)` >>
  simp[] >> simp[as_ptr_val_def] >>
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) op
    (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e))
    (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)) sm` >>
  rename1 `lower_abi_encode _ _ _ _ _ sm = (out,sn)` >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `lower_value _ _ _ e sa = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >> pairarg_tac >>
  rename1 `compile_expr ce (expr_type e) e sa = (vv,si)` >>
  strip_tac >> gvs[] >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `ty` |-> `expr_type e`]
    gas_shadow_stmt_compile_expr) >>
  rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  gvs[] >> rename1 `gas_shadow_state si shadow_si` >>
  rename1 `compile_expr ce (expr_type e) e sa = (vv,si)` >>
  mp_tac (Q.INST [`cenv` |-> `ce`] gasShadowCompileConvertTheory.gas_shadow_compiles_unwrap_value) >>
  rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`si`,`shadow_si`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `unwrap_value ce vv shadow_si` >> gvs[] >>
  rename1 `gas_shadow_state sm shadow_sm` >>
  qpat_x_assum `compile_expr ce cty (gas_shadow_expr _) shadow_sa = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def, compile_abi_encode_nonword_shape,
    gasShadowTheory.gas_shadow_expr_type,
    lower_value_def, comp_bind_def, as_ptr_val_def] >>
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) op
    (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e))
    (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)) shadow_sm` >>
  simp[as_ptr_val_def, contextTheory.mk_ptr_def] >> strip_tac >> gvs[] >>
  rename1 `fn_has_code shadow_sa shadow_sb shadow_func` >>
  `cs_extends sa si /\ cs_extends shadow_sa shadow_si` by
    metis_tac[exprSimUnwrapTheory.compile_expr_extends] >>
  `cs_extends si sm /\ cs_extends shadow_si shadow_sm` by
    metis_tac[exprSimUnwrapTheory.unwrap_value_extends] >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[cs_extends_trans] >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    metis_tac[abiBuiltinEncodeWordTheory.lower_abi_encode_extends] >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  mp_tac (Q.INST [`rest` |-> `[]`, `mid` |-> `si`, `sb` |-> `sm`,
    `shadow_mid` |-> `shadow_si`, `shadow_sb` |-> `shadow_sm`]
    abi_encode_arg_step_full) >>
  simp[expr_can_mutate_def] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  simp[eval_expr_singleton_type_builtin_action,
    vyperContextTheory.type_builtin_args_length_ok_def] >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
      vyperStorageTraceTheory.evaluate_storage_trace_frame,
      vyperStorageTraceTheory.storage_trace_frame_read_result]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_def]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_value >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
      first_assum ACCEPT_TAC) >>
  qexists `childQ` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> first_assum (irule_at Any) >>
      simp[Abbr `childR`] >> rpt strip_tac >>
      Cases_on `res` >- gvs[exprSimDefsTheory.expr_exit_def] >>
      qexists `y` >> Cases_on `r` >> Cases_on `y` >>
      gvs[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >>
      gvs[exprSimDefsTheory.expr_exit_def]) >>
  map_every qx_gen_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`s`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> childQ _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp_tac bool_ss [Abbr `childQ`] >> strip_tac >> gvs[] >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[post_value_type_nonword] >>
  `?ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv` by
    metis_tac[post_type_evaluates] >>
  `~is_word_type (lowered_value_type ce e)` by
    metis_tac[expr_body_pre_lowered_fits,
      exprSimLayoutTransportTheory.compatible_word_type] >>
  `expr_post (storage_trace_horizon ee.storage_trace)
    ctx func ce cx e es sa sm s0 ee v op s` by metis_tac[] >>
  `~is_word_type (post_value_type ce e) ==> !w.
     eval_operand op s = SOME w ==>
     type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= s.vs_alloca_next` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  drule_all abi_encode_arg_positive_resources >> simp[] >> strip_tac >>
  FAIL_TAC "positive and zero capacity"
QED
