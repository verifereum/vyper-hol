Theory bodyFullAbiEncodeWordFull
Ancestors
  bodySimFull bodyInvNoDalloca bodyFullAbiEncodeAllocOrigin
  bodyFullAbiEncodeStore bodyFullAbiEncodeSuffix bodyFullAbiEncodeUniformTranslation
  bodyFullAbiEncodeWordStageWindow bodyFullAbiEncodeWordPack
  exprSimAbiEncodeWordResult bodyFullAbiEncodeResultResources
  bodyFullAbiEncodeSetupTail bodyFullAbiEncodeFinish gasShadowCompile
  exprSimSource exprSimHyps gasExemptCert gasShadowCompileStmtHelpers
  exprSimAbiEncodeWordCase exprSimAbiEncodeRuntimeInputs
  gasOutcomeFullCompose exprLowering compileEnv vyperContext vyperState
  exprLoweringProps exprBopSimProps exprBopLowering abiBuiltinAllocation abiBuiltinEncodeWord
  emitHelper vyperAST list loweringPosts exprSimAbiEncodeOblivious fragExec

Theorem abi_encode_word_vv_full_from_packaging:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\ is_word_type (expr_type e)
  ==> expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `expr_body_pre ce cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `compile_expr ce cty (TypeBuiltin _ _ _ _) sa = _` mp_tac >>
  simp[exprSimAbiEncodeWordCaseTheory.compile_abi_encode_word_shape] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) buf.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e))
    (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)) sh` >>
  rename1 `lower_abi_encode _ _ _ _ _ sh = (out,final)` >>
  gvs[as_ptr_val_def] >>
  `cs_extends sa sm` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sh` by
    (drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
     irule cs_extends_same_block >> simp[]) >>
  `!l. buf.buf_operand <> Label l` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     qpat_x_assum `emit_op ALLOCA _ sm = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[] >>
     Cases_on `buf.buf_operand` >> gvs[]) >>
  drule_all lower_abi_encode_frag_facts >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  Cases_on `lower_value compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (shop,shadow_sm)` >>
  `shop = op /\ gas_shadow_state sm shadow_sm` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `ty` |-> `expr_type e`]
      gas_shadow_stmt_lower_value) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >> gvs[] >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr (TypeBuiltin _ _ _ _)) _ = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def, exprSimAbiEncodeWordCaseTheory.compile_abi_encode_word_shape] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) buf'.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e))
    (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)) sh'` >>
  gvs[as_ptr_val_def, contextTheory.mk_ptr_def] >>
  rename1 `lower_abi_encode _ _ buf'.buf_operand _ _ sh' = (out,shadow_sb)` >>
  `cs_extends shadow_sa shadow_sm` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends shadow_sm sh'` by
    (drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
     irule cs_extends_same_block >> simp[]) >>
  `!l. buf'.buf_operand <> Label l` by
    (drule_at (Pat `compile_alloc_buffer _ shadow_sm = _`)
       abi_builtin_alloc_buffer_shape >> strip_tac >>
     qpat_x_assum `emit_op ALLOCA _ shadow_sm = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[] >>
     Cases_on `buf'.buf_operand` >> gvs[]) >>
  `cs_extends sh' shadow_sb` by metis_tac[lower_abi_encode_frag_facts] >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_full_def] >> disch_then drule_all >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  simp[exprSimAbiEncodeNonwordCaseTheory.eval_expr_singleton_type_builtin_action,
       type_builtin_args_length_ok_def] >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result])
  >- simp[vyperStorageTraceTheory.storage_trace_frame_def]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gas_exempt_cert_bind_value >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >>
      first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> first_assum (irule_at Any) >>
      simp[Abbr `childR`, exprSimDefsTheory.halt_exit_def] >> rpt strip_tac >>
      qpat_x_assum `expr_exit res r` mp_tac >>
      Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def] >>
      Cases_on `r` >> Cases_on `y` >>
      simp[exprSimDefsTheory.expr_exit_def] >> gvs[] >>
      rename1 `Error err` >> Cases_on `err` >>
      simp[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]) >>
  suspend "word_continuation"
QED

Resume abi_encode_word_vv_full_from_packaging[word_continuation]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
  `ee with gas_obs := [] = ee` by
    (qpat_assum `ee.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (fn th =>
      qpat_assum `ee with gas_obs := [] = ee`
        (fn eq => assume_tac (REWRITE_RULE [listTheory.APPEND_NIL,eq] th)))) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     expr_post H ctx func ce cx e es sa sm s0 ee v op t /\
     ghost_inv_at (DF H) lo d ce cx ee G1 tn1 t /\
     ptr_val_ok cx (post_value_type ce e) v op G1 tn1 t /\
     ghost_kept_at lo ce es sa G0 tn0 s0 G1 tn1` by
    (rpt strip_tac >> simp[] >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `fn_has_code sm sh func /\ fn_has_code sh final func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all abi_encode_word_stage_window_origin >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by
    (drule_at (Pat `f st = _`) vyperStorageFootprintTheory.valid_horizon_frame >>
     simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
          cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx es s0 /\
   stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee u` by
    (rpt conj_tac >> first_x_assum drule >> simp[]) >>
  qpat_x_assum `lower_abi_encode _ _ _ _ _ sh = _`
    (fn th => qpat_assum `buf.buf_operand = Var q` (fn src =>
      qpat_assum `type_to_abi_enc_info _ _ _ = AbiCopy 32` (fn ei =>
        qpat_assum `abi_size_bound _ _ = 32` (fn sz =>
          assume_tac (REWRITE_RULE [src,ei,sz] th))))) >>
  drule_all abi_encode_word_pack_origin >>
  disch_then (qspecl_then [`d`,`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choose_then `p` (qx_choose_then `dst` (qx_choose_then `packed`
      (qx_choose_then `Gp` (qx_choose_then `tnp` strip_assume_tac)))) o
      BETA_RULE o PURE_REWRITE_RULE [LET_THM])) >>
  `expr_body_pre ce cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV ETA_CONV)
      exprSimAbiEncodePrefixWindowTheory.abi_encode_operand_success_type) >>
  disch_then (qspecl_then [`env`,`ce`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `rt` strip_assume_tac) >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    (irule exprSimHypsTheory.expr_body_pre_lowered_fits >> goal_assum (drule_at Any)) >>
  `lowered_value_type ce e = expr_type e` by
    (qpat_assum `arg_type_fits _ _` mp_tac >>
     qpat_assum `is_word_type (expr_type e)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `expr_type e` >> Cases_on `lowered_value_type ce e` >>
     gvs[is_word_type_def, vyperTypeSystemTheory.arg_type_fits_def] >>
     Cases_on `b` >> Cases_on `b'` >> gvs[is_word_type_def, vyperTypeSystemTheory.arg_type_fits_def] >>
     Cases_on `b` >> Cases_on `b''` >> gvs[is_word_type_def, vyperTypeSystemTheory.arg_type_fits_def]) >>
  `evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt` by simp[] >>
  drule_all exprSimAbiEncodeNonwordResultTheory.abi_encode_nonword_result_bound >>
  disch_then (qx_choose_then `N` strip_assume_tac) >>
  `evaluate_type_builtin cx (AbiEncode F mid) ty [expr_type e] [v] =
    INL (BytesV (abi_encode_method_id_bytes mid ++ enc ct rv))` by
    (qpat_assum `enc ct rv = _` (fn th => simp[evaluate_type_builtin_def,
      vyperABITheory.needs_external_call_wrap_def,
      vyperABITheory.evaluate_abi_encode_bytes_def,th])) >>
  suspend "word_resources"
QED

Resume abi_encode_word_vv_full_from_packaging[word_resources]:
  `well_typed_type_builtin_args (AbiEncode F mid) ty [expr_type e]` by
    (qpat_assum `expr_body_pre ce cx env (TypeBuiltin ann _ _ _) es` mp_tac >>
     simp[NoAsms, exprSimHypsDefsTheory.expr_body_pre_def,
       Once vyperTypeSystemTheory.well_typed_expr_def]) >>
  `LENGTH (abi_encode_method_id_bytes mid ++ enc ct rv) <= N` by
    (qpat_assum `enc ct rv = _` (fn th => once_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `k = case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4` >>
  qabbrev_tac `cap = 32 + 32 * word_size (32 + k)` >>
  `LENGTH (abi_encode_method_id_bytes mid) = k` by
    (Cases_on `mid` >> fs[Abbr `k`, abi_encode_method_id_bytes_def,
       vyperTypeSystemTheory.well_typed_type_builtin_args_def]) >>
  `type_memory_bytes ce (lowered_value_type ce (TypeBuiltin ann (AbiEncode F mid) ty [e])) = cap` by
    (qpat_assum `lowered_value_type ce e = expr_type e` (fn eq =>
       qpat_assum `abi_size_bound _ (lowered_value_type ce e) = 32`
         (assume_tac o REWRITE_RULE [eq])) >>
     Cases_on `mid` >>
     simp[Once lowered_value_type_def, Abbr `cap`, Abbr `k`, type_memory_bytes_def,
          vfmConstantsTheory.word_size_def]) >>
  `val_store_size (BaseTV (BytesT (Dynamic N)))
     (BytesV (abi_encode_method_id_bytes mid ++ enc ct rv)) = cap` by
    (qunabbrev_tac `cap` >>
     simp_tac (srw_ss()) [exprSimPropsTheory.val_store_size_def, LENGTH_APPEND] >>
     qpat_assum `LENGTH (enc ct rv) = 32` (fn len =>
       qpat_assum `LENGTH (abi_encode_method_id_bytes mid) = k` (fn sel =>
         rewrite_tac[len,sel,Q.SPECL [`k`,`32`] arithmeticTheory.ADD_COMM]))) >>
  `p < dimword (:256)` by decide_tac >>
  `w2n (n2w p : bytes32) = p` by simp[wordsTheory.w2n_n2w] >>
  `!mem. mem_agree_outside tnp.t_mem packed.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic N)))
        (BytesV (abi_encode_method_id_bytes mid ++ enc ct rv)) p mem` by
    (rpt strip_tac >>
     qpat_assum `!mem. mem_agree_outside tnp.t_mem packed.vs_memory mem ==> _`
       (qspec_then `mem` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     irule (SRULE [GSYM valueEncodingPropsTheory.mem_word_at_eq_mload]
       (Q.INST [`actual` |-> `packed with vs_memory := mem`]
         exprSimAbiEncodeTupleResultTheory.abi_encode_tuple_result_memory)) >>
     conj_tac
     >- (qexists `OPTION_MAP bytes_method_id_word mid` >>
         qunabbrev_tac `k` >>
         qpat_assum `LENGTH (enc ct rv) = 32` (fn th => rewrite_tac[th]) >>
         rpt conj_tac >> first_assum ACCEPT_TAC)
     >> qexistsl [`F`,`ty`,`[expr_type e]`] >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `payload = abi_encode_method_id_bytes mid ++ enc ct rv` >>
  `vv_store_bound cx (post_value_type ce (TypeBuiltin ann (AbiEncode F mid) ty [e]))
      (lowered_value_type ce (TypeBuiltin ann (AbiEncode F mid) ty [e])) ee
      (Value (BytesV payload)) (LocatedValue ann (mk_ptr (Var dst) LocMemory)) packed /\
   ptr_vv_ok cx (post_value_type ce (TypeBuiltin ann (AbiEncode F mid) ty [e]))
      (Value (BytesV payload)) (LocatedValue ann (mk_ptr (Var dst) LocMemory)) ee Gp tnp packed /\
   ptr_buf_ok ce (TypeBuiltin ann (AbiEncode F mid) ty [e]) (Var dst) Gp packed` by
    (irule abi_encode_bytes_full_resources >>
     qexistsl [`N`,`cap`,`n2w p`] >> simp[] >>
     qpat_assum `out = Var dst` (fn eq =>
       qpat_assum `eval_operand out packed = SOME _`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  suspend "word_outcome"
QED

Resume abi_encode_word_vv_full_from_packaging[word_outcome]:
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl [`Gp`,`ee`,`INL (Value (BytesV payload))`,`packed`,`tnp`] >>
  simp[] >> qx_gen_tac `H` >> strip_tac >>
  conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] (OK u,Gu,tnu)`
        (qspec_then `DF H` (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
      disch_then (qspecl_then [`u`,`Gu`,`tnu`,`[]`,`OK packed`,`Gp`,`tnp`] mp_tac) >>
      simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
      stmt_state_rel _ _ _ _ _ ee u /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `storage_well_formed_on cx ee (FST H)` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
        expr_post _ _ _ _ _ _ _ _ _ _ ee _ _ t /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     drule (cj 2 (iffLR loweringPostsTheory.expr_post_def)) >> simp[]) >>
  `ghost_inv_at (DF H) lo d ce cx ee Gp tnp packed` by
    (qpat_assum `!H D. _ ==> ghost_inv_at D lo d ce cx ee Gp tnp packed`
       (qspecl_then [`H`,`DF H`] irule) >> simp[]) >>
  reverse conj_tac
  >- (qpat_assum `ty = TupleT [expr_type e]` SUBST_ALL_TAC >>
      qpat_assum `expr_type (TypeBuiltin _ _ _ _) = BaseT _`
        (fn eq =>
          qpat_assum `vv_store_bound _ _ _ _ _ _ packed`
            (assume_tac o REWRITE_RULE [post_value_type_def, eq, contextTheory.mk_ptr_def]) >>
          qpat_assum `ptr_vv_ok _ _ _ _ _ Gp tnp packed`
            (assume_tac o REWRITE_RULE [post_value_type_def, eq, contextTheory.mk_ptr_def])) >>
      simp[contextTheory.vv_location_def, is_bytestring_type_def]) >>
  `abi_encode_staged_observation H ctx func ce cx ee sh out
     (OPTION_MAP bytes_method_id_word mid) cap p ct rv u packed` by
    (qpat_assum `!H. stmt_state_rel H ctx func ce cx ee u ==> _`
       (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
  `~expr_has_effect e ==> pure_frame ce func es sa s0 packed` by
    (strip_tac >>
     qpat_assum `pure_frame ce func es sa s0 u ==> _` irule >> simp[]) >>
  qunabbrev_tac `cap` >> qunabbrev_tac `k` >> qunabbrev_tac `payload` >>
  drule_all (REWRITE_RULE [] (Q.INST
    [`mid` |-> `OPTION_MAP bytes_method_id_word mid0`]
    abi_encode_word_observation_vv_post)) >>
  `ann = BaseT (BytesT (Dynamic N))` by
    (qpat_assum `expr_type (TypeBuiltin _ _ _ _) = BaseT _` mp_tac >>
     rewrite_tac[expr_type_def]) >>
  simp[expr_type_def] >>
  mp_tac (GEN_ALL (Q.INST
    [`p` |-> `<|ptr_operand := Var dst; ptr_location := LocMemory|>`,
     `q` |-> `mk_ptr (Var dst) LocMemory`]
    exprSimAbiEncodeNonwordCaseTheory.abi_encode_vv_post_pointer_cong)) >>
  simp[contextTheory.mk_ptr_def] >>
  disch_then (fn th => rewrite_tac[GSYM th])
QED

Finalise abi_encode_word_vv_full_from_packaging
