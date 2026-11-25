Theory bodyFullAbiEncodeWordFull
Ancestors
  bodySimFull bodyFullAbiEncodeAllocOrigin
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  bodyFullAbiEncodeStore bodyFullAbiEncodeSuffix bodyFullAbiEncodeUniformTranslation
  bodyFullAbiEncodeWordPack bodyFullAbiEncodeWordLayout
  exprSimAbiEncodeBytesOwnership exprSimAbiEncodeCapacity bodyFullAbiEncodeResultResources
  bodyFullAbiEncodeSetupTail bodyFullAbiEncodeFinish gasShadowCompile
  exprSimSource exprSimHyps gasExemptCert valueEncodingDefs vyperTypeABI freshWrites gasShadowCompileStmtHelpers
  exprSimAbiEncodeNonwordCase exprSimAbiEncodeRuntimeInputs exprSimAbiEncodePrefixWindow
  vyperTypeArgFits entryDecodeProps exprOperandVar exprReasonOperand exprSimWordArgs bodyPtrDefs
  gasOutcomeFullCompose gasShadowCompilePure gasShadowState exprLowering compileEnv vyperContext vyperState
  exprLoweringProps exprBopSimProps exprBopLowering abiBuiltinAllocation abiBuiltinEncodeWord
  emitHelper vyperAST list loweringPosts abiBuiltinEncodeSource exprSimProps fragExec

Theorem abi_encode_word_vv_full_from_packaging:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\ is_word_type (expr_type e)
  ==> expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all abi_encode_word_child_layout >>
  disch_then (qx_choosel_then [`op`,`sm`,`shadow_sm`,`out`] strip_assume_tac) >>
  qpat_assum `ci_mono sa sm`
    (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `abi_size_bound ce.ce_struct_fields (expr_type e) = 32` by metis_tac[] >>
  qabbrev_tac `meth = OPTION_MAP bytes_method_id_word mid` >>
  qabbrev_tac `encode = \dst. comp_ignore_bind
    (emit_void MSTORE [dst;op]) (comp_return (Lit 32w))` >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_full_def] >> disch_then drule_all >> simp[] >> strip_tac >>
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
  `expr_body_pre ce cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV ETA_CONV) abi_encode_operand_success_type) >>
  disch_then (qspecl_then [`env`,`ce`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `rt` strip_assume_tac) >>
  `?av. vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av` by
    metis_tac[cj 1 vyper_to_abi_total] >>
  drule_all vyper_to_abi_word_enc >> strip_tac >>
  qabbrev_tac `ct = vyper_to_abi_type (get_tenv cx) (expr_type e)` >>
  qabbrev_tac `rv = av` >>
  `enc ct rv = word_to_bytes (typed_val_to_w256 rt v) T` by fs[Abbr `ct`, Abbr `rv`] >>
  `LENGTH (enc ct rv) = 32` by simp[] >>
  `expr_post (storage_trace_horizon ee.storage_trace) ctx func ce cx e es sa sm s0 ee v op t /\
   ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) lo d ce cx ee G1 tn1 t` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
        expr_post H ctx func ce cx e es sa sm s0 ee v op t /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> asm_rewrite_tac[]) >>
  `post_value_type ce e = expr_type e` by
    (match_mp_tac post_value_type_word >> first_assum ACCEPT_TAC) >>
  `eval_operand op t = SOME (typed_val_to_w256 rt v) /\ op_taint tn1 op = {}` by
    (fs[expr_post_def, ptr_val_ok_def] >>
     match_mp_tac (Q.SPECL [`cx`,`expr_type e`,`rt`,`v`,`op`,`t`]
       expr_val_rel_typed) >> asm_rewrite_tac[]) >>
  `(~expr_has_effect e ==> pure_frame ce func es sa s0 t)` by fs[expr_post_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by
    (drule_at (Pat `f st = _`) vyperStorageFootprintTheory.valid_horizon_frame >>
     simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
          cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx es s0 /\
   stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee t /\
   wb_frame ce es ee sa s0 t` by
    (drule expr_post_frame >> fs[expr_post_def] >> metis_tac[]) >>
  `local_ptrs_reserved ce sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `(!x. op = Var x ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x)` by
    metis_tac[compile_lower_value_var, not_fresh_at_mono, local_ptrs_reserved_imm_base] >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
  qunabbrev_tac `encode` >>
  drule_all abi_encode_word_pack_origin >>
  disch_then (qspecl_then [`d`,`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choose_then `p` (qx_choose_then `dst` (qx_choose_then `packed`
      (qx_choose_then `Gp` (qx_choose_then `tnp` strip_assume_tac)))) o
      BETA_RULE o PURE_REWRITE_RULE [LET_THM])) >>
  qunabbrev_tac `meth` >>
  `evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt` by simp[] >>
  drule_all abi_encode_nonword_result_bound >>
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
    (qunabbrev_tac `ct` >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `k = case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4` >>
  qabbrev_tac `cap = 32 + 32 * word_size (32 + k)` >>
  `LENGTH (abi_encode_method_id_bytes mid) = k` by
    (Cases_on `mid` >> fs[Abbr `k`, abi_encode_method_id_bytes_def,
       vyperTypeSystemTheory.well_typed_type_builtin_args_def]) >>
  `type_memory_bytes ce (lowered_value_type ce (TypeBuiltin ann (AbiEncode F mid) ty [e])) = cap` by
    (Cases_on `mid` >>
     qpat_assum `lowered_value_type ce e = expr_type e` (fn layout =>
       qpat_assum `abi_size_bound _ (expr_type e) = 32` (fn bound =>
         simp[Once lowered_value_type_def, Abbr `cap`, Abbr `k`, type_memory_bytes_def,
              vfmConstantsTheory.word_size_def,layout,bound]))) >>
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
         abi_encode_tuple_result_memory)) >>
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
  `stmt_state_rel H ctx func ce cx ee t /\
   storage_well_formed_on cx ee (FST H) /\
   ghost_inv_at (DF H) lo d ce cx ee G1 tn1 t` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
        expr_post _ _ _ _ _ _ _ _ _ _ ee _ _ t /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `expr_post H ctx func ce cx e es sa sm s0 ee v op t`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     asm_rewrite_tac[]) >>
  `ghost_inv_at (DF H) lo d ce cx ee Gp tnp packed` by
    (qpat_assum `!H D. _ ==> ghost_inv_at D lo d ce cx ee Gp tnp packed`
       (qspecl_then [`H`,`DF H`] irule) >> simp[]) >>
  `stmt_state_rel H ctx func ce cx ee packed` by
    (qpat_assum `!H. stmt_state_rel _ _ _ _ _ ee t ==> _`
       (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
  `s0.vs_alloca_next <= packed.vs_alloca_next` by decide_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp packed` by
    (qpat_assum `stmt_state_rel H ctx func ce cx ee packed`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  reverse conj_tac
  >- (qpat_assum `ty = TupleT [expr_type e]` SUBST_ALL_TAC >>
      qpat_assum `expr_type (TypeBuiltin _ _ _ _) = BaseT _`
        (fn eq =>
          qpat_assum `vv_store_bound _ _ _ _ _ _ packed`
            (assume_tac o REWRITE_RULE [post_value_type_def, eq, contextTheory.mk_ptr_def]) >>
          qpat_assum `ptr_vv_ok _ _ _ _ _ Gp tnp packed`
            (assume_tac o REWRITE_RULE [post_value_type_def, eq, contextTheory.mk_ptr_def])) >>
      simp[contextTheory.mk_ptr_def, contextTheory.vv_location_def, is_bytestring_type_def]) >>
  `32+LENGTH payload <= cap` by
    (simp[Abbr `payload`, Abbr `cap`] >>
     once_rewrite_tac[Q.SPECL [`k`,`32`] arithmeticTheory.ADD_COMM] >>
     ACCEPT_TAC (Q.SPEC `32+k` exprSimPropsTheory.le_word_size_mul)) >>
  `ann = BaseT (BytesT (Dynamic N))` by
    (qpat_assum `expr_type (TypeBuiltin _ _ _ _) = BaseT _` mp_tac >>
     rewrite_tac[expr_type_def]) >>
  irule (REWRITE_RULE [expr_type_def] (Q.INST
    [`e` |-> `TypeBuiltin ann (AbiEncode F mid) (TupleT [expr_type e]) [e]`,
     `result` |-> `Value (BytesV payload)`] abi_encode_bytes_vv_post)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >~ [`read_result _ _ _ = _`]
  >- simp[read_result_def, return_def]
  >~ [`~expr_has_effect _ ==> pure_frame _ _ _ _ _ _`]
  >- (rewrite_tac[expr_has_effect_thm, listTheory.EXISTS_DEF] >> strip_tac >>
      qpat_assum `pure_frame ce func es sa s0 t ==> _` irule >>
      first_assum irule >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`N`,`sm.cs_next_id`,`p`,`cap`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `out = Var dst` (fn eq =>
       qpat_assum `eval_operand out packed = SOME _`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  qpat_assum `!mem. _ ==> val_in_memory _ _ _ _` irule >>
  simp[mem_agree_outside_def]
QED

Finalise abi_encode_word_vv_full_from_packaging
