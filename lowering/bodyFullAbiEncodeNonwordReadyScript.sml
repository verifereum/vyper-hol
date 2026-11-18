(* The singleton read endpoint is fixed before allocation and selector setup. *)
Theory bodyFullAbiEncodeNonwordReady
Ancestors
  bodyFullAbiEncodeSetupTail bodyFullAbiEncodeAllocOrigin
  bodyFullAbiEncodeNonwordWindow bodyFullAbiEncodeSetupSourceFrame
  bodyFullAbiEncodeReadResources exprSimAbiEncodeCapacity
  exprSimAbiEncodeSourceMetadata exprSimAbiEncodeArgsPhysicalCapacity
  exprSimIfExpWidenedPhysicalType exprSimAbiEncodeNonwordResources
  exprSimHyps exprSimSource gasOutcomeFullCompose gasShadowCompile
  bodyPtrMakeArrayCopyStateFrame exprSimHash stateRelProj
  abiEncodeMaterialize valueCopyBytes compileEnv fragGasOriginPtrLoop

Theorem abi_encode_nonword_ready_origin:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  expr_body_pre ce cx env e es /\ ~is_word_type (expr_type e) /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  midw = OPTION_MAP bytes_method_id_word mid /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e) /\
  maxlen = abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) /\
  k = (case midw of NONE => 0 | SOME _ => 4) /\
  mw = (case midw of NONE => 0 | SOME _ => 32) /\
  N = 32 + 32 * word_size (maxlen+k) /\
  cap = val_footprint tv v /\
  lower_abi_encode F midw op ei maxlen sm = (out,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func ce cx e es sa sm s0 ee v op s /\
       ghost_inv_at (DF H) lo d ce cx ee G1 tn1 s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\ expr_val_rel cx (lowered_value_type ce e) v op s /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  ptr_val_ok cx (post_value_type ce e) v op G1 tn1 s /\
  (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G1 s) /\
  (~is_word_type (post_value_type ce e) ==> !w. eval_operand op s = SOME w ==>
    type_memory_size tv = 0 \/ type_memory_size tv + w2n w <= s.vs_alloca_next) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G1 tn1 /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?ready body_end len root dp p src ct rv av u Gu tnu.
    abi_builtin_encode_setup midw maxlen sm = ((Var root,Var dp),ready) /\
    compile_abi_encode_to_buf (Var dp) op ei ready = (len,body_end) /\
    abi_builtin_encode_finish (Var root) len k body_end = ((),sb) /\
    out = Var root /\ fn_has_code ready body_end func /\ fn_has_code body_end sb func /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G1,tn1) [] (OK u,Gu,tnu)) /\
    ~u.vs_halted /\ u.vs_current_bb = ready.cs_current_bb /\
    u.vs_inst_idx = LENGTH ready.cs_current_insts /\
    alloca_history func u /\ alloca_inv u /\ alloca_room ctx func u /\
    allocas_from lo u /\ lo <= p /\ s.vs_alloca_next <= u.vs_alloca_next /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (p,N) /\
    p+N <= u.vs_alloca_next /\ p+N < dimword(:256) /\
    eval_operand (Var root) u = SOME (n2w p) /\ ptr_covers Gu tnu root u N /\
    eval_operand (Var dp) u = SOME (n2w (p+32+k)) /\ ptr_covers Gu tnu dp u maxlen /\
    not_fresh_at ready root /\ not_fresh_at ready dp /\
    (case midw of NONE => T | SOME w => !mem.
      mem_agree_outside tnu.t_mem u.vs_memory mem ==> mem_word_at (p+32) mem = w << 224) /\
    eval_operand op u = SOME (n2w src) /\ op_taint tnu op = {} /\
    (!x. op = Var x ==> not_fresh_at ready x) /\
    vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av /\
    LENGTH (enc ct rv) <= maxlen /\ 32+k+LENGTH (enc ct rv) <= N /\ 32+mw <= N /\
    (!mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==>
      abi_encoder_window_input ei ct rv src cap mem) /\
    (0 < cap ==> src+cap <= u.vs_alloca_next /\
      venomMemDefs$regions_disjoint (src,cap) (p+32+k,LENGTH (enc ct rv)) /\
      ?x. op = Var x /\ ptr_covers Gu tnu x u cap) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids ready body_end /\
      FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (src,cap) (b,sz) /\
      venomMemDefs$regions_disjoint (p+32+k,LENGTH (enc ct rv)) (b,sz) /\
      venomMemDefs$regions_disjoint (p+32,mw) (b,sz)) /\
    local_ptrs_reserved ce ready /\
    (!x. not_fresh_at sa x ==> not_fresh_at ready x) /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gu x = FLOOKUP G1 x /\ op_taint tnu (Var x) = op_taint tn1 (Var x)) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP u.vs_allocas aid = SOME row) /\
    (!aid b sz. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint p N b sz) /\
    (!name b sz. local_region ce ee.scopes u name b sz ==> regions_disjoint p N b sz) /\
    (!b sz. regions_disjoint (p+32) mw b sz ==>
      mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    (!i. i < s.vs_alloca_next /\ ~(p+32 <= i /\ i < p+32+mw) ==>
      (i IN tnu.t_mem <=> i IN tn1.t_mem)) /\
    tnu.t_stor = tn1.t_stor /\ tnu.t_trans = tn1.t_trans /\ tnu.t_imm = tn1.t_imm /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee u /\ ghost_inv_at (DF H) lo d ce cx ee Gu tnu u) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gu tnu /\
    wb_frame ce es ee sa s0 u
Proof
  strip_tac >> gvs[] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  `~is_word_type (post_value_type ce e)` by metis_tac[post_value_type_nonword] >>
  `?ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv` by
    metis_tac[post_type_evaluates] >>
  `~is_word_type (lowered_value_type ce e)` by
    metis_tac[expr_body_pre_lowered_fits, exprSimLayoutTransportTheory.compatible_word_type] >>
  `~is_word_type (post_value_type ce e) ==> !w.
     eval_operand op s = SOME w ==>
     type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= s.vs_alloca_next` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  drule_all abi_encode_arg_positive_resources >> simp[] >> strip_tac >>
  suspend "translate_child"
QED

Resume abi_encode_nonword_ready_origin[translate_child]:
  `value_runtime_typed env (post_value_type ce e) v` by
    (irule memory_rhs_read_post_typed >>
     qexistsl_tac [`cx`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `ee with gas_obs := []`] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[listTheory.APPEND_NIL] >> disch_tac >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def] >>
     first_assum ACCEPT_TAC) >>
  `value_has_type ptv v` by
    gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
       exprSimHypsDefsTheory.expr_body_pre_def, exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `val_footprint ptv v = val_footprint tv v` by
    (drule expr_body_pre_lowered_fits >> strip_tac >>
     drule_all materialize_post_lowered_classify >> strip_tac >- gvs[] >>
     metis_tac[bytestring_val_footprint_eq]) >>
  `?w. eval_operand op s = SOME w` by gvs[loweringPostsTheory.expr_val_rel_def] >>
  `op_taint tn1 op = {}` by gvs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `!mem. mem_agree_outside tn1.t_mem s.vs_memory mem ==>
      val_in_memory ptv v (w2n w) mem` by
    (gvs[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn1.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem` by
    (drule expr_body_pre_lowered_fits >> strip_tac >>
     drule_all materialize_post_lowered_classify >> strip_tac >- gvs[] >>
     rpt strip_tac >> irule bytestring_val_in_memory_transfer >>
     conj_tac >- simp[] >>
     qexistsl_tac [`post_value_type ce e`, `lowered_value_type ce e`, `get_tenv cx`, `ptv`] >> simp[]) >>
  `?av. vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av` by
    metis_tac[cj 1 vyperTypeABITheory.vyper_to_abi_total] >>
  `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\ value_has_type stv v` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     strip_tac >> drule_at (Pat `bind _ _ _ = _`)
       (CONV_RULE (DEPTH_CONV ETA_CONV)
         exprSimAbiEncodePrefixWindowTheory.abi_encode_operand_success_type) >>
     disch_then (qspecl_then [`env`, `ce`] mp_tac) >> simp[]) >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by metis_tac[expr_body_pre_lowered_fits] >>
  `vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
   vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e) =
     vyper_to_abi_type (get_tenv cx) (expr_type e)` by
    metis_tac[exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_conversion,
      exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_abi_type] >>
  drule_all abi_encode_nonword_numerical_capacity >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  suspend "split_code"
QED

Resume abi_encode_nonword_ready_origin[split_code]:
  qpat_assum `lower_abi_encode _ _ _ _ _ sm = _`
    (strip_assume_tac o MATCH_MP abiBuiltinEncodeCodeTheory.lower_abi_encode_trace) >>
  drule abiBuiltinEncodeCodeTheory.abi_builtin_encode_setup_trace >> strip_tac >>
  `cs_extends sm ready` by
    (drule abiBuiltinEncodeCodeTheory.abi_builtin_encode_setup_shape >>
     strip_tac >> irule cs_extends_same_block >> simp[]) >>
  `cs_extends ready body_end` by metis_tac[loweringHaltTheory.compile_abi_encode_to_buf_extends] >>
  `cs_extends body_end sb` by
    (drule abiBuiltinEncodeCodeTheory.abi_builtin_encode_finish_shape >>
     strip_tac >> irule cs_extends_same_block >> simp[]) >>
  `cs_extends sm allocated` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends allocated address_st` by metis_tac[abiEncoderAddressReachTheory.abi_encoder_emit_address_shape] >>
  `cs_extends address_st ready` by
    (Cases_on `mid`
     >- gvs[abiBuiltinEncodeCodeTheory.abi_builtin_encode_method_id_def, comp_return_def, cs_extends_refl] >>
     qpat_x_assum `abi_builtin_encode_method_id _ _ _ = _` mp_tac >>
     simp[abiBuiltinEncodeCodeTheory.abi_builtin_encode_method_id_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_var_def, fresh_id_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_def] >> strip_tac >> gvs[] >>
     simp[cs_extends_def, GSYM listTheory.APPEND_ASSOC, rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sm ready func /\ fn_has_code ready body_end func /\
   fn_has_code body_end sb func /\ fn_has_code sm allocated func /\
   fn_has_code allocated ready func` by metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `ci_mono sa sm` by
    (qpat_assum `lower_value _ _ _ _ sa = _` (fn th =>
       mp_tac (Q.SPECL [`ce`,`expr_type e`,`e`,`sa`] (cj 2 stmtLoweringMonoTheory.ci_mono_compile_expr_sa)) >> simp[th])) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `local_ptrs_reserved ce sm` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  suspend "allocate"
QED

Resume abi_encode_nonword_ready_origin[allocate]:
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    fs[loweringPostsTheory.expr_post_def] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `val_footprint tv v <= type_memory_size tv` by
    metis_tac[exprSimPropsTheory.val_footprint_le, cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `0 < val_footprint ptv v ==> w2n w + val_footprint ptv v <= s.vs_alloca_next` by
    (strip_tac >> `0 < type_memory_size tv` by decide_tac >>
     qpat_assum `~is_word_type (post_value_type ce e) ==> !w. _`
       (drule o Q.SPEC `w` o UNDISCH) >> strip_tac >> decide_tac) >>
  `32 + 32 * word_size (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) +
       (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4)) < dimword (:256)` by
    (Cases_on `mid` >> fs[]) >>
  drule_all abi_encode_nonword_setup_output >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `alloca_inv (abi_builtin_allocate_state _ outsz s)` >>
  qmatch_asmsub_abbrev_tac `alloca_inv alloc_model` >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    abi_encode_alloc_origin_exact) >>
  disch_then (qspecl_then [`tn1`, `gas_explicit_sites ctx shadow_ctx`, `PG`, `G1`] mp_tac) >>
  strip_tac >>
  rename1 `lookup_var q allocated_s = SOME outw` >>
  rename1 `ptr_covers G2 tn2 q allocated_s outsz` >>
  `allocated_s.vs_allocas = alloc_model.vs_allocas /\
   allocated_s.vs_alloca_next = alloc_model.vs_alloca_next` by simp[Abbr `alloc_model`] >>
  `p = w2n outw` by
    (qpat_assum `FLOOKUP allocated_s.vs_allocas _ = _` mp_tac >>
     qpat_assum `allocated_s.vs_allocas = alloc_model.vs_allocas`
       (fn th => pure_rewrite_tac [th]) >> strip_tac >> gvs[]) >>
  `alloca_inv allocated_s /\ alloca_room ctx func allocated_s` by
    metis_tac[localPtrsPropsTheory.alloca_inv_fields, exprLoweringPropsTheory.alloca_room_fields] >>
  `~allocated_s.vs_halted /\ allocated_s.vs_memory = s.vs_memory` by
    (qpat_assum `allocated_s with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s`
       (fn th => mp_tac (Q.AP_TERM `\st. st.vs_halted` th) >>
                 mp_tac (Q.AP_TERM `\st. st.vs_memory` th)) >> simp[]) >>
  `lo <= w2n outw` by
    (qpat_assum `allocas_from lo allocated_s`
       (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
     disch_then (qspecl_then [`sm.cs_next_id`, `w2n outw`, `outsz`] mp_tac) >> simp[]) >>
  suspend "setup"
QED

Resume abi_encode_nonword_ready_origin[setup]:
  `lookup_var q allocated_s = SOME (n2w (w2n outw))` by simp[] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w outsz)] [q]) (fn_insts func)` by
    (drule abiBufferAllocationCodeTheory.compile_alloc_buffer_code >>
     qpat_assum `buf.buf_operand = Var q`
       (fn th => rewrite_tac [th, venomStateTheory.operand_11]) >> strip_tac >>
     irule materializeSeparationTheory.fn_has_code_current_instruction >>
     qexistsl_tac [`sm`, `allocated`] >>
     simp_tac bool_ss [] >> rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (qpat_assum `emitted_insts sm allocated = [_]`
           (fn th => rewrite_tac [th, listTheory.MEM]) >>
         qpat_assum `q = STRING _ _` (fn th => rewrite_tac [th]))
     >> first_assum ACCEPT_TAC) >>
  qpat_assum `buf.buf_operand = Var q` (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  drule_at (Pat `emit_op _ _ _ = _`) abi_encode_setup_tail_origin >>
  disch_then (drule_at (Pat `abi_builtin_encode_method_id _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers G2 tn2 q allocated_s outsz`)) >>
  disch_then (drule_at (Pat `fn_has_code allocated ready func`)) >>
  disch_then (drule_at (Pat `allocas_from lo allocated_s`)) >>
  simp[Abbr `outsz`] >>
  disch_then (qspec_then `w2n outw` mp_tac) >>
  disch_then (qspec_then `abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)` mp_tac) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `ctx`, `PG`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  rename1 `ptr_covers setupG setupTN dp setup_s _` >>
  `val_wf tv v` by metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `!mem. mem_agree_outside tn2.t_mem allocated_s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem` by
    (rpt strip_tac >> irule ghostObservationPtrTheory.robust_val_in_memory_exterior_no_new_taint >>
     simp[] >>
     qexistsl_tac [`{i | s.vs_alloca_next <= i}`, `s.vs_memory`,
       `allocated_s.vs_memory`, `tn1.t_mem`, `tn2.t_mem`] >> simp[] >> metis_tac[]) >>
  `setupTN.t_mem SUBSET tn2.t_mem` by
    (qpat_assum `setupTN.t_mem = _` (fn th => rewrite_tac[th]) >> simp[pred_setTheory.DIFF_SUBSET]) >>
  `32 + (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 32) <=
   32 + 32 * word_size (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) +
       (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4))` by
    (qpat_assum `32 + (case mid of NONE => 0 | SOME _ => 32) <= _` mp_tac >>
     Cases_on `mid` >> simp[NoAsms]) >>
  `!mem. mem_agree_outside setupTN.t_mem setup_s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem` by
    (qpat_assum `p = w2n outw` SUBST_ALL_TAC >>
     qpat_assum `val_footprint ptv v = val_footprint tv v`
       (fn th => rule_assum_tac (REWRITE_RULE[th])) >>
     rpt strip_tac >> irule abi_encode_setup_source_robust >>
     qpat_assum `typed_copy_state_frame allocated _ _ allocated_s setup_s`
       (irule_at Any) >>
     qpat_assum `setupTN.t_mem SUBSET tn2.t_mem` (irule_at Any) >>
     qpat_assum `venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) _`
       (irule_at Any) >> simp[] >> Cases_on `mid` >> simp[NoAsms]) >>
  suspend "translate_ready"
QED

Resume abi_encode_nonword_ready_origin[translate_ready]:
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    (qhdtm_assum `exprSimHypsDefs$expr_body_pre` mp_tac >>
     simp[NoAsms, exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  `!t tv'. evaluate_type (get_tenv cx) t = SOME tv' ==>
      type_memory_bytes ce t = type_memory_size tv'` by
    metis_tac[abi_encode_body_evaluated_metadata] >>
  `?ct rv. enc ct rv = enc (vyper_to_abi_type (get_tenv cx)
        (lowered_value_type ce e)) av /\
     !mem. mem_agree_outside setupTN.t_mem setup_s.vs_memory mem ==>
       abi_encoder_window_input
         (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e))
         ct rv (w2n w) (val_footprint tv v) mem` by
    (irule abi_encode_uniform_translated_footprint_window >>
     simp[] >> qexists_tac `get_tenv cx` >> simp[]) >>
  `32 + (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4) +
    LENGTH (enc ct rv) <= 32 + 32 * word_size
      (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) +
         (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4))` by
    (qpat_assum `enc ct rv = _` SUBST1_TAC >>
     qpat_assum `vyper_to_abi_type _ (lowered_value_type ce e) = _` SUBST1_TAC >>
     qpat_assum `32 + (case mid of NONE => 0 | SOME _ => 4) + _ <= _` mp_tac >>
     Cases_on `mid` >> simp[NoAsms]) >>
  suspend "package"
QED

Resume abi_encode_nonword_ready_origin[package]:
  qexistsl_tac [`body_end`, `len`, `dp`, `w2n outw`, `w2n w`,
    `ct`, `rv`, `setup_s`, `setupG`, `setupTN`] >>
  qpat_assum `data_ptr = Var dp` SUBST_ALL_TAC >>
  qpat_assum `p = w2n outw` SUBST_ALL_TAC >>
  rule_assum_tac (REWRITE_RULE [pairTheory.FST, pairTheory.SND]) >>
  `sm.cs_next_var <= allocated.cs_next_var` by
    (qmatch_asmsub_abbrev_tac `compile_alloc_buffer N sm = (_,allocated)` >>
     mp_tac (Q.SPECL [`N`, `sm`] exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `sm.cs_next_var <= ready.cs_next_var` by
    (drule abiBuiltinEncodeCodeTheory.abi_builtin_encode_setup_shape >> strip_tac >> simp[]) >>
  `local_ptrs_reserved ce ready` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  `(!x. not_fresh_at sa x ==> not_fresh_at ready x) /\
   (!x. not_fresh_at sm x ==> not_fresh_at allocated x) /\
   (!x. not_fresh_at sm x ==> not_fresh_at ready x)` by
    (rpt conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >-
      (qexists_tac `sa` >> simp[] >> decide_tac) >> qexists_tac `sm` >> simp[]) >>
  `alloca_room ctx func setup_s` by
    (irule exprLoweringPropsTheory.alloca_room_fields >> qexists_tac `allocated_s` >> simp[]) >>
  `s.vs_alloca_next <= setup_s.vs_alloca_next` by simp[] >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G1,tn1) [] (OK setup_s,setupG,setupTN)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`G2`, `allocated_s`, `tn2`] >> simp[]) >>
  suspend "ready_resources"
QED

Resume abi_encode_nonword_ready_origin[ready_resources]:
  qpat_assum `ops = (Var q,Var dp)` SUBST_ALL_TAC >>
  rule_assum_tac (REWRITE_RULE [pairTheory.FST, pairTheory.SND]) >>
  `allocated.cs_next_var <= ready.cs_next_var` by
    (drule abiBufferAllocationCodeTheory.compile_alloc_buffer_code >> strip_tac >>
     drule abiBuiltinEncodeCodeTheory.abi_builtin_encode_setup_shape >>
     Cases_on `mid` >> simp[]) >>
  `not_fresh_at ready q` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `allocated` >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x setup_s = lookup_var x s /\
       FLOOKUP setupG x = FLOOKUP G1 x /\
       op_taint setupTN (Var x) = op_taint tn1 (Var x)` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at allocated x` by
       (qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at allocated x` irule >> simp[]) >>
     qpat_assum `!op. _ ==> eval_operand op setup_s = _ /\ _`
       (qspec_then `Var x` (mp_tac o SRULE [venomStateTheory.eval_operand_def,
         ptrDisciplineTheory.op_prov_def])) >>
     (impl_tac >- simp[]) >>
     disch_then (EVERY o map assume_tac o CONJUNCTS) >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x allocated_s = _ /\ _`
       (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (EVERY o map assume_tac o CONJUNCTS) >> simp[]) >>
  `allocated_s.vs_labels = s.vs_labels` by
    (qpat_assum `allocated_s with <|vs_vars := _; vs_allocas := _;
            vs_alloca_next := _; vs_inst_idx := _|> = s`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_labels``) >> simp[]) >>
  `eval_operand op allocated_s = eval_operand op s /\
    op_taint tn2 op = op_taint tn1 op` by
    (qpat_x_assum `eval_operand op s = SOME w` kall_tac >>
     qpat_x_assum `op_taint tn1 op = {}` kall_tac >>
     Cases_on `op` >- simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def]
     >~ [`eval_operand (Var x) _ = _ /\ _`] >-
       (qpat_assum `!x. not_fresh_at sm x ==> lookup_var x allocated_s = _ /\ _`
          (qspec_then `x` mp_tac) >>
        (impl_tac >- (qpat_assum `!y. Var x = Var y ==> _` (qspec_then `x` mp_tac) >> simp[])) >>
        simp[venomStateTheory.eval_operand_def]) >>
     simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def]) >>
  `eval_operand op setup_s = SOME (n2w (w2n w)) /\ op_taint setupTN op = {}` by
    (qpat_assum `!op. _ ==> eval_operand op setup_s = _ /\ _`
      (qspec_then `op` mp_tac) >>
     (impl_tac >- (rpt strip_tac >> first_assum irule >> simp[])) >>
     disch_then (EVERY o map assume_tac o CONJUNCTS) >> simp[]) >>
  `enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av` by simp[] >>
  `LENGTH (enc ct rv) <= abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)` by simp[] >>
  qmatch_asmsub_abbrev_tac `compile_alloc_buffer N sm = _` >>
  qpat_abbrev_tac `k = (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4)` >>
  qpat_abbrev_tac `mw = (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 32)` >>
  `0 < val_footprint tv v ==> w2n w+val_footprint tv v <= setup_s.vs_alloca_next /\
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv v)
         (w2n outw+32+k,LENGTH (enc ct rv)) /\
      ?x. op = Var x /\ ptr_covers setupG setupTN x setup_s (val_footprint tv v)` by
    (strip_tac >>
     `0 < val_footprint ptv v` by simp[] >>
     qpat_assum `0 < val_footprint ptv v ==> _` drule >> strip_tac >>
     conj_tac >- (simp[] >> decide_tac) >>
     conj_tac >-
       (qpat_assum `32+k+LENGTH (enc ct rv) <= N` mp_tac >>
        qpat_assum `venomMemDefs$regions_disjoint (_,val_footprint ptv v) (_,N)` mp_tac >>
        qpat_assum `val_footprint ptv v = val_footprint tv v`
          (fn th => pure_rewrite_tac [th, venomMemDefsTheory.regions_disjoint_def]) >>
        decide_tac) >>
     `0 < type_memory_size tv` by decide_tac >>
     qpat_assum `0 < type_memory_size tv ==> _` drule >> strip_tac >>
     qexists_tac `x` >> ASM_REWRITE_TAC [] >>
     `not_fresh_at sm x` by metis_tac[] >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x setup_s = _ /\ _`
       (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (EVERY o map assume_tac o CONJUNCTS) >>
     irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `type_memory_size tv` >>
     conj_tac >- simp[] >>
     irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`G1`, `s`, `tn1`] >> ASM_REWRITE_TAC []) >>
  suspend "ready_scratch"
QED

Resume abi_encode_nonword_ready_origin[ready_scratch]:
  `FLOOKUP setup_s.vs_allocas sm.cs_next_id = SOME (w2n outw,N)` by simp[] >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids ready body_end /\
      FLOOKUP setup_s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (b,sz) /\
      venomMemDefs$regions_disjoint (w2n outw+32+k,LENGTH (enc ct rv)) (b,sz) /\
      venomMemDefs$regions_disjoint (w2n outw+32,mw) (b,sz)` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP (abi_builtin_allocate_state sm.cs_next_id N s).vs_allocas inst.inst_id =
        SOME (b,sz)` by metis_tac[] >>
     `!j. MEM j (fn_insts func) /\ j.inst_opcode <> STOP /\
        j.inst_opcode <> NOP ==> MEM j (fn_insts func)` by simp[] >>
     drule_all (Q.INST [`obs` |-> `func`] abi_encode_nonword_scratch_row) >>
     strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qpat_assum `val_footprint ptv v = val_footprint tv v`
          (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     drule_all abi_encode_setup_scratch_slices >>
     simp[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  suspend "ready_frames"
QED

Resume abi_encode_nonword_ready_origin[ready_frames]:
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at allocated x` by
    (rpt strip_tac >> first_assum irule >> simp[]) >>
  `local_ptrs_reserved ce allocated` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  `!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at allocated x` by
    (rpt strip_tac >> qpat_assum `local_ptrs_reserved ce allocated`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o
         REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
     disch_then (qspecl_then [`name`,`name`,`x`,`sz`,`sz`] mp_tac) >> simp[]) >>
  `!x. not_fresh_at allocated x ==> lookup_var x setup_s = lookup_var x allocated_s` by
    (qx_gen_tac `old` >> disch_tac >>
     `eval_operand (Var old) setup_s = eval_operand (Var old) allocated_s` by
       (irule typedMemoryCopyTheory.typed_copy_state_frame_operand >>
        qpat_assum `typed_copy_state_frame allocated _ _ allocated_s setup_s` (irule_at Any) >>
        simp[]) >>
     pop_assum (ACCEPT_TAC o REWRITE_RULE [venomStateTheory.eval_operand_def])) >>
  `!name b sz. (local_region ce ee.scopes setup_s name b sz <=>
       local_region ce ee.scopes allocated_s name b sz)` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     rpt strip_tac >>
     qpat_assum `!x. not_fresh_at allocated x ==> lookup_var x setup_s = _` irule >>
     qpat_assum `!name x sz. FLOOKUP ce.ce_vars name = _ ==> not_fresh_at allocated x`
       (drule_then ACCEPT_TAC)) >>
  `32+mw <= N` by simp[] >>
  `!b sz. regions_disjoint (w2n outw) N b sz ==>
       regions_disjoint (w2n outw+32) mw b sz` by
    (pure_rewrite_tac [loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!name b sz. local_region ce ee.scopes allocated_s name b sz ==>
       regions_disjoint (w2n outw+32) mw b sz` by
    ((rpt strip_tac >> first_assum irule >> simp[] >> (metis_tac[]))) >>
  `copy_static setup_s = copy_static allocated_s /\
   LENGTH allocated_s.vs_memory <= LENGTH setup_s.vs_memory /\
   (!b sz. regions_disjoint (w2n outw+32) mw b sz ==>
       mem_bytes_at b sz setup_s.vs_memory = mem_bytes_at b sz allocated_s.vs_memory)` by
    (qpat_assum `typed_copy_state_frame allocated _ _ allocated_s setup_s`
       (strip_assume_tac o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
         typedMemoryCopyTheory.typed_copy_frame_def]) >>
     conj_tac >-
       (qpat_assum `setup_s with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
                                     vs_current_bb := _; vs_inst_idx := _|> = allocated_s` mp_tac >>
        simp[NoAsms, exprSimStorageCopyTheory.copy_static_def,
          venomStateTheory.venom_state_component_equality] >> strip_tac >> ASM_REWRITE_TAC []) >>
     pure_rewrite_tac [loweringStateRelDefsTheory.regions_disjoint_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!a n. _ \/ _ ==> mem_bytes_at a n setup_s.vs_memory = _`
       (mp_tac) >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!b sz. regions_disjoint (w2n outw+32) mw b sz ==>
       mem_bytes_at b sz setup_s.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (qpat_assum `allocated_s.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `!i. i < s.vs_alloca_next /\ ~(w2n outw+32 <= i /\ i < w2n outw+32+mw) ==>
       (i IN setupTN.t_mem <=> i IN tn1.t_mem)` by
    (qx_gen_tac `i` >> strip_tac >>
     `~(w2n outw+32 <= i /\ i < w2n outw+(mw+32))` by decide_tac >>
     `~(s.vs_alloca_next <= i)` by decide_tac >>
     qpat_assum `setupTN.t_mem = _` (fn th => rewrite_tac [th, pred_setTheory.IN_DIFF,
       pred_setTheory.IN_GSPEC_IFF]) >>
     qpat_assum `!i. i IN tn2.t_mem <=> _` (qspec_then `i` (fn th => pure_rewrite_tac [th])) >>
     simp[pred_setTheory.IN_GSPEC_IFF]) >>
  suspend "ready_semantic"
QED

Resume abi_encode_nonword_ready_origin[ready_semantic]:
  `!a sz. a+sz <= w2n outw \/ w2n outw+N <= a ==>
      mem_bytes_at a sz setup_s.vs_memory = mem_bytes_at a sz allocated_s.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!b sz. regions_disjoint (w2n outw+32) mw b sz ==>
       mem_bytes_at b sz setup_s.vs_memory = mem_bytes_at b sz allocated_s.vs_memory` irule >>
     qpat_assum `!b sz. regions_disjoint (w2n outw) N b sz ==> _` irule >>
     pop_assum mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> tautLib.TAUT_TAC) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func ce cx ee setup_s /\
       ghost_inv_at (DF H) lo d ce cx ee setupG setupTN setup_s` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
       (drule_then strip_assume_tac) >>
     `stmt_state_rel H ctx func ce cx ee s` by
       (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
         (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [loweringPostsTheory.expr_post_def])) >>
     `stmt_state_rel H ctx func ce cx ee allocated_s` by
       (qpat_assum `!J. stmt_state_rel J ctx func ce cx ee s ==>
                         stmt_state_rel J ctx func ce cx ee allocated_s`
          (qspec_then `H` mp_tac) >>
        pop_assum mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
        tautLib.TAUT_TAC) >>
     conj_tac >-
       (irule (Q.INST [`u` |-> `allocated_s`, `sh` |-> `allocated`,
          `sa` |-> `allocated`, `b` |-> `w2n (outw:256 word)`, `n` |-> `N`,
          `aid` |-> `sm.cs_next_id`, `p` |-> `q`] literal_copy_window_stmt_state_rel) >>
        qexistsl_tac [`N`,`allocated`,`allocated_s`,`outw`,`q`,`sm`] >>
        ASM_REWRITE_TAC []) >>
     `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
       (rpt strip_tac >>
        qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` irule >> metis_tac[]) >>
     `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
       (rpt strip_tac >>
        qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` irule >> metis_tac[]) >>
     `ghost_inv_at (DF H) lo d ce cx ee G2 tn2 allocated_s` by
       (drule_all bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at >> simp[]) >>
     `local_ptrs_rel func ce ee.scopes allocated_s` by
       (qpat_assum `stmt_state_rel H ctx func ce cx ee allocated_s`
          (ACCEPT_TAC o CONJUNCT1 o MATCH_MP stmt_state_rel_local_ptrs_alloca)) >>
     `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at allocated x` by
       (rpt strip_tac >>
        qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at allocated x` irule >> simp[]) >>
     `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at allocated x` by
       (rpt strip_tac >>
        qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at allocated x` irule >> simp[]) >>
     `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at allocated x` by
       (rpt strip_tac >> drule_all exprLoweringPropsTheory.local_ptrs_reserved_imm_base >> simp[]) >>
     qpat_assum `!D d ce cx es. _ ==> ghost_inv_at D lo d ce cx es setupG setupTN setup_s` irule >>
     ASM_REWRITE_TAC []) >>
  suspend "ready_kept"
QED

Resume abi_encode_nonword_ready_origin[ready_kept]:
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,ee with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL]))) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (`expr_body_pre ce cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) abiEncodeArgsCaseTheory.abi_args_success_ready) >>
     disch_then (mp_tac o CONJUNCT1 o CONJUNCT2) >> simp[NoAsms]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
        simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
             vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
     drule_at (Pat `f st = (res,st')`) vyperStorageFootprintTheory.valid_horizon_frame >>
     simp[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx es s0` by simp[] >>
  `alloca_inv s0` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s0`
       (ACCEPT_TAC o CONJUNCT2 o MATCH_MP stmt_state_rel_local_ptrs_alloca)) >>
  `!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id ==>
       b+sz <= s.vs_alloca_next` by
    (rpt strip_tac >>
     `b+sz <= s0.vs_alloca_next` by
       (qpat_assum `alloca_inv s0` mp_tac >>
        simp[NoAsms, venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
        strip_tac >> first_assum (drule_then ACCEPT_TAC)) >> decide_tac) >>
  `!name b sz. local_region ce es.scopes s0 name b sz ==> b+sz <= s.vs_alloca_next` by
    (rpt strip_tac >>
     `b+sz <= s0.vs_alloca_next` by
       (drule_all abiEncodeOwnershipTheory.abi_encode_local_region_frontier >> simp[]) >>
     decide_tac) >>
  `!x. not_fresh_at sa x ==>
       FLOOKUP G2 x = FLOOKUP G1 x /\ op_taint tn2 (Var x) = op_taint tn1 (Var x)` by
    (qx_gen_tac `old` >> disch_tac >>
     `not_fresh_at sm old` by
       (qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` (drule_then ACCEPT_TAC)) >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x allocated_s = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 G2 tn2` by
    (irule bodyFullAllocaFreshTheory.alloc_buffer_ghost_kept_at >>
     qexistsl_tac [`G1`, `w2n outw+N`, `s`, `tn1`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 setupG setupTN` by
    (qpat_assum `!ce es origin G0 tn0 s0. ghost_kept_at _ _ _ _ _ _ _ G2 tn2 /\ _ ==> _` irule >>
     ASM_REWRITE_TAC []) >>
  suspend "ready_writeback"
QED

Resume abi_encode_nonword_ready_origin[ready_writeback]:
  `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
       FLOOKUP setup_s.vs_allocas aid = SOME row` by
    (qpat_assum `setup_s.vs_allocas = alloc_model.vs_allocas` SUBST1_TAC >>
     qpat_assum `allocated_s.vs_allocas = alloc_model.vs_allocas` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `!name b sz. local_region ce ee.scopes allocated_s name b sz <=>
       local_region ce ee.scopes s name b sz` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     rpt strip_tac >> rename1 `FLOOKUP ce.ce_vars nm = SOME (PtrVar (Var old) width)` >>
     `not_fresh_at sm old` by
       (qpat_assum `local_ptrs_reserved ce sm`
          (mp_tac o CONJUNCT1 o CONJUNCT2 o
           REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
        disch_then (qspecl_then [`nm`,`nm`,`old`,`width`,`width`] mp_tac) >> simp[]) >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x allocated_s = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `wb_frame ce es ee sa s0 s` by
    (qpat_assum `expr_post _ ctx func ce cx e es sa sm s0 ee v op s`
       (ACCEPT_TAC o MATCH_MP exprSimWordArgsTheory.expr_post_frame)) >>
  `wb_frame ce es ee sa s0 setup_s` by
    (irule exprSimHashTheory.wb_frame_allocating_tail >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`s`, `ee.scopes`, `sm`] >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x setup_s = _ /\ _`
       (assume_tac o cj 1) >>
     ASM_REWRITE_TAC [] >> conj_tac >-
       (map_every qx_gen_tac [`nm`, `lb`, `lsz`] >> disch_tac >>
        qpat_assum `!b sz. regions_disjoint (w2n outw+32) mw b sz ==>
               mem_bytes_at b sz setup_s.vs_memory = mem_bytes_at b sz s.vs_memory` irule >>
        qpat_assum `!name b sz. local_region ce ee.scopes allocated_s name b sz ==>
                    regions_disjoint (w2n outw+32) mw b sz`
          (qspecl_then [`nm`, `lb`, `lsz`] irule) >>
        qpat_assum `!name b sz. local_region ce ee.scopes allocated_s name b sz <=> _`
          (fn th => pure_rewrite_tac [th]) >> qexists_tac `nm` >>
        first_assum ACCEPT_TAC) >>
     map_every qx_gen_tac [`id`, `lb`, `lsz`] >> disch_tac >>
     qpat_assum `!b sz. regions_disjoint (w2n outw+32) mw b sz ==>
              mem_bytes_at b sz setup_s.vs_memory = mem_bytes_at b sz s.vs_memory` irule >>
     qpat_assum `!b sz. regions_disjoint (w2n outw) N b sz ==> _` irule >>
     qpat_assum `!aid b sz. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> _`
       (qspecl_then [`id`, `lb`, `lsz`] irule) >> qexists_tac `id` >>
     first_assum ACCEPT_TAC) >>
  suspend "ready_package"
QED

Resume abi_encode_nonword_ready_origin[ready_package]:
  `32 * word_size (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) + k) + 32 = N` by
    (qpat_assum `Abbrev (N = _)` (fn th => rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     irule arithmeticTheory.ADD_COMM) >>
  `w2n outw + (k+32) = w2n outw + 32 + k` by decide_tac >>
  `LENGTH (enc ct rv) + (k+32) = 32+k+LENGTH (enc ct rv)` by decide_tac >>
  `!x. op = Var x ==> not_fresh_at ready x` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at ready x` irule >> simp[]) >>
  `!name b sz. local_region ce ee.scopes setup_s name b sz ==>
       regions_disjoint (w2n outw) N b sz` by
    (qpat_assum `!name b sz. local_region ce ee.scopes setup_s name b sz <=> _`
       (fn th => pure_rewrite_tac [th]) >> first_assum ACCEPT_TAC) >>
  `w2n outw + N <= setup_s.vs_alloca_next` by
    (qpat_assum `setup_s.vs_alloca_next = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `setup_s.vs_allocas = _` kall_tac >>
  qpat_x_assum `setup_s.vs_alloca_next = _` kall_tac >>
  qpat_x_assum `setupTN.t_mem = _` kall_tac >>
  qpat_x_assum `!name b sz. local_region ce ee.scopes setup_s name b sz <=> _` kall_tac >>
  ASM_REWRITE_TAC [] >>
  conj_tac >-
    (qpat_assum `enc ct rv = enc (vyper_to_abi_type _ (expr_type e)) av`
       (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `32 * word_size _ + 32 = N` (fn th =>
       qpat_assum `32 + mw <= N` (mp_tac o PURE_REWRITE_RULE [SYM th])) >> decide_tac) >>
  conj_tac >-
    (qpat_assum `enc ct rv = enc (vyper_to_abi_type _ (expr_type e)) av`
       (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `enc ct rv = enc (vyper_to_abi_type _ (expr_type e)) av`
       (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> (i IN setupTN.t_mem <=> _)`
    (qspec_then `i` irule) >> decide_tac
QED

Finalise abi_encode_nonword_ready_origin
