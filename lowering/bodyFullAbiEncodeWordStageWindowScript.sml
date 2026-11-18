Theory bodyFullAbiEncodeWordStageWindow
Ancestors
  bodyFullAbiEncodeWordStage exprSimAbiEncodeRuntimeInputs
  exprSimAbiEncodePrefixWindow exprSimSource exprSimLayoutTransport exprOperandVar
  abiBuiltinEncodeWord abiTupleValueEncoding abiEncoderAdmissible
  abiEncoderStaticRepresentative abiEncoderWindow abiStaticAggregateProps
  entryDecodeProps valueEncodingProps valueEncodingProofs
  vyperTypeABI vyperStorageTrace vyperStorageFootprint exprBopSimProps
  exprSimHyps exprLoweringProps loweringPosts bodyPtrDefs compileEnv freshWrites exprSimWordArgs
  contractABI byte list arithmetic

(* The padded byte window is exactly 32 bytes in every agreeing memory,
   even if that memory omits trailing zero bytes physically present after MSTORE. *)
Theorem abi_encode_word_stage_window_origin:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  is_word_type (expr_type e) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (INL v,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func ce cx e es sa sm s0 ee v op t /\
    ghost_inv_at (DF H) lo d ce cx ee G1 tn1 t /\
    ptr_val_ok cx (post_value_type ce e) v op G1 tn1 t /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G1 tn1) /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  compile_alloc_buffer 32 sm = (buf,sn) /\
  emit_void MSTORE [buf.buf_operand;op] sn = ((),sh) /\
  fn_has_code sm sh func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q b u Gu tnu ct rv av.
    vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av /\
    LENGTH (enc ct rv) = 32 /\ abi_encoder_admissible (AbiCopy 32) /\
    type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e) = AbiCopy 32 /\
    abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) = 32 /\
    (!mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==>
       abi_encoder_window_input (AbiCopy 32) ct rv b 32 mem) /\
    buf.buf_operand = Var q /\ not_fresh_at sh q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (t,G1,tn1) [] (OK u,Gu,tnu)) /\
    ~u.vs_halted /\ u.vs_current_bb = sh.cs_current_bb /\
    u.vs_inst_idx = LENGTH sh.cs_current_insts /\
    eval_operand (Var q) u = SOME (n2w b) /\ ptr_covers Gu tnu q u 32 /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,32) /\
    sm.cs_next_id < sh.cs_next_id /\ b+32 < dimword(:256) /\
    b+32 <= u.vs_alloca_next /\ lo <= u.vs_alloca_next /\
    alloca_history func u /\ allocas_from lo u /\
    t.vs_alloca_next <= u.vs_alloca_next /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    local_ptrs_reserved ce sh /\ cs_extends sa sh /\
    sa.cs_next_var <= sh.cs_next_var /\ sa.cs_next_id <= sh.cs_next_id /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sh x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sh x) /\
    (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sh x) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func ce cx ee u /\
       ghost_inv_at (DF H) lo d ce cx ee Gu tnu u) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gu tnu /\ wb_frame ce es ee sa s0 u /\
    (~expr_has_effect e ==> pure_frame ce func es sa s0 u)
Proof
  strip_tac >>
  `expr_body_pre ce cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    (drule_at (Pat `bind _ _ _ = _`) (SRULE [SF ETA_ss] abi_encode_operand_success_type) >>
     simp[] >> metis_tac[]) >>
  `?av. vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av` by
    metis_tac[cj 1 vyper_to_abi_total] >>
  drule_all vyper_to_abi_word_enc >> strip_tac >>
  `is_word_type (lowered_value_type ce e)` by
    metis_tac[expr_body_pre_lowered_fits, compatible_word_type] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by
    (drule_at (Pat `f st = _`) valid_horizon_frame >>
     simp[storage_trace_frame_bind_all, cj 5 evaluate_storage_trace_frame,
          storage_trace_frame_read_result]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx es s0 /\
   stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee t /\
   wb_frame ce es ee sa s0 t /\
   (~expr_has_effect e ==> pure_frame ce func es sa s0 t)` by
    (drule expr_post_frame >>
     qhdtm_assum `expr_post`
       (strip_assume_tac o SRULE [expr_post_def]) >> simp[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `op_taint tn1 op = {}` by fs[ptr_val_ok_def] >>
  `eval_operand op t = SOME (typed_val_to_w256 tv v)` by
    ((irule expr_val_rel_typed >> qexistsl_tac [`cx`,`expr_type e`] >>
     fs[expr_post_def, post_value_type_word] >> (gvs[expr_post_def, post_value_type_word, expr_val_rel_typed]))) >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
  `cs_extends sm sh` by (irule cs_extends_same_block >> simp[]) >>
  `cs_extends sa sh` by metis_tac[cs_extends_trans] >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sh` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD] >>
  `!x. op = Var x ==> not_fresh_at sm x` by metis_tac[compile_lower_value_var] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[not_fresh_at_mono] >>
  drule_all abi_encode_word_stage_origin >>
  disch_then (qspecl_then [`d`,`explicit`,`PG`] strip_assume_tac) >>
  suspend "window"
QED

Resume abi_encode_word_stage_window_origin[window]:
  qabbrev_tac `bs = word_to_bytes (typed_val_to_w256 tv v) T` >>
  `LENGTH bs = 32` by simp[Abbr `bs`, LENGTH_word_to_bytes] >>
  drule abi_encoder_bytes32_representative >> strip_tac >>
  `!mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==>
     mem_bytes_at b 32 mem = bs` by
    (rpt strip_tac >>
     `mem_word_at b mem = typed_val_to_w256 tv v` by simp[] >>
     qpat_x_assum `mem_word_at b mem = _` mp_tac >>
     rewrite_tac[mem_word_at_bytes, GSYM word_of_bytes_be_def] >>
     disch_then (mp_tac o AP_TERM ``word_to_bytes_be : bytes32 -> byte list``) >>
     mp_tac (Q.SPEC `mem_bytes_at b 32 mem` TAKE_word_to_bytes_be_word_of_bytes_be) >>
     simp[LENGTH_mem_bytes_at, listTheory.TAKE_LENGTH_ID_rwt, Abbr `bs`, word_to_bytes_be_def]) >>
  qexistsl_tac [`q`,`b`,`u`,`Gu`,`tnu`,`Bytes (SOME 32)`,`contractABI$BytesV bs`,`av`] >>
  simp[abi_encoder_window_copy_iff, abi_encoder_admissible_def,
       abi_word_metadata, abi_encode_word_size_bound] >>
  rpt conj_tac
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sm` >> simp[])
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sm` >> simp[])
  >- metis_tac[local_ptrs_reserved_imm_base]
  >- (qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      metis_tac[expr_post_state])
QED

Finalise abi_encode_word_stage_window_origin
