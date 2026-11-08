(* Source conversion and canonical calldata at the same ghost endpoint. *)
Theory sourceWordDecoderPtr
Ancestors calldataTypedRobustPtr entryDecodeProps abiCanonicalHeadSize
  abiStaticAggregateProps byte words valueEncoding bodyPtrDefs
  calldataWordPtr abiDecoderContract list valueEncodingProofs
  abiDecoderPrimitiveCaller abiDecoderNumericWord abiDecoderSigned
  abiDecoderFixedBytes abiDecoderCoherence abiDecoderWordTyped
  vyperABI vyperTyping contractABI exprLowering abiDecoderClamp compileEnv vyperValue arithmetic

Theorem calldata_source_word_ptr_endpoint:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w)
    (DecPrimWord clamp) sa = ((),sb) /\
  abi_decoder_clamp_valid clamp (abi_decode_load CALLDATALOAD sw s) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s 32 /\
  op_taint tn src = {} /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  is_word_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  sw = n2w srcpos /\ srcpos < dimword (:256) /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    s.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' 32 /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    mem_word_at (w2n dw) s'.vs_memory = abi_decode_load CALLDATALOAD sw s /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    val_in_memory tv v (w2n dw) s'.vs_memory /\
    (!mem. mem_agree_outside tn'.t_mem s'.vs_memory mem ==>
      val_in_memory tv v (w2n dw) mem)
Proof
  strip_tac >>
  `enc (vyper_to_abi_type env ty) av = word_to_bytes (typed_val_to_w256 tv v) T` by
    metis_tac[vyper_to_abi_word_enc] >>
  `abi_decode_load CALLDATALOAD sw s = typed_val_to_w256 tv v` by
    (gvs[] >> simp[abi_decode_load_bytes, abi_decode_source_def,
      LENGTH_word_to_bytes, word_of_bytes_word_to_bytes]) >>
  drule_all calldata_clamped_word_prefix_framed >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `s'` (qx_choose_then `G'`
      (qx_choose_then `tn'` strip_assume_tac)))) >>
  `val_in_memory tv v (w2n dw) s'.vs_memory` by
    metis_tac[val_in_memory_word] >>
  qexistsl_tac [`s'`, `G'`, `tn'`] >> simp[] >>
  rpt strip_tac >>
  `mem_bytes_at (w2n dw) 32 s'.vs_memory = mem_bytes_at (w2n dw) 32 mem` by
    (irule LIST_EQ >> simp[] >> rpt strip_tac >>
     rename1 `j < 32` >>
     `w2n dw+j NOTIN tn'.t_mem` by
       (first_x_assum irule >> decide_tac) >>
     `mem_bytes_at (w2n dw+j) 1 s'.vs_memory =
      mem_bytes_at (w2n dw+j) 1 mem` by
       metis_tac[mem_agree_outside_def] >>
     pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  metis_tac[val_in_memory_word, mem_word_at_bytes]
QED

Theorem coherent_source_word_clamp:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  srcpos < dimword (:256) /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    (abi_decode_source opc s) = enc (vyper_to_abi_type env ty) av ==>
  abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w srcpos : bytes32) s)
Proof
  strip_tac >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
    (drule_all vyper_to_abi_word_enc >> simp[]) >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >> gvs[]
  >- (rename1 `is_word_type (BaseT bt)` >>
      `type_to_abi_dec_info sf ce (BaseT bt) =
        DecPrimWord (type_to_abi_clamp (BaseT bt))` by
        metis_tac[abi_decoder_base_word_info] >>
      (gvs[] >> Cases_on `bt` >> gvs[is_word_type_def] >>
      FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
      gvs[is_word_type_def] >> Cases_on `v` >>
      gvs[value_has_type_def, vyper_to_abi_base_def,
          abi_decoder_coherent_base_iff, abi_decoder_scalar_valid_def] >>
      gvs[evaluate_type_def, AllCaseEqs()]) >- (irule abi_decoder_canonical_uint_clamp >> simp[] >>
           qexists_tac `NumV (Num i)` >>
           simp[has_type_def, valid_int_bound_def, enc_def, enc_number_def])
       >- (irule abi_decoder_canonical_int_clamp >> simp[valid_int_bound_def] >>
           qexists_tac `i` >>
           simp[valid_int_bound_def, enc_def, enc_number_def])
       >- (simp[type_to_abi_clamp_def] >>
           irule abi_decoder_canonical_bool_clamp >> simp[] >>
           qexists_tac `NumV (if b then 1 else 0)` >>
           Cases_on `b` >> simp[has_type_def, enc_def, enc_number_def])
       >- (simp[type_to_abi_clamp_def] >>
           irule abi_decoder_canonical_decimal_clamp >> simp[] >>
           qexists_tac `i` >> simp[enc_def, enc_number_def])
       >- (rename1 `LENGTH bs <= 32` >>
           `abi_decode_load opc (n2w srcpos : bytes32) s = word_of_bytes T 0w bs` by
             (simp[abi_decode_load_bytes, TAKE_LENGTH_TOO_LONG,
                   word_of_bytes_append_zero]) >>
           drule abi_decoder_fixed_bytes_shift_zero >>
           Cases_on `LENGTH bs = 32` >>
           simp[type_to_abi_clamp_def, abi_decoder_clamp_valid_def]) >>
       simp[type_to_abi_clamp_def] >>
       irule abi_decoder_canonical_address_clamp >> simp[] >>
       qexists_tac `NumV (w2n (word_of_bytes_be l : address))` >>
       simp[has_type_def, enc_def, enc_number_def, GSYM dimword_def] >>
       mp_tac (Q.ISPEC `word_of_bytes_be l : address` w2n_lt) >>
       simp[dimword_def, fcpLib.INDEX_CONV ``dimindex(:160)``]) >>
  gvs[abi_decoder_coherent_flag_iff] >>
  Cases_on `v` >>
  gvs[value_has_type_def, vyper_to_abi_def, Once type_to_abi_dec_info_def] >>
  `abi_decode_load opc (n2w srcpos : bytes32) s = n2w n` by
    (irule abi_decoder_canonical_word_load >> simp[]) >>
  Cases_on `ce.ce_flag_n_members (nsid_to_string nsid) = 256` >>
  gvs[abi_decoder_clamp_valid_def] >>
  irule LESS_EQ_LESS_TRANS >> qexists_tac `n` >> simp[MOD_LESS_EQ]
QED
