Theory abiDecoderPrimitiveCaller
Ancestors
  abiDecoderSigned abiDecoderFixedBytes abiDecoderNumericWord abiDecoderClampedTyped
  abiDecoderWordTyped abiDecoderClamp abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract exprLowering compileEnv vyperABI vyperTyping valueEncoding venomState
  contractABI words abiDecoderClampedWord abiDecoderLayout abiDecoderPointed fragExec arithmetic
  vyperValue abiDecodeRanges vfmConstants

(* Canonical typed words satisfy every primitive decoder validation check. *)
Theorem abi_decoder_int_metadata_clamp:
  abi_decoder_metadata ce env (BaseT (IntT bits)) (BaseTV (IntT bits)) root_di av v /\
  sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (Int bits) av ==>
  abi_decoder_clamp_valid (type_to_abi_clamp (BaseT (IntT bits)))
    (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  Cases_on `av` >> simp[abi_decoder_metadata_def, has_type_def] >> rpt strip_tac >>
  gvs[abi_to_vyper_def, check_IntV_def, AllCaseEqs()] >>
  drule_all (SIMP_RULE (srw_ss()) [] abi_decoder_canonical_int_clamp) >> simp[]
QED

Theorem abi_decoder_decimal_metadata_clamp:
  abi_decoder_metadata ce env (BaseT DecimalT) (BaseTV DecimalT) root_di av v /\
  sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (Int 168) av ==>
  abi_decoder_clamp_valid (type_to_abi_clamp (BaseT DecimalT))
    (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  Cases_on `av` >> simp[abi_decoder_metadata_def, has_type_def] >> rpt strip_tac >>
  gvs[abi_to_vyper_def, check_IntV_def, AllCaseEqs()] >>
  drule_all (SIMP_RULE (srw_ss()) [] abi_decoder_canonical_decimal_clamp) >>
  simp[type_to_abi_clamp_def]
QED

Theorem abi_decoder_base_word_info:
  is_word_type (BaseT bt) ==>
  type_to_abi_dec_info sf ce (BaseT bt) =
    DecPrimWord (type_to_abi_clamp (BaseT bt))
Proof
  Cases_on `bt` >>
  FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
  simp[is_word_type_def, Once type_to_abi_dec_info_def]
QED

Theorem abi_decoder_base_word_clamp:
  is_word_type (BaseT bt) /\
  abi_decoder_metadata ce env (BaseT bt) (BaseTV bt) root_di av v /\
  sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (vyper_base_to_abi_type bt) av ==>
  abi_decoder_clamp_valid (type_to_abi_clamp (BaseT bt))
    (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  strip_tac >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  Cases_on `bt` >> gvs[is_word_type_def] >> FIRST
    [drule_all abi_decoder_canonical_uint_clamp >> simp[],
     drule_all abi_decoder_int_metadata_clamp >> simp[],
     drule_all abi_decoder_canonical_bool_clamp >> simp[type_to_abi_clamp_def],
     drule_all abi_decoder_decimal_metadata_clamp >> simp[],
     drule_all abi_decoder_canonical_address_clamp >> simp[type_to_abi_clamp_def],
     (rename1 `abi_decoder_metadata ce env (BaseT (BytesT bound)) _ _ _ _` >>
      Cases_on `bound` >> gvs[is_word_type_def] >>
      drule_all abi_decoder_canonical_fixed_bytes_clamp >> simp[])]
QED

Theorem abi_decoder_primitive_clamp:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (vyper_to_abi_type env ty) av ==>
  abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  strip_tac >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >> gvs[]
  >- (rename1 `is_word_type (BaseT bt)` >>
      `type_to_abi_dec_info sf ce (BaseT bt) =
         DecPrimWord (type_to_abi_clamp (BaseT bt))` by
        (irule abi_decoder_base_word_info >> simp[]) >> gvs[] >>
      drule_all abi_decoder_base_word_clamp >> simp[]) >>
  gvs[Once type_to_abi_dec_info_def] >>
  drule_all (SIMP_RULE (srw_ss()) [] abi_decoder_canonical_flag_clamp) >> simp[]
QED

(* Complete primitive-word decoder correctness for every coherent ABI base type. *)
Theorem abi_decoder_primitive_source:
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st last src dst opc hi sb d b cap s ==>
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (vyper_to_abi_type env ty) av /\
  type_memory_bytes ce ty = 32
Proof
  pure_rewrite_tac [abi_decoder_recursive_pre_def, abi_decoder_pre_def] >> strip_tac >>
  qpat_x_assum `DecPrimWord clamp = type_to_abi_dec_info sf ce ty`
    (assume_tac o SYM) >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
    (drule_all abi_decoder_descended_encoding_length >> asm_simp_tac bool_ss []) >>
  `mem_bytes_at sb 32 (abi_decode_source opc s) = enc (vyper_to_abi_type env ty) av`
    by metis_tac[] >>
  `sb < dimword (:256)` by
    (qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac [abi_decoder_ranges_def] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_decoder_typed_primitive_word_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post tv v st' d 32 b cap s t
Proof
  strip_tac >> drule abi_decoder_primitive_source >> strip_tac >>
  drule_all abi_decoder_primitive_clamp >> strip_tac >>
  drule_all abi_decoder_typed_clamped_word_sequence >> simp[]
QED

Theorem abi_decoder_typed_primitive_word_from_state:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st last src dst opc hi sb d b cap initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post tv v st' d 32 b cap initial) (K F)
Proof
  strip_tac >> drule abi_decoder_primitive_source >> strip_tac >>
  drule_all abi_decoder_primitive_clamp >> strip_tac >>
  drule_all abi_decoder_typed_clamped_word_from_state >> simp[]
QED

Theorem abi_decoder_typed_primitive_word_fragment:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') ==>
  frag_exec ctx st st'
    (abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
      st last src dst opc hi sb d b cap)
    (\t. ?s. abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
       st last src dst opc hi sb d b cap s /\
       abi_decoder_post tv v st' d 32 b cap s t)
    (K F)
Proof
  strip_tac >> irule frag_exec_initial_family >> rpt strip_tac >>
  drule_all abi_decoder_typed_primitive_word_from_state >> simp[]
QED

(* Primitive callers establish coherence from the existing typed precondition. *)
(* Base-type coherence follows from the source evaluator itself. This includes
   dynamic Bytes/String and unused zero-length fixed-byte array children. *)
Theorem abi_decoder_base_caller_coherent:
  evaluate_type env (BaseT bt) = SOME tv ==>
  abi_decoder_coherent ce env sf (BaseT bt) tv
Proof
  Cases_on `bt` >>
  FIRST [rename1 `BytesT bnd` >> Cases_on `bnd`, all_tac] >>
  simp_tac bool_ss [Once evaluate_type_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[] >>
  asm_simp_tac bool_ss
    [abi_decoder_coherent_base_iff, abi_decoder_scalar_valid_def,
     abi_decoder_header_def, Once evaluate_type_def,
     type_memory_bytes_def, type_memory_size_def, word_size_def, MULT_COMM,
     vyper_to_abi_type_def, vyper_base_to_abi_type_def,
     is_dynamic_def, is_abi_dynamic_def, abi_embedded_static_size_def,
     abi_static_size_def, abi_member_head_size_def, static_length_def] >>
  gvs[] >> decide_tac
QED

Theorem abi_decoder_base_word_scalar_valid:
  is_word_type (BaseT bt) /\ has_type (vyper_base_to_abi_type bt) av ==>
  abi_decoder_scalar_valid bt
Proof
  Cases_on `bt` >> Cases_on `av` >>
  FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
  simp[is_word_type_def, abi_decoder_scalar_valid_def, has_type_def,
       valid_int_bound_def, valid_bytes_bound_def]
QED

Theorem abi_decoder_base_word_header:
  is_word_type (BaseT bt) /\ evaluate_type env (BaseT bt) = SOME (BaseTV bt) /\
  type_memory_size (BaseTV bt) = type_memory_bytes ce (BaseT bt) ==>
  abi_decoder_header ce env (BaseT bt) (BaseTV bt)
Proof
  Cases_on `bt` >>
  FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
  simp[is_word_type_def, abi_decoder_header_def, type_memory_size_def,
       is_dynamic_def, is_abi_dynamic_def, abi_embedded_static_size_def,
       abi_static_size_def, abi_member_head_size_def, static_length_def]
QED

Theorem abi_decoder_base_word_coherent:
  is_word_type (BaseT bt) /\
  abi_decoder_metadata ce env (BaseT bt) (BaseTV bt) root_di av v ==>
  abi_decoder_coherent ce env sf (BaseT bt) (BaseTV bt)
Proof
  strip_tac >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  `has_type (vyper_base_to_abi_type bt) av` by fs[] >>
  drule_all abi_decoder_base_word_scalar_valid >> strip_tac >>
  drule_all abi_decoder_base_word_header >> strip_tac >>
  simp[abi_decoder_coherent_base_iff]
QED

Theorem abi_decoder_base_word_recursive_pre:
  is_word_type (BaseT bt) /\
  abi_decoder_pre ce env (BaseT bt) (BaseTV bt)
    (type_to_abi_dec_info ce.ce_struct_fields ce (BaseT bt)) av v
    st last src dst opc hi sb d b cap s ==>
  abi_decoder_recursive_pre ce env ce.ce_struct_fields (BaseT bt) (BaseTV bt)
    (DecPrimWord (type_to_abi_clamp (BaseT bt))) av v
    st last src dst opc hi sb d b cap s
Proof
  strip_tac >>
  `abi_decoder_metadata ce env (BaseT bt) (BaseTV bt)
     (type_to_abi_dec_info ce.ce_struct_fields ce (BaseT bt)) av v` by
    fs[abi_decoder_pre_def] >>
  `abi_decoder_coherent ce env ce.ce_struct_fields (BaseT bt) (BaseTV bt)` by
    (irule abi_decoder_base_word_coherent >> simp[] >>
     qexistsl_tac [`av`, `type_to_abi_dec_info ce.ce_struct_fields ce (BaseT bt)`, `v`] >>
     simp[]) >>
  `type_to_abi_dec_info ce.ce_struct_fields ce (BaseT bt) =
     DecPrimWord (type_to_abi_clamp (BaseT bt))` by
    (irule abi_decoder_base_word_info >> simp[]) >>
  simp[abi_decoder_recursive_pre_def]
QED

Theorem abi_decoder_typed_base_word_sequence:
  compile_abi_decode_to_buf dst src opc hi
    (DecPrimWord (type_to_abi_clamp (BaseT bt))) st = ((),st') /\
  is_word_type (BaseT bt) /\
  abi_decoder_pre ce env (BaseT bt) (BaseTV bt)
    (type_to_abi_dec_info ce.ce_struct_fields ce (BaseT bt)) av v
    st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post (BaseTV bt) v st' d 32 b cap s t
Proof
  strip_tac >> drule_all abi_decoder_base_word_recursive_pre >> strip_tac >>
  drule_all abi_decoder_typed_primitive_word_sequence >> simp[]
QED

Theorem abi_decoder_typed_base_word_from_state:
  compile_abi_decode_to_buf dst src opc hi
    (DecPrimWord (type_to_abi_clamp (BaseT bt))) st = ((),st') /\
  is_word_type (BaseT bt) /\
  abi_decoder_pre ce env (BaseT bt) (BaseTV bt)
    (type_to_abi_dec_info ce.ce_struct_fields ce (BaseT bt)) av v
    st last src dst opc hi sb d b cap initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post (BaseTV bt) v st' d 32 b cap initial) (K F)
Proof
  strip_tac >> drule_all abi_decoder_base_word_recursive_pre >> strip_tac >>
  drule_all abi_decoder_typed_primitive_word_from_state >> simp[]
QED
