(* Typed primitive execution. Canonical numeric inputs discharge clamp validity;
   the general helper exposes the pure word condition for other primitives. *)
Theory abiDecoderClampedTyped
Ancestors
  abiDecoderClampedWord abiDecoderNumericWord abiDecoderClamp abiDecoderWordTyped
  abiDecoderCoherence abiDecoderTypedContract abiDecoderLayout abiDecoderContract
  abiDecoderBytesTyped abiDecoderPointed abiCanonicalLoad abiDecodeRanges
  exprLowering compileEnv valueEncoding vyperABI contractABI abiEncoder
  fragExec venomState venomInst words arithmetic list rich_list

Theorem abi_decoder_typed_clamped_word_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st last src dst opc hi sb d b cap s /\
  abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w sb : bytes32) s) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post tv v st' d 32 b cap s t
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decoder_recursive_pre_def, abi_decoder_pre_def] >> strip_tac >>
  qpat_x_assum `DecPrimWord clamp = type_to_abi_dec_info sf ce ty`
    (assume_tac o SYM) >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
    (drule_all abi_decoder_descended_encoding_length >> asm_simp_tac bool_ss []) >>
  qpat_assum `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` (fn len_th =>
    qpat_assum `type_memory_bytes ce ty = 32` (fn size_th =>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [len_th, size_th]))) >>
  `sb < dimword (:256) /\ d < dimword (:256)` by
    (conj_tac >> irule (DECIDE ``!a b:num. a + 32 < b ==> a < b``) >>
     first_assum ACCEPT_TAC) >>
  drule_all abi_decoder_clamped_word_copied_window >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  `mem_bytes_at d 32 t.vs_memory = enc (vyper_to_abi_type env ty) av` by
    asm_rewrite_tac[] >>
  drule_all abi_decoder_primitive_canonical_layout >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_post_def] >>
  irule abi_decoder_frame_from_output >> simp[]
QED

Theorem abi_decoder_numeric_primitive_clamp:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (vyper_to_abi_type env ty) av /\
  ((?bits. ty = BaseT (UintT bits)) \/ ty = BaseT AddressT \/
   ty = BaseT BoolT \/ (?nsid. ty = FlagT nsid)) ==>
  abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  strip_tac >> gvs[]
  >- (gvs[Once type_to_abi_dec_info_def] >>
      qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
        (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
      fs[] >>
      drule_all abi_decoder_canonical_uint_clamp >> simp[])
  >- (gvs[Once type_to_abi_dec_info_def, type_to_abi_clamp_def] >>
      qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
        (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
      fs[] >>
      drule_all abi_decoder_canonical_address_clamp >> simp[])
  >- (gvs[Once type_to_abi_dec_info_def, type_to_abi_clamp_def] >>
      qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
        (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
      fs[] >>
      drule_all abi_decoder_canonical_bool_clamp >> simp[]) >>
  gvs[Once type_to_abi_dec_info_def] >>
  drule_all (SIMP_RULE (srw_ss()) [] abi_decoder_canonical_flag_clamp) >> simp[]
QED

Theorem abi_decoder_typed_numeric_word_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st last src dst opc hi sb d b cap s /\
  ((?bits. ty = BaseT (UintT bits)) \/ ty = BaseT AddressT \/
   ty = BaseT BoolT \/ (?nsid. ty = FlagT nsid)) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post tv v st' d 32 b cap s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [abi_decoder_recursive_pre_def, abi_decoder_pre_def]) >>
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
     pure_rewrite_tac[abi_decoder_ranges_def] >> rpt strip_tac >>
     gvs[] >> decide_tac) >>
  drule_all abi_decoder_numeric_primitive_clamp >> strip_tac >>
  drule_all abi_decoder_typed_clamped_word_sequence >> simp[]
QED

Theorem abi_decoder_typed_numeric_word_from_state:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st last src dst opc hi sb d b cap initial /\
  ((?bits. ty = BaseT (UintT bits)) \/ ty = BaseT AddressT \/
   ty = BaseT BoolT \/ (?nsid. ty = FlagT nsid)) ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post tv v st' d 32 b cap initial) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_typed_numeric_word_sequence >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_post_inst_idx]
QED

Theorem abi_decoder_typed_clamped_word_from_state:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st last src dst opc hi sb d b cap initial /\
  abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w sb : bytes32) initial) ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post tv v st' d 32 b cap initial) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_typed_clamped_word_sequence >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_post_inst_idx]
QED
