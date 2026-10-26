(* Primitive decoder descriptors and their typed canonical word layout. *)
Theory abiDecoderWordTyped
Ancestors
  abiDecoderWordCopy abiDecoderCoherence abiDecoderLayout abiDecoderTypedContract
  abiStaticPrimitiveProps exprLowering compileEnv valueEncoding vyperABI vyperTyping
  abiEncoder contractABI abiDecoderContract abiDecodeRanges abiDecoderBytesTyped fragExec

Theorem abi_decoder_base_primitive_shape[local]:
  abi_decoder_scalar_valid bt /\
  type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp ==>
  is_word_type (BaseT bt) /\ type_memory_bytes ce (BaseT bt) = 32 /\
  ~is_abi_dynamic ce.ce_struct_fields (BaseT bt)
Proof
  Cases_on `bt` >>
  FIRST [(rename1 `BytesT bd` >> Cases_on `bd`), all_tac] >>
  simp[abi_decoder_scalar_valid_def, Once type_to_abi_dec_info_def,
       is_word_type_def, type_memory_bytes_def,
       is_abi_dynamic_def]
QED

Theorem abi_decoder_primitive_cases:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  !clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  ((?bt. ty = BaseT bt /\ tv = BaseTV bt /\ is_word_type ty) \/
   (?nsid n. ty = FlagT nsid /\ tv = FlagTV n)) /\
  type_memory_bytes ce ty = 32 /\ ~is_abi_dynamic ce.ce_struct_fields ty
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- (rpt strip_tac >> drule_all abi_decoder_base_primitive_shape >> simp[])
  >- simp[type_memory_bytes_def, is_abi_dynamic_def]
  >- (rpt gen_tac >> strip_tac >> Cases_on `bound` >>
      simp[Once type_to_abi_dec_info_def])
  >- (rpt gen_tac >> strip_tac >> simp[Once type_to_abi_dec_info_def]) >>
  rpt gen_tac >> strip_tac >> simp[Once type_to_abi_dec_info_def]
QED

Theorem abi_decoder_primitive_canonical_layout:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  mem_bytes_at d 32 mem = enc (vyper_to_abi_type env ty) av ==>
  val_in_memory tv v d mem
Proof
  strip_tac >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  drule_all abi_decoder_typed_conversion >> strip_tac >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  simp[] >> strip_tac >> gvs[abi_decoder_metadata_def]
  >- (irule abi_static_primitive_layout >> asm_simp_tac bool_ss [] >>
      qexists_tac `av` >>
      gvs[Once vyper_to_abi_def, vyper_to_abi_type_def]) >>
  irule abi_compatible_flag_value_layout >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`av`, `nsid`, `env`] >> simp[]
QED

Theorem abi_decoder_typed_unclamped_word_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord NoClamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord NoClamp) av v
    st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post tv v st' d 32 b cap s t
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decoder_recursive_pre_def, abi_decoder_pre_def] >> strip_tac >>
  qpat_x_assum `DecPrimWord NoClamp = type_to_abi_dec_info sf ce ty`
    (assume_tac o SYM) >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `NoClamp` mp_tac) >>
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
  drule_all abi_decode_word_copied_window >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  `mem_bytes_at d 32 t.vs_memory = enc (vyper_to_abi_type env ty) av` by
    asm_rewrite_tac[] >>
  drule_all abi_decoder_primitive_canonical_layout >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_post_def] >>
  irule abi_decoder_frame_from_output >> simp[]
QED

Theorem abi_decoder_typed_unclamped_word_fragment:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord NoClamp) st = ((),st') ==>
  frag_exec ctx st st'
    (abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord NoClamp) av v
      st last src dst opc hi sb d b cap)
    (\t. ?s. abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord NoClamp) av v
       st last src dst opc hi sb d b cap s /\
       abi_decoder_post tv v st' d 32 b cap s t)
    (K F)
Proof
  reverse (Cases_on `abi_decode_source_opcode opc`)
  >- simp[frag_exec_def, abi_decoder_recursive_pre_def, abi_decoder_pre_def,
          abi_decoder_ranges_def] >>
  strip_tac >> drule_all abi_decoder_word_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >> rpt strip_tac >>
  drule_all abi_decoder_typed_unclamped_word_sequence >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_post_inst_idx] >> qexists_tac `s` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_WORD_TYPED_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder primitive layout not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderWordTyped");
