(* Complete primitive-word decoder correctness for every coherent ABI base type. *)
Theory abiDecoderPrimitive
Ancestors
  abiDecoderPrimitiveClamp abiDecoderClampedTyped abiDecoderClampedWord
  abiDecoderCoherence abiDecoderTypedContract abiDecoderWordTyped abiDecoderLayout
  abiDecoderContract abiDecoderPointed fragExec exprLowering compileEnv valueEncoding
  vyperABI contractABI words arithmetic

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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRIMITIVE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive decoder not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPrimitive");
