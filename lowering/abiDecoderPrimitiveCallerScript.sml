(* Primitive callers establish coherence from the existing typed precondition. *)
Theory abiDecoderPrimitiveCaller
Ancestors
  abiDecoderPrimitive abiDecoderPrimitiveClamp abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract exprLowering compileEnv valueEncoding
  vyperABI vyperValue contractABI abiDecodeRanges fragExec venomState words
  vfmConstants arithmetic

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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRIMITIVE_CALLER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive caller not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPrimitiveCaller");
