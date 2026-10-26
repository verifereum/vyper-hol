(* String decoding reuses the bytestring code and its exact memory layout. *)
Theory abiDecoderString
Ancestors
  abiDecoderBytesTyped abiDecoderTypedContract abiDecoderContract abiDecoderBytes
  abiCanonicalBytes abiDecoderPointed compileEnv exprLoweringProps exprLowering
  vyperABI vyperTyping vyperValue contractABI valueEncoding
  fragExec venomExecSemantics byte words list string combin

Theorem abi_decoder_string_pre_bytes:
  abi_decoder_pre ce env (BaseT (StringT n)) (BaseTV (StringT n))
    (DecBytestring n) (contractABI$BytesV bs)
    (StringV (MAP (CHR o w2n) bs)) st last src dst opc hi sb d b cap s ==>
  abi_decoder_pre ce env (BaseT (BytesT (Dynamic n))) (BaseTV (BytesT (Dynamic n)))
    (DecBytestring n) (contractABI$BytesV bs) (vyperValue$BytesV bs)
    st last src dst opc hi sb d b cap s
Proof
  simp[abi_decoder_pre_def, abi_decoder_metadata_def, abi_decoder_ranges_def,
       evaluate_type_def, type_slot_size_def, value_has_type_def,
       type_memory_size_def, type_memory_bytes_def, type_to_abi_dec_info_def,
       vyper_to_abi_type_def, vyper_base_to_abi_type_def,
       enc_def, has_type_def, abi_to_vyper_def, compatible_bound_def]
QED

Theorem abi_string_dimindex8[simp,local]: dimindex (:8) = 8
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem abi_string_byte_bound[local]: !w:word8. w2n w < 256
Proof
  gen_tac >> mp_tac (ISPEC ``w:word8`` w2n_lt) >> simp[dimword_def]
QED

Theorem abi_decoder_string_bytes_roundtrip:
  MAP (n2w o ORD) (MAP (CHR o w2n) (bs : word8 list)) = bs
Proof
  simp[MAP_MAP_o, o_DEF, ORD_CHR_RWT, abi_string_byte_bound, n2w_w2n]
QED

Theorem abi_decoder_string_memory:
  val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) bs)) d mem <=>
  val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) d mem
Proof
  simp[val_in_memory_def, abi_decoder_string_bytes_roundtrip]
QED

Theorem abi_decoder_string_post_bytes:
  abi_decoder_post (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs)
    st' d outsz b cap initial =
  abi_decoder_post (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) bs))
    st' d outsz b cap initial
Proof
  simp[FUN_EQ_THM, abi_decoder_post_def, abi_decoder_string_memory]
QED

Theorem abi_decoder_typed_string_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_pre ce env (BaseT (StringT n)) (BaseTV (StringT n))
    (DecBytestring n) (contractABI$BytesV bs) (StringV (MAP (CHR o w2n) bs))
    st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) bs))
      st' d (type_memory_bytes ce (BaseT (StringT n))) b cap s t
Proof
  strip_tac >> drule_all abi_decoder_string_pre_bytes >> strip_tac >>
  drule_all abi_decoder_typed_bytes_sequence >> strip_tac >>
  qexists_tac `t` >>
  fs[abi_decoder_string_post_bytes, abi_decode_bytes_copy_size_def,
     type_memory_bytes_def]
QED

Theorem abi_decoder_typed_string_from_state:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_pre ce env (BaseT (StringT n)) (BaseTV (StringT n))
    (DecBytestring n) (contractABI$BytesV bs) (StringV (MAP (CHR o w2n) bs))
    st last src dst opc hi sb d b cap initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) bs))
       st' d (type_memory_bytes ce (BaseT (StringT n))) b cap initial) (K F)
Proof
  strip_tac >> drule_all abi_decoder_string_pre_bytes >> strip_tac >>
  drule_all abi_decoder_typed_bytes_from_state >>
  simp[abi_decoder_string_post_bytes, abi_decode_bytes_copy_size_def,
       type_memory_bytes_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_STRING_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI String decoder not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderString");
