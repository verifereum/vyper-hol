(* Canonical dynamic singleton layout and typed child restriction. *)
Theory abiDecoderSingleton
Ancestors
  abiDecoderTypedContract abiDecoderTypedCompose abiDecoderSingletonSetup
  abiDecoderReservation abiCanonicalLoad abiDecodeRanges abiDecoderContract
  valueEncoding vyperABI contractABI compileEnv exprLowering byte words
  arithmetic list rich_list

Theorem abi_singleton_dimindex[simp,local]: dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem canonical_dynamic_singleton_encoding:
  is_dynamic aty ==>
  enc (Tuple [aty]) (ListV [av]) =
    word_to_bytes (32w:bytes32) T ++ enc aty av
Proof
  simp[enc_def, head_lengths_def, enc_number_def, REV_REVERSE_LEM]
QED

Theorem canonical_dynamic_singleton_source:
  is_dynamic aty /\
  mem_bytes_at sb (LENGTH (enc (Tuple [aty]) (ListV [av]))) mem =
    enc (Tuple [aty]) (ListV [av]) ==>
  mem_bytes_at (sb + 32) (LENGTH (enc aty av)) mem = enc aty av
Proof
  strip_tac >>
  qpat_x_assum `mem_bytes_at sb _ mem = _` mp_tac >>
  asm_simp_tac bool_ss [canonical_dynamic_singleton_encoding] >> strip_tac >>
  drule abi_decoder_source_prefix >> simp[LENGTH_word_to_bytes]
QED

Theorem abi_decoder_singleton_pre_child:
  abi_decoder_pre ce env (TupleT [ty]) (TupleTV [tv]) di
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap s /\
  is_dynamic (vyper_to_abi_type env ty) /\
  eval_operand child_src s = SOME (n2w (sb + 32)) ==>
  abi_decoder_pre ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    av v st last child_src dst opc hi (sb + 32) d b cap s
Proof
  pure_rewrite_tac[abi_decoder_pre_def] >> strip_tac >>
  drule abi_decoder_singleton_metadata_child >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [type_memory_bytes_def, Excl "enc_def"]) >>
  asm_rewrite_tac[vyper_to_abi_type_def] >> conj_tac
  >- (irule abi_decoder_child_ranges >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`LENGTH (enc (Tuple [vyper_to_abi_type env ty]) (ListV [av]))`, `src`] >>
      simp[canonical_dynamic_singleton_encoding, LENGTH_word_to_bytes,
           type_memory_bytes_def, Excl "enc_def"]) >>
  irule canonical_dynamic_singleton_source >>
  qpat_x_assum `mem_bytes_at sb _ _ = _` mp_tac >>
  simp_tac bool_ss [vyper_to_abi_type_def] >> simp[Excl "enc_def"]
QED

Theorem abi_decoder_singleton_setup_pre:
  abi_decoder_pre ce env (TupleT [ty]) (TupleTV [tv]) di
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap s /\
  is_dynamic (vyper_to_abi_type env ty) ==>
  abi_decode_singleton_setup_pre st src dst opc hi sb d s
Proof
  strip_tac >>
  `has_types [vyper_to_abi_type env ty] [av]` by
    fs[abi_decoder_pre_def, abi_decoder_metadata_def, has_type_def, Excl "enc_def"] >>
  qpat_x_assum `abi_decoder_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decoder_pre_def, abi_decoder_ranges_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [vyper_to_abi_type_def]) >>
  mp_tac (Q.INST [`pre` |-> `[]`, `pvs` |-> `[]`, `post` |-> `[]`, `rest` |-> `[]`,
    `aty` |-> `vyper_to_abi_type env ty`, `v` |-> `(av:abi_value)`]
    (Q.INST [`ty` |-> `aty`] canonical_member_offset_load)) >>
  impl_tac >- simp[Excl "enc_def"] >> simp[head_lengths_def] >> strip_tac >>
  `32 <= LENGTH (enc (Tuple [vyper_to_abi_type env ty]) (ListV [av]))` by
    simp[canonical_dynamic_singleton_encoding, LENGTH_word_to_bytes, Excl "enc_def"] >>
  gvs[abi_decode_singleton_setup_pre_def, Excl "enc_def"] >>
  rpt strip_tac >> TRY decide_tac >> disj2_tac >>
  rename1 `eval_operand hi s = SOME (n2w hb)` >>
  qexists_tac `hb` >> simp[] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_SINGLETON_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI dynamic singleton boundary not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderSingleton");
