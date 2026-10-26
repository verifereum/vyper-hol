(* Canonical singleton Bytes input reaches the actual typed child decoder. *)
Theory abiDecoderWrappedBytesTyped
Ancestors
  abiDecoderWrappedBytes abiDecoderSingletonSetup abiDecoderTypedCompose
  abiDecoderTypedContract abiDecoderReservation abiDecoderBytesTyped
  abiCanonicalLoad abiDecodeRanges abiDecoderContract
  exprLowering compileEnv emitHelperProps valueEncoding vyperABI contractABI byte
  venomExecSemantics venomState words arithmetic list

Theorem abi_wrapped_bytes_dimindex[simp,local]: dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem abi_decoder_wrapped_bytes_setup_pre:
  abi_decoder_pre ce env (TupleT [BaseT (BytesT (Dynamic n))])
    (TupleTV [BaseTV (BytesT (Dynamic n))]) di
    (ListV [contractABI$BytesV bs]) (ArrayV (TupleV [vyperValue$BytesV bs]))
    st last src dst MLOAD hi sb d b cap s ==>
  abi_decode_singleton_setup_pre st src dst MLOAD hi sb d s
Proof
  strip_tac >>
  `has_types [Bytes NONE] [contractABI$BytesV bs]` by
    fs[abi_decoder_pre_def, abi_decoder_metadata_def, has_type_def, Excl "enc_def"] >>
  qpat_x_assum `abi_decoder_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decoder_pre_def, abi_decoder_ranges_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [vyper_to_abi_type_def, vyper_base_to_abi_type_def]) >>
  mp_tac (Q.INST [`pre` |-> `[]`, `pvs` |-> `[]`, `post` |-> `[]`, `rest` |-> `[]`,
    `ty` |-> `Bytes NONE`, `v` |-> `contractABI$BytesV bs`, `opc` |-> `MLOAD`]
    canonical_member_offset_load) >>
  impl_tac >- simp[Excl "enc_def"] >> simp[head_lengths_def] >> strip_tac >>
  `32 <= LENGTH (enc (Tuple [Bytes NONE]) (ListV [contractABI$BytesV bs]))` by
    simp[abi_decoder_singleton_bytes_encoding, LENGTH_word_to_bytes, Excl "enc_def"] >>
  gvs[abi_decode_singleton_setup_pre_def, abi_decode_source_opcode_def, Excl "enc_def"] >>
  rpt strip_tac >> TRY decide_tac >>
  disj2_tac >> rename1 `eval_operand hi s = SOME (n2w hb)` >>
  qexists_tac `hb` >> simp[] >> decide_tac
QED

Theorem abi_decoder_wrapped_bytes_setup:
  abi_decode_singleton_setup dst src MLOAD hi st = ((child_src,child_dst),st') /\
  abi_decoder_pre ce env (TupleT [BaseT (BytesT (Dynamic n))])
    (TupleTV [BaseTV (BytesT (Dynamic n))]) di
    (ListV [contractABI$BytesV bs]) (ArrayV (TupleV [vyperValue$BytesV bs]))
    st last src dst MLOAD hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_pre ce env (BaseT (BytesT (Dynamic n))) (BaseTV (BytesT (Dynamic n)))
      (DecBytestring n) (contractABI$BytesV bs) (vyperValue$BytesV bs)
      st' last child_src child_dst MLOAD hi (sb + 32) d b cap t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  strip_tac >> drule abi_decoder_wrapped_bytes_setup_pre >> strip_tac >>
  drule_all abi_decode_singleton_setup_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_singleton_setup_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  drule_all abi_decoder_pre_pure_transport >> strip_tac >>
  drule_all abi_decoder_wrapped_bytes_pre_child >> strip_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [type_to_abi_dec_info_def]) >>
  `abi_decoder_pre ce env (BaseT (BytesT (Dynamic n))) (BaseTV (BytesT (Dynamic n)))
     (DecBytestring n) (contractABI$BytesV bs) (vyperValue$BytesV bs)
     st' last child_src child_dst MLOAD hi (sb + 32) d b cap t` by
    (drule_all abi_decoder_pre_destination_value >> simp[]) >>
  qexists_tac `t` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_WRAPPED_BYTES_TYPED_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI wrapped Bytes typed decoder not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderWrappedBytesTyped");
