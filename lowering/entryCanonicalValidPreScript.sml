(* Canonical member validity at the already selected registration witness. *)
Theory entryCanonicalValidPre
Ancestors
  entryCanonicalReadyPre entryCanonicalMemberDecode entryNormalizedBackwardExists
  entryZeroReservePre abiValidDecodedMetadata abiDecoderCoherence
  abiDecoderValidContract abiDecoderTypedContract abiDecodeRanges
  vyperABI compileEnv venomState words list arithmetic

Theorem entry_canonical_valid_pre:
  abi_decoder_coherent ce env sf ty tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\ at = vyper_to_abi_type env ty /\
  has_types (pre ++ at::post) (pvs ++ av::rest) /\ LENGTH pre = LENGTH pvs /\
  bs = enc (Tuple (pre ++ at::post)) (ListV (pvs ++ av::rest)) /\
  mem_bytes_at 4 (LENGTH bs) (abi_decode_source CALLDATALOAD ready) = bs /\
  4 + LENGTH bs < dimword (:256) /\
  ao = SUM (MAP abi_member_head_size pre) /\
  k = abi_decode_member_offset at bs ao /\
  bytes = abi_decode_member_bytes at bs (DROP ao bs) /\
  eval_operand src ready = SOME (n2w (4+k)) /\
  eval_operand dst ready = SOME (n2w p) /\
  p + type_memory_bytes ce ty < dimword (:256) /\
  abi_decoder_operand_live first.cs_next_var src /\
  abi_decoder_operand_live first.cs_next_var dst ==>
  ?nv. abi_to_vyper env ty av = SOME nv /\
    abi_decoder_valid_pre ce env sf ty tv bytes nv first src dst CALLDATALOAD
      (Lit 0w) (4+k) p (p + type_memory_bytes ce ty) 0 ready
Proof
  strip_tac >>
  `evaluate_type env ty = SOME tv` by
    (drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  drule_all entry_typed_forward_backward_exists >> strip_tac >>
  qexists_tac `nv` >> conj_tac >- simp[] >>
  `dec at bytes = av` by
    (drule_all entry_canonical_member_decode >> simp[]) >>
  `vyper_decode_valid_enc at bytes /\
   (is_dynamic at \/ static_length at <= LENGTH bytes) /\
   k + LENGTH bytes <= LENGTH bs /\ 4+k < dimword (:256) /\
   mem_bytes_at (4+k) (LENGTH bytes) (abi_decode_source CALLDATALOAD ready) = bytes` by
    (drule_all entry_canonical_member_window >> simp[LET_THM]) >>
  `abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
     (dec (vyper_to_abi_type env ty) bytes) nv` by
    (irule abi_valid_decoded_metadata >> gvs[] >> metis_tac[]) >>
  `4+k + LENGTH bytes < dimword (:256)` by decide_tac >>
  irule entry_zero_reserve_valid_pre >> gvs[]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag entry_canonical_valid_pre)
  in if null axioms andalso null (Thm.hyp entry_canonical_valid_pre) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "canonical valid pre inherited admission"
  end;
