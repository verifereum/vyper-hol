(* Actual tuple member windows establish allocation-free scalar inputs. *)
Theory abiDecodePtrPhysicalMemberRun
Ancestors
  abiDecodePtrPhysicalScalarRun abiValidMember abiValidDecodedMetadata
  abiDecoderValidMemberCons abiDecoderCoherence abiDecoderDynamic
  abiDecoderMemberSetup abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecodeRanges abiDecoderContract abiDecoderTypedContract abiCanonicalHeadSize abiValidMembers
  supportedTypes exprLowering abiEncoder compileEnv valueEncoding vyperABI contractABI
  venomState words list arithmetic

Theorem abi_decode_supported_source_shape[local]:
  supported_scalar_type ty ==>
  abi_member_head_size (vyper_to_abi_type env ty) = 32 /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem)
Proof
  Cases_on `ty` >> fs[supported_scalar_type_def, supported_word_type_def,
    supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  fs[supported_word_type_def, supported_string_type_def,
    vyper_to_abi_type_def, vyper_base_to_abi_type_def, abi_member_head_size_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  fs[supported_word_type_def, supported_string_type_def,
    vyper_to_abi_type_def, vyper_base_to_abi_type_def, abi_member_head_size_def]
QED

Theorem abi_decode_physical_member_input:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  supported_scalar_type ty /\ abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  mem_bytes_at (B + z) (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
  B + z + LENGTH bs < dimword(:256) /\
  d + q + type_memory_bytes ce ty < dimword(:256) /\
  (B + z + LENGTH bs <= d + q \/ d + q + type_memory_bytes ce ty <= B + z) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand childsrc s = SOME (n2w (z + off)) /\
  eval_operand childdst s = SOME (n2w (d + q)) /\ fresh_vars_wrt st s /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    z + LENGTH bs <= h /\ h < dimword(:256)) ==>
  abi_decode_physical_scalar_pre ce env ce.ce_struct_fields ty tv childbs v
    st childsrc childdst base_op hi B (z + off) (d + q) s
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_supported_source_shape >> disch_then (qspec_then `env` strip_assume_tac) >>
  drule abi_valid_member_window >>
  disch_then (qspecl_then [`B + z`, `s`, `MLOAD`] mp_tac) >>
  asm_simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule abi_decoder_valid_member_readable >>
  asm_simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  asm_simp_tac bool_ss [abi_decode_physical_scalar_pre_def, ADD_ASSOC] >>
  rpt conj_tac
  >- decide_tac
  >- decide_tac >>
  Cases_on `hi = Lit 0w` >> simp[] >>
  qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> simp[] >> strip_tac >>
  qexists_tac `h` >> simp[] >> decide_tac
QED
