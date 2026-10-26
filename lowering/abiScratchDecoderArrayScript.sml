(* Both emitted dynamic-array branches satisfy the physical decoder contract. *)
Theory abiScratchDecoderArray
Ancestors
  abiScratchDecoderContract abiScratchDecoderArrayExecute abiScratchDecoderArrayBulk
  abiScratchDecoderLeaves abiScratchDecoderTuple abiDecoderValidTuple
  abiDecoderCorrectPrimitiveArray abiDecoderRecursiveArray abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract abiDecoderReentry abiDecoderLoop abiDecodeRanges
  abiEncoder exprLowering fragExec compileEnv valueEncoding vyperABI vyperValue contractABI
  venomState words list

Theorem abi_scratch_decoder_array_loop:
  abi_scratch_decoder ce env sf ty tv /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  (is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
  abi_scratch_decoder ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_scratch_decoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) bs v start src dst opc hi sb d first last b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_input_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [Once type_to_abi_dec_info_def]) >>
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_ranges_def] >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`,
    `ei` |-> `type_to_abi_dec_info (sf:string |-> (string # vyperAST$type # num) list) ce ty`,
    `asz` |-> `abi_embedded_static_size ce.ce_struct_fields ty`,
    `msz` |-> `type_memory_bytes ce ty`, `dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`]
    abi_decoder_recursive_array_adds_blocks) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  `!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`, `hi_op` |-> `hi:operand`]
    abi_scratch_decoder_array_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss [])
QED

Theorem abi_scratch_decoder_array_copy:
  ~is_abi_dynamic ce.ce_struct_fields ty /\ ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) ==>
  abi_scratch_decoder ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_scratch_decoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) bs v start src dst opc hi sb d first last b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_input_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  (qpat_assum `~is_abi_dynamic ce.ce_struct_fields ty` (fn static =>
    qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
      (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def, static])) >>
  mp_tac (Q.INST [`st` |-> `start`] abi_scratch_decoder_array_bulk) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss [])
QED

Theorem abi_scratch_decoder_array:
  abi_scratch_decoder ce env sf ty tv /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  abi_scratch_decoder ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- (irule abi_scratch_decoder_array_loop >> asm_simp_tac bool_ss []) >>
  irule abi_scratch_decoder_array_copy >> fs[]
QED

Theorem abi_scratch_decoder_base_array:
  !bt. abi_scratch_decoder ce env sf
    (ArrayT (BaseT bt) (Dynamic maxn)) (ArrayTV (BaseTV bt) (Dynamic maxn))
Proof
  gen_tac >> irule abi_scratch_decoder_array >>
  metis_tac[abi_scratch_decoder_base, abi_decoder_valid_base_member_nonempty]
QED
