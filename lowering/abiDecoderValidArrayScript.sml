(* Dynamic arrays close the actual-source decoder API for both emitted branches. *)
Theory abiDecoderValidArray
Ancestors
  abiDecoderValidContract abiDecoderValidPrefix abiDecoderValidArrayExecute
  abiDecoderValidLeaves abiDecoderValidTuple
  abiDecoderValidArrayInitInputs abiDecoderCorrectPrimitiveArray abiDecoderRecursiveArrayCode
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecodeRanges
  abiDecoderEffect abiDecoderReentry abiDecoderLoop abiEncoder exprLowering compileEnv valueEncoding
  vyperABI vyperValue contractABI venomState words list

Theorem abi_decoder_valid_correct_dynamic_array:
  abi_decoder_valid_correct ce env sf ty tv /\ is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  abi_decoder_valid_correct ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_decoder_valid_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_valid_pre ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) bs v start src dst opc hi sb d b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `is_abi_dynamic ce.ce_struct_fields ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once type_to_abi_dec_info_def] >> strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def] >>
  qpat_assum `is_abi_dynamic ce.ce_struct_fields ty`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`dyn` |-> `T`] abi_decoder_recursive_array_adds_blocks)) >> disch_then assume_tac >>
  `!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`, `hi_op` |-> `hi:operand`]
    abi_decoder_valid_array_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_correct_array:
  abi_decoder_valid_correct ce env sf ty tv /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  abi_decoder_valid_correct ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (irule abi_decoder_valid_correct_dynamic_array >> asm_simp_tac bool_ss []) >>
  irule abi_decoder_valid_correct_static_array >>
  qexists_tac `vyper_to_abi_type env ty` >> asm_simp_tac bool_ss [Once vyper_to_abi_type_def]
QED

Theorem abi_decoder_valid_correct_base_array:
  !bt. abi_decoder_valid_correct ce env sf
    (ArrayT (BaseT bt) (Dynamic maxn)) (ArrayTV (BaseTV bt) (Dynamic maxn))
Proof
  gen_tac >> irule abi_decoder_valid_correct_array >>
  metis_tac[abi_decoder_valid_correct_base, abi_decoder_valid_base_member_nonempty]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_VALID_ARRAY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI actual-source array decoder not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderValidArray");
