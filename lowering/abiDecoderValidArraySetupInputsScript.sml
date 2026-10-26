(* Source validity justifies the actual dynamic-element offset and bounds guards. *)
Theory abiDecoderValidArraySetupInputs
Ancestors
  abiDecoderValidArrayWindows abiDecoderDynamic abiDecoderCoherence abiDecoderTypedContract
  abiDecoderOffset
  abiDecoderContract abiDecodeRanges abiValidMemberWindows abiValidMembers
  abiEncoder compileEnv valueEncoding vyperABI contractABI venomState words list arithmetic

Theorem abi_decoder_valid_array_setup_inputs:
  let at = vyper_to_abi_type env ty;
      asz = abi_embedded_static_size ce.ce_struct_fields ty;
      rel = abi_decode_member_offset at (DROP 32 bs) (j * abi_member_head_size at) in
  abi_decoder_coherent ce env sf ty tv /\ is_dynamic at /\
  (!elem. at <> Array (SOME 0) elem) /\
  valid_enc (Array NONE at) bs /\ j < abi_head_word bs /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs ==>
  abi_decoder_dynamic (type_to_abi_dec_info sf ce ty) /\
  dec_info_needs_offset (type_to_abi_dec_info sf ce ty) /\ abi_decode_source_opcode opc /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decode_load opc (n2w (sb + 32 + j * asz):bytes32) initial = n2w rel /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + 32 + rel + asz <= hb /\ hb < dimword (:256))
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_coherent_header >> strip_tac >>
  qpat_assum `abi_decoder_header ce env ty tv`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_header_def]) >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  drule_all abi_decoder_nonempty_type_offset >> strip_tac >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  mp_tac (SIMP_RULE arith_ss [LET_THM]
    (Q.INST [`at` |-> `vyper_to_abi_type env ty`, `s` |-> `initial:venom_state`]
      abi_valid_array_child_window)) >> impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `is_abi_dynamic ce.ce_struct_fields ty /\
    abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` by metis_tac[] >>
  RULE_ASSUM_TAC (SIMP_RULE arith_ss []) >>
  asm_simp_tac arith_ss [] >> Cases_on `hi = Lit 0w` >- simp[] >>
  qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `eval_operand hi initial = SOME (n2w hb)` >>
  qexists_tac `hb` >> asm_simp_tac bool_ss [] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_VALID_ARRAY_SETUP_INPUTS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid array setup inputs not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderValidArraySetupInputs");
