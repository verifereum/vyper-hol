(* Fixed arrays use the actual repeated-type member view of source-valid bytes. *)
Theory abiDecoderValidFixedInputs
Ancestors
  abiDecoderValidContract abiDecoderFixedMembers abiDecoderMembers abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract abiValidMembers abiValidAggregateHeads
  abiCanonicalHeadSize abiCanonicalArrays compileEnv valueEncoding vyperABI vyperValue
  contractABI venomState words list rich_list

Theorem abi_decoder_valid_fixed_view:
  valid_enc (Array (SOME n) at) bs ==>
  valid_enc_tuple (REPLICATE n at) bs bs /\
  dec (Array (SOME n) at) bs = ListV (abi_decode_members (REPLICATE n at) bs bs)
Proof
  strip_tac >>
  `valid_enc_tuple (REPLICATE n at) bs bs` by
    fs[Once valid_enc_def, valid_enc_tuple_REPLICATE, Excl "dec_def"] >>
  asm_simp_tac (srw_ss()) [Once dec_def, LET_THM, abi_decode_array_members, abi_decode_members_value,
    Excl "dec_def", Excl "enc_def", Excl "valid_enc_def"]
QED

Theorem abi_decoder_valid_fixed_array_inputs:
  abi_decoder_valid_pre ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
    bs v st src dst opc hi sb d b cap initial ==>
  ?vs. v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)) /\ LENGTH vs = n /\
    abi_decoder_members ce env sf (REPLICATE n ty) (REPLICATE n tv)
      (abi_decode_members (MAP (vyper_to_abi_type env) (REPLICATE n ty)) bs bs) vs /\
    valid_enc_tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty)) bs bs /\
    type_memory_bytes ce (ArrayT ty (Fixed n)) = SUM (MAP (type_memory_bytes ce) (REPLICATE n ty)) /\
    abi_decoder_ranges opc hi src dst sb (LENGTH bs)
      d (SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))) b cap initial /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_decoder_valid_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_fixed_array_values >> strip_tac >>
  `type_memory_bytes ce (ArrayT ty (Fixed n)) = SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))`
    by simp[Once type_memory_bytes_def, map_replicate, SUM_REPLICATE] >>
  `valid_enc (Array (SOME n) (vyper_to_abi_type env ty)) bs` by
    (qpat_x_assum `valid_enc _ bs` mp_tac >> simp_tac bool_ss [Once vyper_to_abi_type_def]) >>
  drule abi_decoder_valid_fixed_view >> strip_tac >>
  gvs[Once vyper_to_abi_type_def, map_replicate,
    Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  qexists_tac `vs` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_VALID_FIXED_INPUTS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid fixed-array inputs not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderValidFixedInputs");
