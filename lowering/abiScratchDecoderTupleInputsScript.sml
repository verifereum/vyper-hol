(* Recover tuple metadata from the actual valid source bytes. *)
Theory abiScratchDecoderTupleInputs
Ancestors
  abiScratchDecoderContract
  abiDecoderValidContract abiDecoderTupleInputs abiDecoderMembers abiDecoderMemberInfos
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiValidMembers
  compileEnv valueEncoding vyperABI contractABI venomState words list

Theorem abi_scratch_decoder_tuple_inputs:
  abi_scratch_decoder_input ce env sf (TupleT tys) (TupleTV tvs) bs v
    st src dst opc hi sb d first last b cap initial ==>
  ?vs. v = ArrayV (TupleV vs) /\
    abi_decoder_members ce env sf tys tvs
      (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) vs /\
    valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
    type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys) /\
    abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs)
      d (SUM (MAP (type_memory_bytes ce) tys)) first last b cap initial /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_scratch_decoder_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys)`
    by (simp[Once type_memory_bytes_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `valid_enc (Tuple (MAP (vyper_to_abi_type env) tys)) bs` by
    (qpat_x_assum `valid_enc _ bs` mp_tac >>
     simp_tac bool_ss [Once vyper_to_abi_type_def, vyper_to_abi_types_MAP]) >>
  drule abi_valid_tuple_view >> strip_tac >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  drule abi_decoder_tuple_values >> strip_tac >>
  gvs[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
    Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  drule_all abi_decoder_tuple_members >> strip_tac >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `valid_enc (Tuple _) bs` mp_tac >> simp_tac bool_ss [Once valid_enc_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_TUPLE_INPUTS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical tuple inputs not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderTupleInputs");

