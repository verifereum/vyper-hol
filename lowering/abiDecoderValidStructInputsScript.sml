(* Positional struct metadata and ranges over actual noncanonical source bytes. *)
Theory abiDecoderValidStructInputs
Ancestors
  abiDecoderValidContract abiDecoderStructInputs abiDecoderStructMembers abiDecoderMembers
  abiDecoderMemberInfos abiDecoderCoherence abiDecoderTypedContract abiDecoderContract
  abiValidMembers compileEnv valueEncoding vyperABI contractABI venomState words list pair

Theorem abi_decoder_valid_struct_inputs:
  FLOOKUP env nsid = SOME (StructArgs args) /\ LENGTH tvs = LENGTH args /\
  abi_decoder_valid_pre ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
    bs v st src dst opc hi sb d b cap initial ==>
  ?cfields fields.
    FLOOKUP sf (nsid_to_string nsid) = SOME cfields /\
    MAP (FST o SND) cfields = MAP SND args /\
    v = StructV fields /\
    value_has_type (StructTV (ZIP (MAP FST args,tvs))) (StructV fields) /\
    abi_decoder_members ce (env \\ nsid) (sf \\ nsid_to_string nsid)
      (MAP SND args) tvs
      (abi_decode_members (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) bs bs)
      (MAP SND fields) /\
    valid_enc_tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) bs bs /\
    type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args)) /\
    abi_decoder_ranges opc hi src dst sb
      (LENGTH bs)
      d (SUM (MAP (type_memory_bytes ce) (MAP SND args))) b cap initial /\
    mem_bytes_at sb
      (LENGTH bs)
      (abi_decode_source opc initial) =
        bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_decoder_valid_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  drule abi_decoder_struct_values >> strip_tac >> gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  drule_all abi_decoder_struct_members_at >> strip_tac >>
  drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> simp[]) >>
  `type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args))` by
    fs[Once type_memory_size_def, Excl "enc_def"] >>
  drule_all abi_decoder_struct_field_types >> strip_tac >>
  `valid_enc (Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))) bs` by
    (qpat_x_assum `valid_enc _ bs` mp_tac >>
     asm_simp_tac (srw_ss()) [Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
       Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"]) >>
  drule abi_valid_tuple_view >> strip_tac >>
  qexists_tac `cfields` >>
  gvs[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
    Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  qpat_x_assum `valid_enc (Tuple _) bs` mp_tac >> simp_tac bool_ss [Once valid_enc_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_VALID_STRUCT_INPUTS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid struct inputs not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderValidStructInputs");
