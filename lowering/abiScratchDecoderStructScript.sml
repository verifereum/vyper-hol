Theory abiScratchDecoderStruct
Ancestors
  valueEncodingTyping
  abiScratchDecoderContract abiDecoderValidContract abiDecoderStruct abiDecoderMembers
  abiDecoderMemberInfos abiDecoderCoherence abiDecoderTypedContract abiDecoderContract
  abiValidMembers compileEnv valueEncoding vyperABI contractABI venomState words list pair
  abiScratchDecoderLeaves abiScratchDecoderComplex abiDecoderEffect abiDecoderReentry
  abiStaticListProps fragExec valueEncodingProps vyperTyping

(* ===== Inputs ===== *)

(* Positional struct metadata and ranges over actual noncanonical source bytes. *)

Theorem abi_scratch_decoder_struct_inputs:
  FLOOKUP env nsid = SOME (StructArgs args) /\ LENGTH tvs = LENGTH args /\
  abi_scratch_decoder_input ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
    bs v st src dst opc hi sb d first last b cap initial ==>
  ?cfields fields.
    FLOOKUP sf (nsid_to_string nsid) = SOME cfields /\
    MAP (FST o SND) cfields = MAP SND args /\
    v = StructV fields /\
    value_has_type (StructTV (ZIP (MAP FST args,tvs))) (StructV fields) /\
    abi_decoder_members ce (env \\ nsid) (sf \\ nsid_to_string nsid)
      (MAP SND args) tvs
      (abi_decode_members (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) bs bs)
      (MAP SND fields) /\
    vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) bs bs /\
    type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args)) /\
    abi_scratch_decoder_ranges opc hi src dst sb
      (LENGTH bs)
      d (SUM (MAP (type_memory_bytes ce) (MAP SND args))) first last b cap initial /\
    mem_bytes_at sb
      (LENGTH bs)
      (abi_decode_source opc initial) =
        bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_scratch_decoder_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  drule abi_decoder_struct_values >> strip_tac >> gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  drule_all abi_decoder_struct_members_at >> strip_tac >>
  drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> simp[]) >>
  `type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args))` by
    fs[Once type_memory_size_def, Excl "enc_def"] >>
  drule_all abi_decoder_struct_field_types >> strip_tac >>
  `vyper_decode_valid_enc (Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))) bs` by
    (qpat_x_assum `vyper_decode_valid_enc _ bs` mp_tac >>
     asm_simp_tac (srw_ss()) [Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
       Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"]) >>
  drule abi_valid_tuple_view >> strip_tac >>
  qexists_tac `cfields` >>
  gvs[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qpat_x_assum `vyper_decode_valid_enc (Tuple _) bs` mp_tac >> simp_tac bool_ss [Once vyper_decode_valid_enc_def]
QED

(* ===== Scratch Decoder Struct ===== *)

(* Actual-source struct correctness retains independently descending type maps. *)

Theorem abi_scratch_decoder_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (abi_scratch_decoder ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs ==>
  abi_scratch_decoder ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  simp_tac bool_ss [abi_scratch_decoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_struct_inputs >> strip_tac >> gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  (drule abi_decoder_struct_infos >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`,
    `env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
    `tys` |-> `MAP SND (args:(string # vyperAST$type) list)`,
    `vs` |-> `MAP SND (fields:(string # value) list)`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields)
      (MAP SND (args:(string # vyperAST$type) list))`]
    abi_scratch_decoder_complex_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `tuple_in_memory (MAP SND fields) tvs d actual.vs_memory` >>
  `fields_in_memory fields (ZIP (MAP FST args,tvs)) d actual.vs_memory` by
    (irule static_fields_memory_zip >> fs[Once value_has_type_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [val_in_memory_struct])
QED
