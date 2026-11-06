(* Finite descending-map interface checks; no operational execution claim. *)
Theory entryReachBodyDescendingLayoutProbes
Ancestors
  entryReachBodyDescendingProducer entryReachBodyDescendingMetadata
  abiDecoderStruct abiDecoderCoherence abiDecoderMembers
  vyperABI vyperValue vyperTyping compileEnv valueEncoding finite_map
  contractABI abiDecodeRanges
Libs
  finite_mapLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;

Definition descending_probe_env_def:
  descending_probe_env = FEMPTY |+
    ((NONE,"Inner"), StructArgs [("a",BaseT (UintT 256))]) |+
    ((NONE,"Outer"), StructArgs [("items",ArrayT (StructT (NONE,"Inner")) (Fixed 1))])
End

Definition descending_probe_sf_def:
  descending_probe_sf = FEMPTY |+
    ("Inner", [("a",BaseT (UintT 256),32)]) |+
    ("Outer", [("items",ArrayT (StructT (NONE,"Inner")) (Fixed 1),32)])
End

Definition descending_probe_ce_def:
  descending_probe_ce = (ARB : compile_env) with ce_struct_fields := descending_probe_sf
End

Theorem descending_probe_maps[local]:
  FLOOKUP descending_probe_env (NONE,"Inner") =
    SOME (StructArgs [("a",BaseT (UintT 256))]) /\
  FLOOKUP descending_probe_env (NONE,"Outer") =
    SOME (StructArgs [("items",ArrayT (StructT (NONE,"Inner")) (Fixed 1))]) /\
  FLOOKUP descending_probe_sf "Inner" = SOME [("a",BaseT (UintT 256),32)] /\
  FLOOKUP descending_probe_sf "Outer" =
    SOME [("items",ArrayT (StructT (NONE,"Inner")) (Fixed 1),32)] /\
  (NONE,"Inner") <> (NONE,"Outer") /\ "Inner" <> "Outer"
Proof
  EVAL_TAC
QED

Theorem descending_probe_inner_coherent[local]:
  abi_decoder_coherent descending_probe_ce descending_probe_env
    descending_probe_sf (StructT (NONE,"Inner"))
    (StructTV [("a",BaseTV (UintT 256))])
Proof
  `descending_probe_sf = descending_probe_ce.ce_struct_fields` by
    simp[descending_probe_ce_def] >>
  pop_assum SUBST1_TAC >>
  irule abi_decoder_one_field_struct_realizable >>
  simp[descending_probe_maps, descending_probe_ce_def, nsid_to_string_def]
QED

Theorem descending_probe_inner_metadata[local]:
  entry_descending_metadata descending_probe_ce descending_probe_env
    descending_probe_sf (StructT (NONE,"Inner"))
    (StructTV [("a",BaseTV (UintT 256))])
    (type_to_abi_dec_info descending_probe_sf descending_probe_ce (StructT (NONE,"Inner")))
    (ListV [NumV 0]) (StructV [("a",IntV 0)])
Proof
  simp[entry_descending_metadata_def, descending_probe_ce_def,
    type_memory_bytes_def, get_struct_fields_def, descending_probe_sf_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def,
    default_value_def, enumerate_static_array_def]
QED

Theorem descending_probe_inner_members[local]:
  entry_descending_members descending_probe_ce
    (descending_probe_env \\ (NONE,"Inner"))
    (descending_probe_sf \\ "Inner")
    [BaseT (UintT 256)] [BaseTV (UintT 256)] [NumV 0] [IntV 0]
Proof
  mp_tac descending_probe_inner_metadata >>
  rewrite_tac[entry_descending_metadata_transport] >> strip_tac >>
  mp_tac descending_probe_inner_coherent >> strip_tac >>
  mp_tac descending_probe_maps >> strip_tac >>
  drule abi_decoder_struct_members >>
  simp[descending_probe_maps] >>
  disch_then drule >>
  simp[descending_probe_maps, entry_descending_members_equiv,
       nsid_to_string_def] >>
  strip_tac >> drule abi_decoder_members_lengths >> simp[] >>
  Cases_on `tvs` >> simp[] >> Cases_on `t` >> gvs[]
QED

Theorem descending_probe_outer_metadata[local]:
  entry_descending_metadata descending_probe_ce descending_probe_env
    descending_probe_sf (StructT (NONE,"Outer"))
    (StructTV [("items",ArrayTV (StructTV [("a",BaseTV (UintT 256))]) (Fixed 1))])
    (type_to_abi_dec_info descending_probe_sf descending_probe_ce (StructT (NONE,"Outer")))
    (ListV [ListV [ListV [NumV 0]]])
    (StructV [("items",ArrayV (SArrayV []))])
Proof
  simp[entry_descending_metadata_def, descending_probe_ce_def,
    type_memory_bytes_def, get_struct_fields_def, descending_probe_sf_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def,
    default_value_def, enumerate_static_array_def]
QED


Theorem descending_probe_inner_header[local]:
  abi_decoder_header descending_probe_ce
    (descending_probe_env \\ (NONE,"Outer")) (StructT (NONE,"Inner"))
    (StructTV [("a",BaseTV (UintT 256))])
Proof
  simp[abi_decoder_header_def, descending_probe_ce_def,
    type_memory_bytes_def, get_struct_fields_def, descending_probe_sf_def,
    is_abi_dynamic_def, abi_embedded_static_size_def, abi_static_size_def,
    abi_member_head_size_def, vyper_to_abi_type_def, vyper_to_abi_types_MAP,
    is_dynamic_def, static_length_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def]
QED

Theorem descending_probe_array_header[local]:
  abi_decoder_header descending_probe_ce
    (descending_probe_env \\ (NONE,"Outer"))
    (ArrayT (StructT (NONE,"Inner")) (Fixed 1))
    (ArrayTV (StructTV [("a",BaseTV (UintT 256))]) (Fixed 1))
Proof
  simp[abi_decoder_header_def, descending_probe_ce_def,
    type_memory_bytes_def, get_struct_fields_def, descending_probe_sf_def,
    is_abi_dynamic_def, abi_embedded_static_size_def, abi_static_size_def,
    abi_member_head_size_def, vyper_to_abi_type_def, vyper_to_abi_types_MAP,
    is_dynamic_def, static_length_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def]
QED

Theorem descending_probe_outer_header[local]:
  abi_decoder_header descending_probe_ce descending_probe_env (StructT (NONE,"Outer"))
    (StructTV [("items",ArrayTV (StructTV [("a",BaseTV (UintT 256))]) (Fixed 1))])
Proof
  simp[abi_decoder_header_def, descending_probe_ce_def,
    type_memory_bytes_def, get_struct_fields_def, descending_probe_sf_def,
    is_abi_dynamic_def, abi_embedded_static_size_def, abi_static_size_def,
    abi_member_head_size_def, vyper_to_abi_type_def, vyper_to_abi_types_MAP,
    is_dynamic_def, static_length_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def]
QED

Theorem descending_probe_inner_deleted_coherent[local]:
  abi_decoder_coherent descending_probe_ce
    (descending_probe_env \\ (NONE,"Outer")) (descending_probe_sf \\ "Outer")
    (StructT (NONE,"Inner")) (StructTV [("a",BaseTV (UintT 256))])
Proof
  simp[abi_decoder_coherent_struct_iff, descending_probe_env_def,
    descending_probe_sf_def, FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM,
    nsid_to_string_def] >>
  qexists_tac `[BaseTV (UintT 256)]` >>
  simp[abi_decoder_uint256_probe, type_memory_bytes_def] >>
  mp_tac descending_probe_inner_header >> simp[descending_probe_env_def]
QED

Theorem descending_probe_array_coherent[local]:
  abi_decoder_coherent descending_probe_ce
    (descending_probe_env \\ (NONE,"Outer")) (descending_probe_sf \\ "Outer")
    (ArrayT (StructT (NONE,"Inner")) (Fixed 1))
    (ArrayTV (StructTV [("a",BaseTV (UintT 256))]) (Fixed 1))
Proof
  simp[abi_decoder_coherent_array_iff, descending_probe_inner_deleted_coherent,
    descending_probe_array_header]
QED

Theorem descending_probe_outer_coherent[local]:
  abi_decoder_coherent descending_probe_ce descending_probe_env descending_probe_sf
    (StructT (NONE,"Outer"))
    (StructTV [("items",ArrayTV (StructTV [("a",BaseTV (UintT 256))]) (Fixed 1))])
Proof
  simp[abi_decoder_coherent_struct_iff, descending_probe_maps, nsid_to_string_def] >>
  qexists_tac `[ArrayTV (StructTV [("a",BaseTV (UintT 256))]) (Fixed 1)]` >>
  simp[descending_probe_array_coherent, descending_probe_outer_header,
    descending_probe_ce_def, descending_probe_sf_def,
    type_memory_bytes_def, get_struct_fields_def, nsid_to_string_def,
    FLOOKUP_UPDATE] >>
  mp_tac descending_probe_array_coherent >>
  simp[descending_probe_ce_def, descending_probe_sf_def]
QED

Theorem descending_probe_outer_members[local]:
  entry_descending_members descending_probe_ce
    (descending_probe_env \\ (NONE,"Outer")) (descending_probe_sf \\ "Outer")
    [ArrayT (StructT (NONE,"Inner")) (Fixed 1)]
    [ArrayTV (StructTV [("a",BaseTV (UintT 256))]) (Fixed 1)]
    [ListV [ListV [NumV 0]]] [ArrayV (SArrayV [])]
Proof
  mp_tac descending_probe_outer_metadata >>
  rewrite_tac[entry_descending_metadata_transport] >> strip_tac >>
  mp_tac descending_probe_outer_coherent >> strip_tac >>
  drule abi_decoder_struct_members >> simp[descending_probe_maps] >>
  disch_then drule >> simp[entry_descending_members_equiv, nsid_to_string_def] >>
  strip_tac >> drule abi_decoder_members_lengths >> simp[] >>
  Cases_on `tvs` >> simp[] >> Cases_on `t` >> gvs[]
QED

Theorem descending_probe_nested_inner_metadata[local]:
  entry_descending_metadata descending_probe_ce
    (descending_probe_env \\ (NONE,"Outer")) (descending_probe_sf \\ "Outer")
    (StructT (NONE,"Inner")) (StructTV [("a",BaseTV (UintT 256))])
    (type_to_abi_dec_info (descending_probe_sf \\ "Outer") descending_probe_ce
      (StructT (NONE,"Inner"))) (ListV [NumV 0]) (StructV [("a",IntV 0)])
Proof
  simp[entry_descending_metadata_def, descending_probe_ce_def,
    type_memory_bytes_def, get_struct_fields_def, descending_probe_sf_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem descending_probe_nested_inner_members[local]:
  entry_descending_members descending_probe_ce
    (descending_probe_env \\ (NONE,"Outer") \\ (NONE,"Inner"))
    (descending_probe_sf \\ "Outer" \\ "Inner")
    [BaseT (UintT 256)] [BaseTV (UintT 256)] [NumV 0] [IntV 0]
Proof
  mp_tac descending_probe_nested_inner_metadata >>
  rewrite_tac[entry_descending_metadata_transport] >> strip_tac >>
  mp_tac descending_probe_inner_deleted_coherent >> strip_tac >>
  `FLOOKUP ((descending_probe_env : nsid |-> type_args) \\ (NONE,"Outer")) (NONE,"Inner") =
    SOME (StructArgs [("a",BaseT (UintT 256))])` by
    simp[descending_probe_env_def, DOMSUB_FLOOKUP_THM, FLOOKUP_UPDATE] >>
  drule abi_decoder_struct_members >> asm_simp_tac (srw_ss()) [] >>
  disch_then drule >> simp[entry_descending_members_equiv, nsid_to_string_def] >>
  strip_tac >> drule abi_decoder_members_lengths >> simp[] >>
  Cases_on `tvs` >> simp[] >> Cases_on `t` >> gvs[]
QED

Theorem descending_probe_descriptor_steps[local]:
  type_to_abi_dec_info descending_probe_sf descending_probe_ce (StructT (NONE,"Outer")) =
    DecComplex F [(type_to_abi_dec_info (descending_probe_sf \\ "Outer")
      descending_probe_ce (ArrayT (StructT (NONE,"Inner")) (Fixed 1)),32,32)] /\
  type_to_abi_dec_info (descending_probe_sf \\ "Outer") descending_probe_ce
    (ArrayT (StructT (NONE,"Inner")) (Fixed 1)) =
    DecComplex F [(type_to_abi_dec_info (descending_probe_sf \\ "Outer")
      descending_probe_ce (StructT (NONE,"Inner")),32,32)] /\
  type_to_abi_dec_info (descending_probe_sf \\ "Outer") descending_probe_ce
    (StructT (NONE,"Inner")) =
    DecComplex F [(type_to_abi_dec_info (descending_probe_sf \\ "Outer" \\ "Inner")
      descending_probe_ce (BaseT (UintT 256)),32,32)] /\
  type_to_abi_dec_info (descending_probe_sf \\ "Outer" \\ "Inner")
    descending_probe_ce (BaseT (UintT 256)) = DecPrimWord NoClamp
Proof
  simp[descending_probe_ce_def] >> EVAL_TAC
QED

Theorem descending_probe_root_specialization[local]:
  entry_descending_certified_child_producer cert descending_probe_ce descending_probe_env
    descending_probe_sf (StructT (NONE,"Outer"))
    (StructTV [("items",ArrayTV (StructTV [("a",BaseTV (UintT 256))]) (Fixed 1))])
    (ListV [ListV [ListV [NumV 0]]]) (StructV [("items",ArrayV (SArrayV []))])
    ctx fn oid root extent ambient b cap site limit_st <=>
  entry_certified_child_producer cert descending_probe_ce descending_probe_env
    (StructT (NONE,"Outer"))
    (StructTV [("items",ArrayTV (StructTV [("a",BaseTV (UintT 256))]) (Fixed 1))])
    (ListV [ListV [ListV [NumV 0]]]) (StructV [("items",ArrayV (SArrayV []))])
    ctx fn oid root extent ambient b cap site limit_st
Proof
  `descending_probe_sf = descending_probe_ce.ce_struct_fields` by
    simp[descending_probe_ce_def] >>
  pop_assum SUBST1_TAC >>
  irule entry_descending_certified_child_root
QED
