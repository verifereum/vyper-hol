(* Source conversion supplies structural encoding layout, without ABI typing. *)
Theory sourceEncodingLayout
Ancestors entryDecodePlanProps abiDecoderCoherence sourceEncodingWindows
  abiEncoderOpenInput abiDecodeRanges vyperABIRoundtrip list

Theorem coherent_source_encoding_layout:
  abi_decoder_coherent ce env sf ty tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
  abi_encoder_layout_valid (vyper_to_abi_type env ty) av
Proof
  strip_tac >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> strip_tac >>
  simp[abi_encoder_layout_valid_def] >> strip_tac >>
  `~is_dynamic (vyper_to_abi_type env ty)` by metis_tac[] >>
  drule_all (cj 1 vyper_to_abi_static_enc_length) >> simp[]
QED

Theorem coherent_source_list_encoding_layout:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL value_has_type tvs vs /\
  vyper_to_abi_list env tys vs = SOME avs ==>
  LIST_REL abi_encoder_layout_valid (MAP (vyper_to_abi_type env) tys) avs
Proof
  strip_tac >> drule vyper_to_abi_list_EL >> strip_tac >>
  `LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    metis_tac[LIST_REL_LENGTH] >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  simp[EL_MAP] >> irule coherent_source_encoding_layout >>
  qexistsl_tac [`ce`, `sf`, `EL n tvs`, `EL n vs`] >> simp[]
QED

(* This is exactly the alignment premise of both structural indexed windows.
   Homogeneous array consumers instantiate tys with REPLICATE n ty. *)
Theorem coherent_source_list_head_lengths:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL value_has_type tvs vs /\
  vyper_to_abi_list env tys vs = SOME avs ==>
  LIST_REL (\ty av. ~is_dynamic ty ==>
    LENGTH (enc ty av) = abi_member_head_size ty)
    (MAP (vyper_to_abi_type env) tys) avs
Proof
  strip_tac >> drule_all coherent_source_list_encoding_layout >>
  simp[LIST_REL_EL_EQN, abi_encoder_layout_valid_def, abi_member_head_size_def]
QED
