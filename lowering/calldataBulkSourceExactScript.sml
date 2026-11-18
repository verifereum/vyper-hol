Theory calldataBulkSourceExact
Ancestors
  calldataBulkLive calldataSourceDecisions calldataSourceSize calldataSourceCorrespondence
  calldataReconstruction vyperCalldata vyperCalldataProps
  abiDecoderCoherence valueEncoding valueEncodingTyping
  compileEnv exprLowering abiEncoder words list arithmetic
  calldataWordProps entryDecodeProps valueEncodingProps calldataRecursiveProducers

Theorem calldata_bulk_descriptor_layout:
  abi_decoder_coherent ce env sf (ArrayT ety (Dynamic maxn)) tv /\
  type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\
  ~dec_info_needs_clamp ei ==>
  ?etv. tv = ArrayTV etv (Dynamic maxn) /\
    abi_decoder_coherent ce env sf ety etv /\
    ~tv_abi_dynamic etv /\ ~tv_needs_clamp etv /\
    mem_sz = type_memory_size etv /\
    type_memory_size tv = 32+maxn*mem_sz
Proof
  simp[abi_decoder_coherent_array_iff, type_to_abi_dec_info_def] >>
  rpt strip_tac >> qexists_tac `tv'` >> simp[] >>
  drule calldata_coherent_clamp >>
  drule calldata_coherent_dynamic >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def, valueEncodingTheory.type_memory_size_def]
QED

Theorem calldata_bulk_capacity:
  d + (32 + maxn * mem_sz) < dimword (:256) /\ n <= maxn ==>
  32+n*mem_sz <= 32+maxn*mem_sz /\
  d+32 < dimword (:256) /\ n*mem_sz < dimword (:256)
Proof
  strip_tac >>
  `n*mem_sz <= maxn*mem_sz` by simp[] >> decide_tac
QED

Theorem calldata_bulk_source_decode:
  ~tv_abi_dynamic etv /\ ~tv_needs_clamp etv ==>
  cd_decode F cd (ArrayTV etv (Dynamic maxn)) (w2n p) =
    if maxn < w2n (cd_word cd (w2n p)) then NONE
    else OPTION_MAP (ArrayV o DynArrayV)
      (cd_decode_elems T cd etv (w2n ((p:bytes32)+32w)) 0
        (w2n (cd_word cd (w2n p))))
Proof
  simp[Once cd_decode_def, cd_at_def, word_add_def, w2n_n2w] >>
  strip_tac >> CASE_TAC >> simp[]
QED

Theorem calldata_unclamped_word_source:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  mem_word_at d mem = cd_word cd p ==>
  ?v. cd_word_value tv (cd_word cd p) = SOME v /\
    value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v d mem
Proof
  strip_tac >>
  `evaluate_type env ty = SOME tv` by
    (drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  `abi_clamp_ok
    (case type_to_abi_dec_info sf ce ty of DecPrimWord c => c | _ => NoClamp)
    (cd_word cd p)` by
    (Cases_on `ty` >>
     gvs[is_word_type_def, type_to_abi_dec_info_def, dec_info_needs_clamp_def,
         needs_clamp_def, abi_clamp_ok_def, AllCaseEqs(),
         SF boolSimps.COND_elim_ss] >>
     Cases_on `b` >>
     gvs[is_word_type_def, type_to_abi_dec_info_def, type_to_abi_clamp_def,
         dec_info_needs_clamp_def, needs_clamp_def, abi_clamp_ok_def,
         AllCaseEqs(), SF boolSimps.COND_elim_ss] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_word_type_def, type_to_abi_dec_info_def, type_to_abi_clamp_def,
         dec_info_needs_clamp_def, needs_clamp_def, abi_clamp_ok_def,
         AllCaseEqs(), SF boolSimps.COND_elim_ss]) >>
  `!nsid. ty = FlagT nsid ==>
    ?m. FLOOKUP env nsid = SOME (FlagArgs m) /\
      ce.ce_flag_n_members (nsid_to_string nsid) = m` by
    (rpt strip_tac >> gvs[abi_decoder_coherent_flag_iff] >> metis_tac[]) >>
  drule_all word_arg_clamp_inverse_selected >> strip_tac >>
  qexists_tac `v` >> simp[] >> conj_tac
  >- metis_tac[cd_word_value_encoding] >> conj_tac
  >- (irule (cj 1 value_has_type_val_wf) >> simp[]) >>
  irule calldata_word_representation >> metis_tac[]
QED
