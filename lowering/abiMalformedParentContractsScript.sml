(* Semantic constructor adapters for coherent-type induction. *)
Theory abiMalformedParentContracts
Ancestors
  abiMalformedParentAggregate abiMalformedMembersFold
  abiMalformedConstructorInduction abiMalformedBytesExecution
  abiMalformedConstructorContract abiDecoderCoherence abiDecoderWordTyped
  exprLowering compileEnv vyperABI vyperTypeSystem valueEncoding words list

Theorem abi_malformed_base_type_contract:
  !ce env sf bt.
    abi_decoder_scalar_valid bt /\
    abi_decoder_header ce env (BaseT bt) (BaseTV bt) ==>
    abi_malformed_type_contract ce env sf (BaseT bt) (BaseTV bt)
Proof
  rpt gen_tac >> strip_tac >>
  `abi_decoder_coherent ce env sf (BaseT bt) (BaseTV bt)` by
    simp[abi_decoder_coherent_base_iff] >>
  `(?clamp. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp /\
      type_memory_bytes ce (BaseT bt) = 32) \/
   (?n. type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring n)` by
    (Cases_on `bt` >> simp[type_to_abi_dec_info_def, type_memory_bytes_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     simp[type_to_abi_dec_info_def, type_memory_bytes_def])
  >- (simp[abi_malformed_type_contract_def] >> rpt strip_tac >> gvs[] >>
      irule abi_malformed_primitive_constructor >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule abi_malformed_bytes_type_contract >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_malformed_flag_type_contract:
  !ce env sf nsid n.
    FLOOKUP env nsid = SOME (FlagArgs n) /\ n <= 256 /\
    ce.ce_flag_n_members (nsid_to_string nsid) = n /\
    abi_decoder_header ce env (FlagT nsid) (FlagTV n) ==>
    abi_malformed_type_contract ce env sf (FlagT nsid) (FlagTV n)
Proof
  rpt gen_tac >> strip_tac >>
  `abi_decoder_coherent ce env sf (FlagT nsid) (FlagTV n)` by
    (simp[abi_decoder_coherent_flag_iff] >> metis_tac[]) >>
  simp[abi_malformed_type_contract_def, type_to_abi_dec_info_def,
       type_memory_bytes_def] >> rpt strip_tac >> gvs[] >>
  irule abi_malformed_primitive_constructor >>
  goal_assum (drule_at Any) >> simp[type_to_abi_dec_info_def] >> metis_tac[]
QED
