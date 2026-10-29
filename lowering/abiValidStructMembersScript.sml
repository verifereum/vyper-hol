(* Successful struct decoding selects the actual source-valid positional
   children under the independently descended semantic and compiler maps. *)
Theory abiValidStructMembers
Ancestors
  abiValidMembers abiDecoderStruct abiDecoderMembers abiDecoderCoherence abiDecoderTypedContract
  abiBuiltinSource abiDecodeRanges vyperABIValid vyperABI vyperValue contractABI compileEnv
  valueEncoding finite_map list

Theorem abi_valid_struct_source_members:
  abi_decoder_coherent ce env sf (StructT nsid) tv /\
  evaluate_abi_decode env (StructT nsid) bs = INL (StructV vfields) ==>
  ?args tvs. FLOOKUP env nsid = SOME (StructArgs args) /\
    tv = StructTV (ZIP (MAP FST args,tvs)) /\
    valid_enc_tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) bs bs /\
    abi_decoder_members ce (env \\ nsid) (sf \\ nsid_to_string nsid)
      (MAP SND args) tvs
      (abi_decode_members (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) bs bs)
      (MAP SND vfields)
Proof
  strip_tac >> drule_all abi_builtin_source_metadata >> strip_tac >>
  qpat_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decoder_coherent_struct_iff] >> strip_tac >>
  rename1 `FLOOKUP env nsid = SOME (StructArgs args)` >>
  `valid_enc (Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))) bs` by
    (drule evaluate_abi_decode_vyper_valid_enc >>
     asm_simp_tac (srw_ss()) [vyper_valid_enc_def, vyper_to_abi_type_def,
       vyper_to_abi_types_MAP, Excl "valid_enc_def", Excl "dec_def"]) >>
  drule abi_valid_tuple_view >> strip_tac >>
  `dec (vyper_to_abi_type env (StructT nsid)) bs =
    ListV (abi_decode_members (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) bs bs)` by
    asm_simp_tac (srw_ss()) [vyper_to_abi_type_def, vyper_to_abi_types_MAP,
      Excl "dec_def", Excl "valid_enc_def", Excl "enc_def"] >>
  qpat_assum `dec (vyper_to_abi_type env (StructT nsid)) bs = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  drule_all abi_decoder_struct_members >>
  disch_then (qx_choose_then `child_tvs` strip_assume_tac) >>
  qexistsl_tac [`args`, `child_tvs`] >>
  asm_simp_tac bool_ss [] >> fs[Once valid_enc_def]
QED
