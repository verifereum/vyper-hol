(* Package discovered fixed-array members as the source decoder's value. *)
Theory extcallDecoderFixedSemantics
Ancestors
  abiDecoderCoherence abiDecoderContract abiDecoderStruct abiDecoderMembers
  abiValidMembers abiValidAggregateHeads vyperValue vyperTyping vyperTypeABI
  vyperABI vyperABIValid contractABI list words arithmetic

Theorem decoder_fixed_array_completion:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  n < dimword(:256) /\
  vyper_decode_valid_enc_tuple (REPLICATE n (vyper_to_abi_type env ty)) bs bs /\
  abi_to_vyper_list env (REPLICATE n ty)
    (abi_decode_members (REPLICATE n (vyper_to_abi_type env ty)) bs bs) = SOME vs ==>
  vyper_decode_valid_enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) bs /\
  abi_to_vyper env (ArrayT ty (Fixed n))
    (dec (vyper_to_abi_type env (ArrayT ty (Fixed n))) bs) =
    SOME (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) /\
  value_has_type (ArrayTV tv (Fixed n))
    (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)))
Proof
  strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `evaluate_type env (ArrayT ty (Fixed n)) = SOME (ArrayTV tv (Fixed n))` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `LENGTH vs = n` by
    (drule abi_to_vyper_list_lengths >> simp[] >> decide_tac) >>
  `vyper_decode_valid_enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) bs` by
    simp[Once vyper_to_abi_type_def, Once vyper_decode_valid_enc_def,
      GSYM vyper_decode_valid_enc_tuple_REPLICATE] >>
  `dec (vyper_to_abi_type env (ArrayT ty (Fixed n))) bs =
   ListV (abi_decode_members (REPLICATE n (vyper_to_abi_type env ty)) bs bs)` by
    simp[Once vyper_to_abi_type_def, Once dec_def,
      abi_decode_array_members, abi_decode_members_value] >>
  `abi_to_vyper env (ArrayT ty (Fixed n))
    (dec (vyper_to_abi_type env (ArrayT ty (Fixed n))) bs) =
    SOME (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)))` by
    simp[Once abi_to_vyper_def, compatible_bound_def, make_array_value_def] >>
  simp[] >> irule (CONJUNCT1 abi_to_vyper_well_typed) >>
  qexistsl_tac [`dec (vyper_to_abi_type env (ArrayT ty (Fixed n))) bs`,
    `env`, `ArrayT ty (Fixed n)`] >>
  simp[]
QED
