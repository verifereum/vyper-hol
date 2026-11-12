(* Transfer a child's compiler-selected byte view to source member semantics. *)
Theory abiMalformedMemberReflection
Ancestors
  abiMalformedConstructorContract abiDecoderOffset abiDecoderDynamic
  abiValidMembers abiMalformedMembers abiDecodeRanges vyperABI contractABI list rich_list arithmetic

Theorem abi_malformed_member_reflection:
  abi_decoder_coherent ce env sf ty tv /\
  LENGTH xs = L /\
  p + ao + abi_member_head_size (vyper_to_abi_type env ty) <= L /\
  child_pos = p + (if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
            then abi_head_word (DROP (p+ao) xs) else ao) /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (if is_dynamic (vyper_to_abi_type env ty) then DROP child_pos xs
     else TAKE (static_length (vyper_to_abi_type env ty)) (DROP child_pos xs)) /\
  abi_vyper_admissible env ty
    (dec (vyper_to_abi_type env ty)
      (if is_dynamic (vyper_to_abi_type env ty) then DROP child_pos xs
       else TAKE (static_length (vyper_to_abi_type env ty)) (DROP child_pos xs))) ==>
  (is_dynamic (vyper_to_abi_type env ty) ==>
    is_num_value (dec_number (Uint 256) (TAKE 32 (DROP (p+ao) xs)))) /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty)
      (DROP p xs) (DROP (p+ao) xs)) /\
  abi_vyper_admissible env ty
    (dec (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty)
        (DROP p xs) (DROP (p+ao) xs)))
Proof
  strip_tac >> conj_tac
  >- (strip_tac >> fs[abi_member_head_size_def] >>
      simp[dec_number_def, is_num_value_def, LENGTH_DROP] >> decide_tac) >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (drule_all abi_malformed_empty_source >> simp[]) >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty)` by
    metis_tac[abi_decoder_nonempty_offset, abi_decoder_coherent_dynamic] >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
  gvs[abi_decode_member_bytes_def, DROP_DROP_T, ADD_COMM]
QED
