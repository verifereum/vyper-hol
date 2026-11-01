(* Advance actual decoded-member metadata with the compiler's two cursors. *)
Theory abiDecoderValidMemberCursor
Ancestors
  abiDecoderMembers abiDecoderCoherence abiDecoderTypedContract abiValidMembers
  abiDecodeRanges compileEnv valueEncoding vyperABI vyperValue contractABI
  list rich_list arithmetic

Theorem abi_decoder_valid_member_cursor:
  abi_decoder_members ce env sf (ty::tys) (tv::tvs)
    (abi_decode_members (MAP (vyper_to_abi_type env) (ty::tys)) bs
      (DROP (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) bs)) (v::vs) ==>
  abi_decoder_coherent ce env sf ty tv /\
  abi_to_vyper env ty
    (dec (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
        (DROP (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) bs))) = SOME v /\
  value_has_type tv v /\ type_memory_size tv = type_memory_bytes ce ty /\
  abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty) /\
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs
      (DROP (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (pretys ++ [ty])))) bs)) vs
Proof
  simp_tac bool_ss [MAP, abi_decode_members_def, Once abi_decoder_members_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_coherent_header >> strip_tac >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  qpat_assum `abi_decoder_header ce env ty tv`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_header_def]) >>
  asm_simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, DROP_DROP_T, ADD_CLAUSES, ADD_COMM] >>
  qpat_x_assum `abi_decoder_members ce env sf tys tvs _ vs`
    (mp_tac o PURE_REWRITE_RULE [DROP_DROP_T]) >> simp_tac bool_ss [ADD_COMM]
QED
