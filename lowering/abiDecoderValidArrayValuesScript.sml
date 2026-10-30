(* Successful conversion relates the actual array count and decoded children. *)
Theory abiDecoderValidArrayValues
Ancestors
  abiValidAggregateHeads abiValidMembers abiDecoderArrayInvariant abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract compileEnv valueEncoding vyperABI vyperValue
  contractABI venomState words list rich_list arithmetic

Theorem abi_decoder_valid_dynarray_values:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs ==>
  32 <= LENGTH bs /\ abi_head_word bs = LENGTH vs /\ all_have_type tv vs /\ LENGTH vs <= maxn /\
  abi_decoder_coherent ce env sf ty tv /\ type_memory_size tv = type_memory_bytes ce ty /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (ListV (abi_decode_members (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty))
      (DROP 32 bs) (DROP 32 bs))) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc_tuple (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty)) (DROP 32 bs) (DROP 32 bs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_valid_dynamic_array_view >> strip_tac >>
  qpat_assum `dec (Array NONE _) bs = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `abi_head_word bs = LENGTH vs` by
    fs[abi_decode_members_length, LENGTH_REPLICATE, Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  drule abi_decoder_coherent_header >> strip_tac >>
  qpat_assum `abi_decoder_header ce env ty tv`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_header_def]) >>
  qpat_assum `abi_head_word bs = LENGTH vs`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  asm_simp_tac bool_ss []
QED
