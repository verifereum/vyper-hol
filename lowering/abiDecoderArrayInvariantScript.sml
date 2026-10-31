(* Memory observations carried through the actual finite array decoder loop. *)
Theory abiDecoderArrayInvariant
Ancestors
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiCanonicalHeadSize
  abiDecoderArrayPrefix abiDecoderFrameCompose valueEncodingProps valueEncoding
  vyperABI vyperABIRoundtrip vyperTyping vyperValue venomState words list rich_list arithmetic

Theorem abi_decoder_dynarray_values:
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) ==>
  LENGTH avs = LENGTH vs /\ all_have_type tv vs /\ LENGTH vs <= maxn /\
  has_type (Array NONE (vyper_to_abi_type env ty)) (ListV avs)
Proof
  strip_tac >> qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  `evaluate_type env ty = SOME tv` by
    (qpat_x_assum `evaluate_type env (ArrayT _ _) = _` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs()]) >>
  `abi_to_vyper_list env (REPLICATE (LENGTH avs) ty) avs = SOME vs` by
    (qpat_x_assum `abi_to_vyper env (ArrayT _ _) _ = _` mp_tac >>
     simp[Once abi_to_vyper_def, make_array_value_def, AllCaseEqs()]) >>
  drule abi_to_vyper_list_EL >> strip_tac >>
  `all_have_type tv vs /\ LENGTH vs <= maxn` by fs[Once value_has_type_def] >>
  `has_type (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[Once vyper_to_abi_type_def] >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED

Definition abi_decoder_array_memory_def:
  abi_decoder_array_memory opc aty avs tv vs sb d j s <=>
    j <= LENGTH vs /\ mem_word_at d s.vs_memory = n2w (LENGTH vs) /\
    elems_in_memory (TAKE j vs) (d + 32) tv s.vs_memory /\
    mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV avs)))
      (abi_decode_source opc s) = enc (Array NONE aty) (ListV avs)
End

Theorem abi_decoder_array_memory_init:
  mem_word_at d s.vs_memory = n2w (LENGTH vs) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV avs)))
    (abi_decode_source opc s) = enc (Array NONE aty) (ListV avs) ==>
  abi_decoder_array_memory opc aty avs tv vs sb d 0 s
Proof
  simp[abi_decoder_array_memory_def, val_in_memory_def, Excl "enc_def"]
QED

Theorem abi_decoder_array_memory_exit:
  abi_decoder_array_memory opc aty avs tv vs sb d (LENGTH vs) s ==>
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d s.vs_memory
Proof
  simp[abi_decoder_array_memory_def, val_in_memory_dynarray, Excl "enc_def"]
QED

Theorem abi_decoder_array_memory_update[simp]:
  abi_decoder_array_memory opc aty avs tv vs sb d j (update_var name w s) <=>
  abi_decoder_array_memory opc aty avs tv vs sb d j s
Proof
  simp[abi_decoder_array_memory_def, update_var_def, abi_decode_source_def, Excl "enc_def"]
QED

Theorem abi_decoder_array_memory_jump[simp]:
  abi_decoder_array_memory opc aty avs tv vs sb d j (jump_to lbl s) <=>
  abi_decoder_array_memory opc aty avs tv vs sb d j s
Proof
  simp[abi_decoder_array_memory_def, jump_to_def, abi_decode_source_def, Excl "enc_def"]
QED

Theorem abi_decoder_array_memory_count:
  abi_decoder_array_memory opc aty avs tv vs sb d j s /\ LENGTH avs = LENGTH vs /\
  sb + LENGTH (enc (Array NONE aty) (ListV avs)) < dimword (:256) ==>
  abi_decode_load opc (n2w sb : bytes32) s = n2w (LENGTH vs)
Proof
  simp_tac bool_ss [abi_decoder_array_memory_def] >> strip_tac >>
  drule_all canonical_dynamic_array_count_load >> simp[]
QED
