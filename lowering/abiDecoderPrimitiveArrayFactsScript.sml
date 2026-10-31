(* Derive the loop initializer's arithmetic from typed canonical array inputs. *)
Theory abiDecoderPrimitiveArrayFacts
Ancestors
  abiDecoderArrayInvariant abiDecoderArrayAdvance abiDecoderPrimitiveLoopContext
  abiDecoderCoherence abiDecoderTypedContract abiDecoderWordTyped abiDecoderContract
  abiCanonicalHeadSize abiCanonicalHeadSize abiDecoderBulk compileEnv exprLowering valueEncoding
  vyperABI vyperTyping vyperValue contractABI byte words list arithmetic

Theorem abi_decoder_static_word_array_length:
  has_type (Array NONE aty) (ListV avs) /\ ~is_dynamic aty /\ static_length aty = 32 ==>
  LENGTH (enc (Array NONE aty) (ListV avs)) = 32 + LENGTH avs * 32
Proof
  strip_tac >>
  `has_type (Array (SOME (LENGTH avs)) aty) (ListV avs)` by fs[has_type_def] >>
  mp_tac (Q.SPECL [`Array (SOME (LENGTH (avs:abi_value list))) aty`, `ListV avs`]
    (cj 1 enc_has_static_length)) >>
  asm_simp_tac bool_ss [is_dynamic_def, static_length_def] >> strip_tac >>
  `enc (Array NONE aty) (ListV avs) = enc_number (Uint 256) (NumV (LENGTH avs)) ++
    enc (Array (SOME (LENGTH avs)) aty) (ListV avs)` by
    (pure_rewrite_tac [canonical_array_tuple] >> simp[]) >>
  simp[enc_number_def, LENGTH_word_to_bytes, Excl "enc_def"]
QED

Theorem abi_decoder_primitive_dynarray_pre_facts:
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap s ==>
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  type_memory_size tv = 32 /\ type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * 32 /\
  LENGTH avs = LENGTH vs /\ LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) = 32 + LENGTH vs * 32 /\
  abi_decode_load opc (n2w sb:bytes32) s = n2w (LENGTH vs) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    sb + 32 + LENGTH vs * 32 <= h /\ h < dimword (:256))
Proof
  simp_tac bool_ss [abi_decoder_recursive_pre_def, abi_decoder_pre_def,
                   abi_decoder_ranges_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `type_to_abi_dec_info sf ce ty = DecPrimWord clamp` by
    (qpat_x_assum `DecDynArray _ _ _ _ _ = type_to_abi_dec_info _ _ _` mp_tac >>
     simp[Once type_to_abi_dec_info_def]) >>
  drule_all abi_decoder_dynarray_values >> strip_tac >>
  drule_all abi_decoder_primitive_array_sizes >> strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_header ce env ty tv` by metis_tac[abi_decoder_coherent_header] >>
  `~is_dynamic (vyper_to_abi_type env ty) /\ static_length (vyper_to_abi_type env ty) = 32`
    by fs[abi_decoder_header_def] >>
  `LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) = 32 + LENGTH vs * 32`
    by (drule_all abi_decoder_static_word_array_length >> simp[]) >>
  `maxn < dimword (:256)` by
    (irule abi_decoder_primitive_count_bound >> qexists_tac `d` >> gvs[Excl "enc_def"]) >>
  `abi_decode_load opc (n2w sb:bytes32) s = n2w (LENGTH avs)` by
    (irule canonical_dynamic_array_count_load >> qexists_tac `vyper_to_abi_type env ty` >>
     gvs[Once vyper_to_abi_type_def, Excl "enc_def"]) >>
  gvs[Once vyper_to_abi_type_def, Excl "enc_def"] >>
  disj2_tac >> qexists_tac `h` >> simp[]
QED
