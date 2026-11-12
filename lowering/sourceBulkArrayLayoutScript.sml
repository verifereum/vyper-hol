(* Source-valued bulk array layout, including empty arrays. *)
Theory sourceBulkArrayLayout
Ancestors
  abiDecoderCoherence abiDecoderLayout abiStaticDynarrayLayout abiDecoderBulk
  vyperTyping vyperABI vyperValue valueEncoding valueEncodingProps
  abiEncoder exprLowering contractABI list words arithmetic

Theorem source_bulk_array_layout:
  abi_decoder_coherent ce env sf (ArrayT ety (Dynamic maxn)) tv /\
  ~is_abi_dynamic ce.ce_struct_fields ety /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ety) /\
  value_has_type tv v /\
  vyper_to_abi env (ArrayT ety (Dynamic maxn)) v = SOME av ==>
  ?etv vs avs.
    tv = ArrayTV etv (Dynamic maxn) /\ v = ArrayV (DynArrayV vs) /\
    av = ListV avs /\ LENGTH vs <= maxn /\ all_have_type etv vs /\
    vyper_to_abi_same env ety vs = SOME avs /\
    static_layout_compatible ce env ety etv /\
    type_memory_bytes ce ety = type_memory_size etv /\
    LENGTH avs = LENGTH vs /\
    LENGTH (FLAT (MAP (enc (vyper_to_abi_type env ety)) avs)) =
      LENGTH vs * type_memory_size etv /\
    enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av =
      word_to_bytes (n2w (LENGTH vs) : bytes32) T ++
      FLAT (MAP (enc (vyper_to_abi_type env ety)) avs)
Proof
  strip_tac >>
  gvs[abi_decoder_coherent_array_iff] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  Cases_on `a` >> gvs[value_has_type_def] >>
  gvs[vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"] >>
  `static_layout_compatible ce env ety tv'` by
    (irule abi_decoder_unclamped_static_layout >> metis_tac[]) >>
  drule_all static_same_canonical_layout >> strip_tac >>
  `type_memory_bytes ce ety = type_memory_size tv' /\
   ~is_dynamic (vyper_to_abi_type env ety)` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  simp[static_dynarray_encoding, Excl "enc_def"]
QED
