(* Codec boundary for arbitrary static-window reflection. *)
Theory abiMalformedStaticReflection
Ancestors
  abiBoundedLeafReflection abiMalformedPrefix abiDecodeRanges entryDecodeStaticProps calldataReconstruction valueEncodingProps
  vyperTypeABI vyperABI vyperTyping vyperABIValid abiVyperAdmissible abiDecoderCoherence
  vyperABIRoundtrip vyperTypeDefaults abiStaticSparseProps
  contractABI vyperValue valueEncoding valueEncodingDefs words list rich_list alist pair arithmetic

Theorem abi_typed_encoding_reflected:
  has_type (vyper_to_abi_type env ty) av /\
  abi_vyper_admissible env ty av /\
  LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (enc (vyper_to_abi_type env ty) av) /\
  abi_vyper_admissible env ty
    (dec (vyper_to_abi_type env ty) (enc (vyper_to_abi_type env ty) av))
Proof
  strip_tac >>
  `dec (vyper_to_abi_type env ty) (enc (vyper_to_abi_type env ty) av) = av` by
    (drule_all (cj 1 dec_enc) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  simp[] >> irule valid_enc_vyper_decode_valid_enc >>
  drule_all (cj 1 enc_valid) >>
  disch_then (qspec_then `[]` mp_tac) >> simp[]
QED

Theorem abi_unclamped_static_encoding_witness:
  abi_decoder_coherent ce env sf ty tv /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  LENGTH bs = static_length (vyper_to_abi_type env ty) ==>
  ?v av. value_has_type tv v /\ val_wf tv v /\
    vyper_to_abi env ty v = SOME av /\
    bs = enc (vyper_to_abi_type env ty) av
Proof
  strip_tac >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  drule_all calldata_unclamped_static_typed >>
  disch_then (qspecl_then [`0`, `bs`] strip_assume_tac) >>
  drule_all (cj 1 vyper_to_abi_total) >> strip_tac >>
  qexistsl_tac [`v`, `av`] >> asm_simp_tac bool_ss [] >>
  `~is_dynamic (vyper_to_abi_type env ty)` by metis_tac[] >>
  `type_memory_size tv = LENGTH bs` by metis_tac[] >>
  drule_all val_in_memory_static_abi >>
  qpat_x_assum `type_memory_size tv = LENGTH bs` SUBST1_TAC >>
  simp_tac std_ss [mem_bytes_at_def, DROP_0, TAKE_APPEND, TAKE_LENGTH_ID,
    TAKE_0, APPEND_NIL]
QED

Theorem abi_typed_conversion_list_admissible[local]:
  !tys tvs vs avs.
  LIST_REL (\ty tv. !v av. value_has_type tv v /\
    vyper_to_abi env ty v = SOME av ==> abi_vyper_admissible env ty av)
    tys tvs /\ values_have_types tvs vs /\
  vyper_to_abi_list env tys vs = SOME avs ==>
  abi_vyper_admissible_list env tys avs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `vs` >>
  simp_tac std_ss [LIST_REL_def, value_has_type_def, Once vyper_to_abi_def,
    abi_vyper_admissible_list_nil] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs(), Excl "vyper_to_abi_def"] >>
  simp[abi_vyper_admissible_list_nil, abi_vyper_admissible_list_cons] >>
  metis_tac[]
QED

Theorem abi_typed_conversion_same_admissible[local]:
  (!v av. value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
      abi_vyper_admissible env ty av) ==>
  !vs avs. all_have_type tv vs /\ vyper_to_abi_same env ty vs = SOME avs ==>
    abi_vyper_admissible_list env (REPLICATE (LENGTH avs) ty) avs /\
    LENGTH avs = LENGTH vs
Proof
  strip_tac >> Induct >>
  simp_tac std_ss [value_has_type_def, Once vyper_to_abi_def, LENGTH,
    REPLICATE, abi_vyper_admissible_list_nil] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs(), Excl "vyper_to_abi_def"] >>
  simp[abi_vyper_admissible_list_nil, abi_vyper_admissible_list_cons] >>
  metis_tac[]
QED

Theorem abi_typed_conversion_sparse_admissible[local]:
  (!v av. value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
      abi_vyper_admissible env ty av) /\
  abi_vyper_admissible env ty (default_to_abi tv) ==>
  !n sp avs m. sparse_has_type tv m sp /\
    vyper_to_abi_sparse env ty tv n sp = SOME avs ==>
    abi_vyper_admissible_list env (REPLICATE (LENGTH avs) ty) avs
Proof
  strip_tac >> Induct >>
  simp_tac std_ss [Once vyper_to_abi_def, LENGTH, REPLICATE,
    abi_vyper_admissible_list_nil] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs(), Excl "vyper_to_abi_def"] >>
  rename1 `vyper_to_abi_sparse env ty tv n sp = SOME prior` >>
  `abi_vyper_admissible_list env (REPLICATE (LENGTH prior) ty) prior` by
    metis_tac[] >>
  qmatch_goalsub_abbrev_tac `abi_vyper_admissible_list env _ output` >>
  qspec_then `output` mp_tac abi_vyper_admissible_replicate >>
  simp[Abbr `output`] >> disch_then (fn th => rewrite_tac[th]) >>
  fs[abi_vyper_admissible_replicate, EVERY_APPEND] >>
  `value_has_type tv v` by
    (drule sparse_has_type_all_have_type >>
     simp[all_have_type_EVERY] >> strip_tac >>
     imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM, MEM_MAP] >> metis_tac[SND]) >>
  metis_tac[]
QED

Theorem abi_coherent_typed_conversion_admissible:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  !v av. value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
    abi_vyper_admissible env ty av
Proof
  ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp_tac bool_ss [Once vyper_to_abi_def] >>
      metis_tac[abi_base_typed_admissible])
  >- (rpt gen_tac >> strip_tac >> Cases_on `v` >>
      simp[value_has_type_def, Once vyper_to_abi_def] >>
      rpt strip_tac >> irule abiVyperAdmissibleTheory.flag >> simp[])
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume abi_coherent_typed_conversion_admissible[array]:
  rpt gen_tac >> strip_tac >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  Cases_on `v` >> simp[value_has_type_def, Once vyper_to_abi_def] >>
  rename1 `ArrayV ar` >> Cases_on `ar` >> Cases_on `bound` >>
  simp[value_has_type_def, Once vyper_to_abi_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), Excl "vyper_to_abi_def"]
  >- (drule_all abi_typed_conversion_same_admissible >> strip_tac >>
      irule abiVyperAdmissibleTheory.array >>
      simp[compatible_bound_def] >> metis_tac[]) >>
  drule canonical_sparse_length >> strip_tac >>
  `value_has_type tv (default_value tv)` by
    metis_tac[default_value_has_type_thm] >>
  `abi_vyper_admissible env ty (default_to_abi tv)` by
    metis_tac[cj 1 vyper_to_abi_default_value] >>
  drule_all abi_typed_conversion_sparse_admissible >> strip_tac >>
  irule abiVyperAdmissibleTheory.array >>
  simp[compatible_bound_def] >> metis_tac[]
QED
Resume abi_coherent_typed_conversion_admissible[tuple]:
  rpt gen_tac >> strip_tac >> Cases_on `v` >>
  simp[value_has_type_def, Once vyper_to_abi_def] >>
  rename1 `ArrayV ar` >> Cases_on `ar` >>
  simp[value_has_type_def, Once vyper_to_abi_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), Excl "vyper_to_abi_def"] >>
  irule abiVyperAdmissibleTheory.tuple >>
  irule abi_typed_conversion_list_admissible >>
  qexistsl_tac [`tvs`, `l`] >> simp[] >>
  gvs[LIST_REL_EL_EQN] >> metis_tac[]
QED
Resume abi_coherent_typed_conversion_admissible[struct]:
  rpt gen_tac >> strip_tac >> Cases_on `v` >>
  simp[value_has_type_def, Once vyper_to_abi_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), Excl "vyper_to_abi_def"] >>
  qmatch_asmsub_abbrev_tac `StructArgs args` >>
  `LENGTH args = LENGTH tvs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  drule struct_has_type_values_have_types >>
  simp[MAP_ZIP] >> strip_tac >>
  irule abiVyperAdmissibleTheory.struct_case >>
  qexists_tac `args` >> simp[] >>
  irule abi_typed_conversion_list_admissible >>
  qexistsl_tac [`tvs`, `MAP SND l`] >> simp[] >>
  gvs[LIST_REL_EL_EQN] >> metis_tac[]
QED
Finalise abi_coherent_typed_conversion_admissible

Theorem abi_static_types_inhabited[local]:
  !tys witness. ~any_dynamic (vyper_to_abi_types env tys) /\
    has_types (vyper_to_abi_types env tys) witness ==>
    EVERY (\ty. ~is_dynamic (vyper_to_abi_type env ty) /\
      ?a. has_type (vyper_to_abi_type env ty) a) tys
Proof
  Induct >> Cases_on `witness` >> simp[has_type_def] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem abi_static_admissible_has_type:
  (!env ty av. abi_vyper_admissible env ty av ==>
    ~is_dynamic (vyper_to_abi_type env ty) /\
    (?a. has_type (vyper_to_abi_type env ty) a) ==>
    has_type (vyper_to_abi_type env ty) av) /\
  (!env tys avs. abi_vyper_admissible_list env tys avs ==>
    EVERY (\ty. ~is_dynamic (vyper_to_abi_type env ty) /\
      ?a. has_type (vyper_to_abi_type env ty) a) tys ==>
    has_types (vyper_to_abi_types env tys) avs)
Proof
  ho_match_mp_tac abi_vyper_admissible_ind >> rpt conj_tac
  >- suspend "uint"
  >- suspend "int"
  >- suspend "address"
  >- (simp[has_type_def])
  >- suspend "bytes"
  >- (simp[has_type_def])
  >- suspend "decimal"
  >- suspend "tuple"
  >- suspend "array"
  >- (simp[has_type_def])
  >- suspend "struct"
  >- suspend "flag"
  >- (simp[has_type_def])
  >> (simp[has_type_def])
QED

Resume abi_static_admissible_has_type[uint]:
  rpt gen_tac >> strip_tac >> simp[] >> strip_tac >> Cases_on `a` >>
  gvs[has_type_def, within_int_bound_def]
QED
Resume abi_static_admissible_has_type[int]:
  rpt gen_tac >> strip_tac >> simp[] >> strip_tac >> Cases_on `a` >>
  gvs[has_type_def, within_int_bound_def, int_bits_bound_def] >>
  Cases_on `i < 0` >> gvs[PRE_SUB1] >> intLib.COOPER_TAC
QED
Resume abi_static_admissible_has_type[address]:
  simp[has_type_def, within_int_bound_def]
QED
Resume abi_static_admissible_has_type[bytes]:
  rpt gen_tac >> strip_tac >> Cases_on `b` >>
  simp[has_type_def, compatible_bound_def] >> strip_tac >>
  Cases_on `a` >> gvs[has_type_def, compatible_bound_def]
QED
Resume abi_static_admissible_has_type[decimal]:
  simp[has_type_def, within_int_bound_def, int_bits_bound_def,
    decimal_bound_def, valid_int_bound_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >> Cases_on `i < 0` >>
  gvs[PRE_SUB1] >> intLib.COOPER_TAC
QED
Resume abi_static_admissible_has_type[tuple]:
  rpt gen_tac >> strip_tac >> simp[] >> strip_tac >> Cases_on `a` >>
  gvs[has_type_def] >>
  drule_all abi_static_types_inhabited >> strip_tac >>
  `has_types (vyper_to_abi_types env tys) avs` by metis_tac[] >>
  imp_res_tac has_types_length >> simp[]
QED
Resume abi_static_admissible_has_type[struct]:
  rpt gen_tac >> strip_tac >> simp[] >> strip_tac >> Cases_on `a` >>
  gvs[has_type_def] >>
  drule_all abi_static_types_inhabited >> strip_tac >>
  `has_types (vyper_to_abi_types (env \\ nsid) (MAP SND fields)) avs` by metis_tac[] >>
  imp_res_tac has_types_length >> simp[]
QED
Resume abi_static_admissible_has_type[flag]:
  simp[has_type_def, valid_int_bound_def] >> rpt strip_tac >>
  `2 ** n <= 2 ** 256` by simp[] >>
  `k < 2 ** 256` by metis_tac[LESS_LESS_EQ_TRANS] >> fs[]
QED
Resume abi_static_admissible_has_type[array]:
  rpt gen_tac >> strip_tac >> Cases_on `b` >>
  simp[has_type_def] >> strip_tac >> Cases_on `a` >>
  gvs[has_type_def, compatible_bound_def, vyper_to_abi_types_REPLICATE] >>
  Cases_on `avs` >- gvs[has_type_def] >>
  Cases_on `l` >> gvs[has_type_def] >> metis_tac[]
QED
Finalise abi_static_admissible_has_type

Theorem abi_unclamped_static_window_reflected:
  abi_decoder_coherent ce env sf ty tv /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  (?a. has_type (vyper_to_abi_type env ty) a) /\
  LENGTH bs = static_length (vyper_to_abi_type env ty) /\
  LENGTH bs < dimword (:256) ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
  abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs)
Proof
  strip_tac >>
  drule_all abi_unclamped_static_encoding_witness >> strip_tac >>
  `abi_vyper_admissible env ty av` by
    metis_tac[abi_coherent_typed_conversion_admissible] >>
  `~is_dynamic (vyper_to_abi_type env ty)` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `has_type (vyper_to_abi_type env ty) av` by
    metis_tac[cj 1 abi_static_admissible_has_type] >>
  gvs[] >> irule abi_typed_encoding_reflected >> simp[]
QED
