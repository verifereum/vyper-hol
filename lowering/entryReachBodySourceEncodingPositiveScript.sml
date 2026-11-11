Theory entryReachBodySourceEncodingPositive
Ancestors
  entryReachBodySourceLayout entryReachBodyEncodingSizes
  entryReachBodyConversionSupport entryReachBodyScalarConversion
  vyperTyping vyperABI vyperABIRoundtrip vyperTypeDefaults valueEncoding vyperValue
  contractABI list rich_list arithmetic pair alist supportedTypes byte words abiEncoderOpenInput
  abiDecoderMembers vyperTypeABI finite_map vyperStorageRegionWrite

Theorem source_list_encoding_positive[local]:
  !tys tvs vs avs.
  LIST_REL (\ty tv. !v av. value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\ 0 < type_slot_size tv ==>
    0 < LENGTH (enc (vyper_to_abi_type env ty) av)) tys tvs /\
  values_have_types tvs vs /\ vyper_to_abi_list env tys vs = SOME avs ==>
  LENGTH tys = LENGTH avs /\
  (0 < SUM (MAP type_slot_size tvs) ==>
   0 < LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
Proof
  Induct_on `tys` >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[value_has_type_def, vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"] >>
  rpt strip_tac >> gvs[Excl "enc_def"] >>
  first_x_assum drule_all >> strip_tac >>
  simp[entry_tuple_encoding_length, Excl "enc_def"] >>
  Cases_on `0 < type_slot_size h`
  >- (`0 < LENGTH (enc (vyper_to_abi_type env h'') av)` by metis_tac[] >> decide_tac) >>
  `0 < SUM (MAP type_slot_size t)` by decide_tac >>
  qpat_x_assum `0 < SUM _ ==> _` drule >>
  simp[entry_tuple_encoding_length, Excl "enc_def"] >> decide_tac
QED

Theorem source_sparse_encoding_positive[local]:
  !n avs.
  (!k v av. k < n /\ ALOOKUP sparse k = SOME v /\
    vyper_to_abi env ty v = SOME av ==>
    0 < LENGTH (enc (vyper_to_abi_type env ty) av)) /\
  0 < LENGTH (enc (vyper_to_abi_type env ty) (default_to_abi tv)) /\
  vyper_to_abi_sparse env ty tv n sparse = SOME avs ==>
  LENGTH avs = n /\ EVERY (\av. 0 < LENGTH (enc (vyper_to_abi_type env ty) av)) avs
Proof
  Induct_on `n` >> simp[Once vyper_to_abi_def, Excl "enc_def"] >>
  rpt strip_tac >> gvs[AllCaseEqs(), Excl "enc_def"] >>
  `LENGTH avs' = n /\ EVERY (\av. 0 < LENGTH (enc (vyper_to_abi_type env ty) av)) avs'` by
    (first_x_assum irule >> simp[Excl "enc_def"] >> rpt strip_tac >>
     `k < SUC n` by simp[] >> metis_tac[]) >>
  simp[EVERY_APPEND, Excl "enc_def"] >> `n < SUC n` by simp[] >> metis_tac[]
QED

Theorem source_same_layout[local]:
  !xs avs. entry_abi_support env ty /\ evaluate_type env ty = SOME tv /\
  all_have_type tv xs /\ vyper_to_abi_same env ty xs = SOME avs ==>
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) avs
Proof
  Induct >> Cases_on `avs` >>
  simp[vyper_to_abi_def, all_have_type_EVERY, AllCaseEqs(), Excl "enc_def"] >>
  rpt strip_tac >> gvs[Excl "enc_def"] >>
  metis_tac[entry_source_conversion_layout]
QED

Theorem entry_source_encoding_positive:
  !env ty. entry_abi_support env ty ==>
  !tv v av. evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\ 0 < type_slot_size tv ==>
    0 < LENGTH (enc (vyper_to_abi_type env ty) av)
Proof
  ho_match_mp_tac entry_abi_support_strongind >> rpt strip_tac
  >- suspend "scalar"
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume entry_source_encoding_positive[scalar]:
  drule_all entry_scalar_conversion_typed >>
  Cases_on `ty` >> gvs[supported_scalar_type_def, supported_word_type_def,
    supported_string_type_def] >>
  Cases_on `b` >> Cases_on `av` >>
  gvs[vyper_base_to_abi_type_def, has_type_def, enc_def,
    LENGTH_word_to_bytes, supported_word_type_def, supported_string_type_def,
    AllCaseEqs()] >>
  Cases_on `b'` >>
  gvs[vyper_base_to_abi_type_def, has_type_def, enc_def,
    supported_word_type_def, supported_string_type_def, evaluate_type_def,
    value_has_type_def, compatible_bound_def] >>
  strip_tac >> `LENGTH (TAKE 32 l) = n` by simp[TAKE_LENGTH_TOO_LONG] >> decide_tac
QED
Resume entry_source_encoding_positive[array]:
  Cases_on `bd`
  >~ [`Dynamic maxn`] >-
    (gvs[Once evaluate_type_def, AllCaseEqs(), Excl "enc_def"] >>
     Cases_on `v` >> gvs[Once value_has_type_def, Excl "enc_def"] >>
     Cases_on `a` >> gvs[Once value_has_type_def, AllCaseEqs(), Excl "enc_def"] >>
     drule_all source_same_layout >> strip_tac >>
     simp[Once vyper_to_abi_type_def, Once enc_def] >>
     drule abi_encoder_open_enc_tuple_length >>
     disch_then (qspecl_then [`head_lengths (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) 0`,
       `0`, `[word_to_bytes (n2w (LENGTH avs) : bytes32) T]`, `[]`] mp_tac) >>
     simp[LENGTH_word_to_bytes]) >>
  gvs[Once evaluate_type_def, AllCaseEqs(), Excl "enc_def"] >>
  Cases_on `v` >> gvs[Once value_has_type_def, Excl "enc_def"] >>
  Cases_on `a` >> gvs[Once value_has_type_def, AllCaseEqs(), Excl "enc_def"] >>
  `0 < LENGTH (enc (vyper_to_abi_type env ty) (default_to_abi tv'))` by
    metis_tac[default_value_has_type_thm, vyper_to_abi_default_value] >>
  `!k v av. k < n /\ ALOOKUP l k = SOME v /\ vyper_to_abi env ty v = SOME av ==>
    0 < LENGTH (enc (vyper_to_abi_type env ty) av)` by
    (rpt strip_tac >> first_x_assum irule >> simp[Excl "enc_def"] >>
     drule sparse_has_type_all_have_type >>
     simp[all_have_type_EVERY, EVERY_MAP, EVERY_MEM, Excl "enc_def"] >>
     metis_tac[ALOOKUP_MEM, SND]) >>
  drule_all source_sparse_encoding_positive >> strip_tac >>
  `LENGTH avs <= LENGTH (enc (Tuple (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty))) (ListV avs))` by
    (irule entry_tuple_encoding_cardinality >>
     gvs[EVERY_EL, Excl "enc_def"] >> simp[EL_REPLICATE, Excl "enc_def"]) >>
  qpat_x_assum `LENGTH avs <= _` mp_tac >>
  simp[Once enc_def] >> simp[Once enc_def]
QED
Resume entry_source_encoding_positive[tuple]:
  gvs[Once evaluate_type_def, AllCaseEqs(), Excl "enc_def"] >>
  Cases_on `v` >> gvs[Once value_has_type_def, Excl "enc_def"] >>
  Cases_on `a` >> gvs[Once value_has_type_def, AllCaseEqs(), Excl "enc_def"] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `LIST_REL (\ty tv. !v av. value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\ 0 < type_slot_size tv ==>
    0 < LENGTH (enc (vyper_to_abi_type env ty) av)) ts tvs` by
    (gvs[LIST_REL_EL_EQN, EVERY_EL, Excl "enc_def"] >> metis_tac[]) >>
  drule_all source_list_encoding_positive >> strip_tac >>
  gvs[type_slot_size_def, type_slot_size_list_sum, Once vyper_to_abi_type_def,
      vyper_to_abi_types_MAP, Excl "enc_def"]
QED
Resume entry_source_encoding_positive[struct]:
  gvs[Once evaluate_type_def, AllCaseEqs(), Excl "enc_def"] >>
  Cases_on `v` >> gvs[Once value_has_type_def, AllCaseEqs(), Excl "enc_def"] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `LENGTH (MAP FST fields) = LENGTH tvs` by
    (drule LIST_REL_LENGTH >> simp[]) >>
  `values_have_types tvs (MAP SND l)` by
    (drule struct_has_type_values_have_types >> simp[MAP_ZIP]) >>
  `LIST_REL (\ty tv. !v av. value_has_type tv v /\
    vyper_to_abi (env \\ id) ty v = SOME av /\ 0 < type_slot_size tv ==>
    0 < LENGTH (enc (vyper_to_abi_type (env \\ id) ty) av))
      (MAP SND fields) tvs` by
    (gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP, Excl "enc_def"] >> metis_tac[]) >>
  drule_all source_list_encoding_positive >> strip_tac >>
  gvs[type_slot_size_def, type_slot_size_fields_list, type_slot_size_list_sum,
      MAP_ZIP, vyper_to_abi_types_MAP, Excl "enc_def"]
QED
Finalise entry_source_encoding_positive
