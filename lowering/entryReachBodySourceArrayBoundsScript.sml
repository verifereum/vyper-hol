Theory entryReachBodySourceArrayBounds
Ancestors
  entryReachBodySourceEncodingPositive entryReachBodySourceLayout
  entryReachBodyEncodingSizes entryReachBodyConversionSupport
  abiEncoderSourceTransport abiEncoderOpenInput abiDecoderMembers
  vyperTyping vyperABI vyperABIRoundtrip vyperTypeDefaults vyperValue
  vyperValueOperation valueEncodingProofs
  contractABI list rich_list arithmetic pair alist supportedTypes byte words

Theorem source_same_positive[local]:
  entry_abi_support env ty /\ evaluate_type env ty = SOME tv /\
  0 < type_slot_size tv /\ all_have_type tv xs /\
  vyper_to_abi_same env ty xs = SOME avs ==>
  !i. i < LENGTH avs ==>
    0 < LENGTH (enc (vyper_to_abi_type env ty) (EL i avs))
Proof
  strip_tac >> drule abi_encoder_same_conversion >> strip_tac >>
  gvs[all_have_type_EVERY, EVERY_EL, Excl "enc_def"] >>
  rpt strip_tac >> irule entry_source_encoding_positive >> metis_tac[]
QED

Theorem source_sparse_positive[local]:
  entry_abi_support env ty /\ evaluate_type env ty = SOME tv /\
  0 < type_slot_size tv /\
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  vyper_to_abi_sparse env ty tv n kvs = SOME avs ==>
  LENGTH avs = n /\ !i. i < n ==>
    0 < LENGTH (enc (vyper_to_abi_type env ty) (EL i avs))
Proof
  strip_tac >> drule_all abi_encoder_sparse_conversion >> strip_tac >>
  simp[Excl "enc_def"] >> rpt strip_tac >>
  irule entry_source_encoding_positive >> simp[Excl "enc_def"] >>
  qexists `EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs))` >>
  simp[Excl "enc_def"] >>
  gvs[array_elements_def, Excl "enc_def"] >>
  Cases_on `ALOOKUP kvs i` >> gvs[Excl "enc_def"]
  >- metis_tac[default_value_has_type_thm] >>
  gvs[value_has_type_def, Excl "enc_def"] >>
  metis_tac[sparse_has_type_lookup]
QED

Theorem entry_source_array_encoding_cardinality:
  entry_abi_support env (ArrayT ty bd) /\
  evaluate_type env (ArrayT ty bd) = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env (ArrayT ty bd) v = SOME (ListV avs) ==>
  LENGTH avs <= LENGTH (enc (vyper_to_abi_type env (ArrayT ty bd)) (ListV avs))
Proof
  strip_tac >>
  `abi_encoder_layout_valid (vyper_to_abi_type env (ArrayT ty bd)) (ListV avs)` by
    metis_tac[entry_source_conversion_layout] >>
  Cases_on `bd` >>
  gvs[Once entry_abi_support_cases, supported_scalar_type_def,
      supported_word_type_def, supported_string_type_def,
      Once evaluate_type_def, AllCaseEqs(), Excl "enc_def"] >>
  Cases_on `v` >> gvs[Once value_has_type_def, Excl "enc_def"] >>
  Cases_on `a` >> gvs[Once value_has_type_def, AllCaseEqs(), Excl "enc_def"]
  >- (`value_has_type (ArrayTV tv' (Fixed n)) (ArrayV (SArrayV l))` by
        simp[value_has_type_def] >>
      drule_all source_sparse_positive >> strip_tac >>
      `LENGTH avs <= LENGTH (enc (Tuple (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty))) (ListV avs))` by
        (irule entry_tuple_encoding_cardinality >> simp[EL_REPLICATE, Excl "enc_def"]) >>
      qpat_x_assum `LENGTH avs <= _` mp_tac >>
      simp[Once enc_def] >> simp[Once enc_def]) >>
  `!i. i < LENGTH avs ==> 0 < LENGTH (enc (vyper_to_abi_type env ty) (EL i avs))` by
    metis_tac[source_same_positive] >>
  `LENGTH avs <= LENGTH (enc (Tuple (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty))) (ListV avs))` by
    (irule entry_tuple_encoding_cardinality >> simp[EL_REPLICATE, Excl "enc_def"]) >>
  `LIST_REL abi_encoder_layout_valid
    (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) avs` by
    (drule abi_encoder_same_conversion >> strip_tac >>
     simp[LIST_REL_EL_EQN, EL_REPLICATE, Excl "enc_def"] >> rpt strip_tac >>
     irule entry_source_conversion_layout >>
     gvs[all_have_type_EVERY, EVERY_EL, Excl "enc_def"] >> metis_tac[]) >>
  drule abi_encoder_open_enc_tuple_length >>
  disch_then (qspecl_then [`head_lengths (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) 0`,
    `0`, `[word_to_bytes (n2w (LENGTH avs) : bytes32) T]`, `[]`] assume_tac) >>
  qpat_x_assum `LENGTH avs <= _` mp_tac >>
  simp[abi_encoder_open_tuple_length, Excl "enc_def"] >>
  simp[Once enc_def, LENGTH_word_to_bytes]
QED

Theorem entry_source_array_count_word_bound:
  entry_abi_support env (ArrayT ty bd) /\
  evaluate_type env (ArrayT ty bd) = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env (ArrayT ty bd) v = SOME (ListV avs) /\
  sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty bd)) (ListV avs)) < dimword (:256) ==>
  LENGTH avs < dimword (:256)
Proof
  strip_tac >> drule_all entry_source_array_encoding_cardinality >> decide_tac
QED

Theorem entry_source_dynamic_array_alignment:
  evaluate_type env (ArrayT ty (Dynamic maxn)) = SOME tv /\
  value_has_type tv (ArrayV (DynArrayV xs)) /\
  vyper_to_abi env (ArrayT ty (Dynamic maxn)) (ArrayV (DynArrayV xs)) = SOME (ListV avs) ==>
  LENGTH xs = LENGTH avs /\ LENGTH xs <= maxn
Proof
  simp[Once evaluate_type_def, AllCaseEqs(), Excl "enc_def"] >>
  rpt strip_tac >> gvs[value_has_type_def, AllCaseEqs(), Excl "enc_def"] >>
  drule abi_encoder_same_conversion >> simp[Excl "enc_def"]
QED
