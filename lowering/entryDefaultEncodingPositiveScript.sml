Theory entryDefaultEncodingPositive
Ancestors
  entryEncodingPositive entryConversionPositive vyperABI vyperValue
  vyperTypeSystem contractABI byte list rich_list arithmetic

Theorem default_list_encoding_positive_members:
  !atys tvs.
    LIST_REL (\aty tv. 0 < LENGTH (enc aty (default_to_abi tv))) atys tvs ==>
    EVERY (\p. 0 < LENGTH (enc (FST p) (SND p)))
      (ZIP (atys,default_to_abi_list tvs))
Proof
  Induct >> Cases_on `tvs` >>
  simp[default_to_abi_list_MAP, Excl "enc_def"] >>
  rpt strip_tac >> first_x_assum (qspec_then `t` mp_tac) >>
  simp[default_to_abi_list_MAP, Excl "enc_def"]
QED

Theorem default_fields_encoding_positive_members:
  LIST_REL (\aty tv. 0 < LENGTH (enc aty (default_to_abi tv)))
    atys (MAP SND fields) ==>
  EVERY (\p. 0 < LENGTH (enc (FST p) (SND p)))
    (ZIP (atys,default_to_abi_fields fields))
Proof
  strip_tac >> drule default_list_encoding_positive_members >>
  simp[default_to_abi_fields_MAP, default_to_abi_list_MAP, MAP_MAP_o,
       Excl "enc_def"]
QED

Theorem default_tuple_encoding_positive:
  atys <> [] /\
  LIST_REL (\aty tv. 0 < LENGTH (enc aty (default_to_abi tv))) atys tvs ==>
  0 < LENGTH (enc (Tuple atys) (default_to_abi (TupleTV tvs)))
Proof
  strip_tac >> pure_rewrite_tac[default_to_abi_def] >>
  irule tuple_encoding_positive_member >>
  drule default_list_encoding_positive_members >>
  Cases_on `atys` >> Cases_on `tvs` >>
  gvs[default_to_abi_list_MAP, Excl "enc_def"] >>
  metis_tac[LIST_REL_LENGTH]
QED

Theorem default_fixed_array_encoding_positive:
  0 < n /\ 0 < LENGTH (enc aty (default_to_abi tv)) ==>
  0 < LENGTH (enc (Array (SOME n) aty) (default_to_abi (ArrayTV tv (Fixed n))))
Proof
  strip_tac >> pure_rewrite_tac[default_to_abi_def] >>
  irule fixed_array_encoding_positive >> simp[EVERY_REPLICATE]
QED

Theorem default_dynamic_array_encoding_positive:
  0 < LENGTH (enc (Array NONE aty) (default_to_abi (ArrayTV tv (Dynamic n))))
Proof
  pure_rewrite_tac[default_to_abi_def] >>
  irule dynamic_array_encoding_positive
QED

Theorem default_base_encoding_positive:
  assignable_type env (BaseT bt) /\
  evaluate_type env (BaseT bt) = SOME tv ==>
  0 < LENGTH (enc (vyper_to_abi_type env (BaseT bt)) (default_to_abi tv))
Proof
  Cases_on `bt` >>
  simp[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[default_to_abi_def, enc_def, enc_number_def, LENGTH_word_to_bytes] >>
  simp[TAKE_LENGTH_TOO_LONG]
QED

Theorem default_flag_encoding_positive:
  assignable_type env (FlagT nsid) /\
  evaluate_type env (FlagT nsid) = SOME tv ==>
  0 < LENGTH (enc (vyper_to_abi_type env (FlagT nsid)) (default_to_abi tv))
Proof
  simp[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[AllCaseEqs(), default_to_abi_def, enc_def, enc_number_def,
      LENGTH_word_to_bytes]
QED

Theorem default_struct_encoding_positive:
  atys <> [] /\
  LIST_REL (\aty tv. 0 < LENGTH (enc aty (default_to_abi tv)))
    atys (MAP SND fields) ==>
  0 < LENGTH (enc (Tuple atys) (default_to_abi (StructTV fields)))
Proof
  strip_tac >> pure_rewrite_tac[default_to_abi_def] >>
  `default_to_abi_fields fields = default_to_abi_list (MAP SND fields)` by
    simp[default_to_abi_fields_MAP, default_to_abi_list_MAP, MAP_MAP_o] >>
  simp[Excl "enc_def"] >>
  irule tuple_encoding_positive_member >>
  drule default_list_encoding_positive_members >>
  Cases_on `atys` >> Cases_on `MAP SND fields` >>
  gvs[default_to_abi_list_MAP, Excl "enc_def"] >>
  metis_tac[LIST_REL_LENGTH]
QED

Theorem sparse_fixed_encoding_positive:
  0 < n /\ vyper_to_abi_sparse env ty tv n sparse = SOME avs /\
  0 < LENGTH (enc aty (default_to_abi tv)) /\
  (!k v av. k < n /\ ALOOKUP sparse k = SOME v /\
    vyper_to_abi env ty v = SOME av ==> 0 < LENGTH (enc aty av)) ==>
  0 < LENGTH (enc (Array (SOME n) aty) (ListV avs))
Proof
  strip_tac >> irule fixed_array_encoding_positive >>
  conj_tac >- (drule sparse_conversion_length >> Cases_on `avs` >> simp[]) >>
  irule sparse_conversion_encoding_positive >> metis_tac[]
QED
