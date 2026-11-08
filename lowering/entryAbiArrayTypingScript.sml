Theory entryAbiArrayTyping
Ancestors
  entryAbiSourceSparseTyping entryAbiTupleTyping entryHereditarySlotCardinality
  entryDecodeProps entryConversionPositive alist pair vyperABI vyperABIRoundtrip vyperTypeABI vyperTypeSystem
  vyperTyping vyperValue contractABI valueEncodingProofs list rich_list words arithmetic

Theorem entry_array_abi_conversion_typed:
  (!tv v av. evaluate_type env ty = SOME tv /\ value_has_type tv v /\
     abi_decode_bytes_widths env ty /\
     entry_tuple_cardinality (vyper_to_abi_type env ty) /\
     vyper_to_abi env ty v = SOME av ==>
     has_type (vyper_to_abi_type env ty) av) /\
  assignable_type env (ArrayT ty bd) /\
  evaluate_type env (ArrayT ty bd) = SOME tv /\ value_has_type tv v /\
  abi_decode_bytes_widths env (ArrayT ty bd) /\
  entry_tuple_cardinality (vyper_to_abi_type env (ArrayT ty bd)) /\
  vyper_to_abi env (ArrayT ty bd) v = SOME av ==>
  has_type (vyper_to_abi_type env (ArrayT ty bd)) av
Proof
  strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `bound_length bd < dimword (:256)` by
    (Cases_on `bd` >>
     gvs[type_slot_size_def, vyperASTTheory.bound_length_def] >>
     `n <= n * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >>
     decide_tac) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  Cases_on `a` >> gvs[value_has_type_def] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
  Cases_on `bd` >>
  gvs[value_has_type_def, vyper_to_abi_type_def,
      abi_decode_bytes_widths_def, entry_tuple_cardinality_array]
  >- (gvs[vyper_to_abi_same_OPT_MMAP] >>
      drule OPT_MMAP_LENGTH >> strip_tac >>
      drule OPT_MMAP_LIST_REL >>
      gvs[LIST_REL_EL_EQN, all_have_type_EVERY, EVERY_EL,
          has_types_LIST_REL, EL_REPLICATE] >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  gvs[AllCaseEqs()] >>
  `!i v. i < n /\ ALOOKUP l i = SOME v ==> value_has_type tv' v` by
    (drule sparse_has_type_all_have_type >>
     simp[all_have_type_EVERY, EVERY_MEM, MEM_MAP] >>
     metis_tac[ALOOKUP_MEM, SND]) >>
  drule_all source_sparse_conversion_abi_typed >> strip_tac >>
  drule sparse_conversion_length >> strip_tac >>
  gvs[has_types_LIST_REL, LIST_REL_EL_EQN, EVERY_EL, EL_REPLICATE]
QED
