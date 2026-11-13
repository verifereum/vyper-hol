Theory entryReachBodySourceLayout
Ancestors
  entryReachBodyConversionSupport entryReachBodyScalarConversion
  abiEncoderOpenInput abiDecodeRanges vyperTyping vyperABI contractABI list rich_list
  vyperTypeDefaults vyperABIRoundtrip vyperValue vyperTypeABI abiDecoderMembers finite_map alist pair

Theorem entry_list_layout_lift[local]:
  !tys tvs vs avs.
  LIST_REL (\ty tv. !v av.
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
    abi_encoder_layout_valid (vyper_to_abi_type env ty) av) tys tvs /\
  values_have_types tvs vs /\ vyper_to_abi_list env tys vs = SOME avs ==>
  LIST_REL abi_encoder_layout_valid (MAP (vyper_to_abi_type env) tys) avs
Proof
  Induct_on `tys`
  >- (Cases_on `vs` >> simp[vyper_to_abi_def]) >>
  Cases_on `tvs` >> Cases_on `vs` >>
  simp[value_has_type_def, vyper_to_abi_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem entry_sparse_layout_lift[local]:
  !n avs.
  (!k v av. k < n /\ ALOOKUP sparse k = SOME v /\
    vyper_to_abi env ty v = SOME av ==>
    abi_encoder_layout_valid (vyper_to_abi_type env ty) av) /\
  abi_encoder_layout_valid (vyper_to_abi_type env ty) (default_to_abi tv) /\
  vyper_to_abi_sparse env ty tv n sparse = SOME avs ==>
  LENGTH avs = n /\ EVERY (abi_encoder_layout_valid (vyper_to_abi_type env ty)) avs
Proof
  Induct_on `n` >> simp[Once vyper_to_abi_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  `LENGTH avs' = n /\ EVERY (abi_encoder_layout_valid (vyper_to_abi_type env ty)) avs'` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     `k < SUC n` by simp[] >> metis_tac[]) >>
  simp[EVERY_APPEND] >> `n < SUC n` by simp[] >> metis_tac[]
QED

Theorem entry_static_layout_tuple_length[local]:
  LIST_REL abi_encoder_layout_valid ts avs /\ ~any_dynamic ts ==>
  LENGTH (enc_tuple hl tl ts avs [] []) = static_length (Tuple ts)
Proof
  strip_tac >>
  `LENGTH ts = LENGTH avs` by metis_tac[LIST_REL_LENGTH] >>
  drule_all abi_encoder_open_static_tuple_size >>
  drule abi_encoder_open_enc_tuple_length >>
  disch_then (qspecl_then [`hl`, `tl`, `[]`, `[]`] mp_tac) >> simp[]
QED

Theorem entry_source_conversion_layout:
  !env ty. entry_abi_support env ty ==>
  !tv v av. evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av ==>
    abi_encoder_layout_valid (vyper_to_abi_type env ty) av
Proof
  ho_match_mp_tac entry_abi_support_ind >> rpt strip_tac
  >- (simp[abi_encoder_layout_valid_def] >> strip_tac >>
      irule (cj 1 enc_has_static_length) >>
      metis_tac[entry_scalar_conversion_typed])
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume entry_source_conversion_layout[array]:
  Cases_on `bd`
  >~ [`Fixed n`] >-
    (gvs[Once evaluate_type_def, AllCaseEqs()] >>
     Cases_on `v` >> gvs[Once value_has_type_def] >>
     Cases_on `a` >> gvs[Once value_has_type_def] >>
     gvs[AllCaseEqs()] >>
     `abi_encoder_layout_valid (vyper_to_abi_type env ty) (default_to_abi tv')` by
       metis_tac[default_value_has_type_thm, vyper_to_abi_default_value] >>
     `!k v av. k < n /\ ALOOKUP l k = SOME v /\
       vyper_to_abi env ty v = SOME av ==>
       abi_encoder_layout_valid (vyper_to_abi_type env ty) av` by
       (rpt strip_tac >> first_x_assum irule >> simp[] >>
        drule sparse_has_type_all_have_type >>
        simp[all_have_type_EVERY, EVERY_MAP, EVERY_MEM] >>
        metis_tac[ALOOKUP_MEM, SND]) >>
     drule_all entry_sparse_layout_lift >> strip_tac >>
     simp[abi_encoder_layout_valid_def] >> strip_tac >>
     `LIST_REL abi_encoder_layout_valid
       (REPLICATE n (vyper_to_abi_type env ty)) avs` by
       (gvs[EVERY_EL] >> simp[LIST_REL_EL_EQN, EL_REPLICATE]) >>
     rewrite_tac[GSYM abi_encoder_open_replicate_static] >>
     irule entry_static_layout_tuple_length >>
     simp[abi_encoder_open_replicate_dynamic]) >>
  simp[Once vyper_to_abi_type_def, abi_encoder_layout_valid_def, is_dynamic_def]
QED

Resume entry_source_conversion_layout[tuple]:
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[Once value_has_type_def] >>
  Cases_on `a` >> gvs[Once value_has_type_def, AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `LIST_REL (\ty tv. !v av. value_has_type tv v /\
     vyper_to_abi env ty v = SOME av ==>
     abi_encoder_layout_valid (vyper_to_abi_type env ty) av) ts tvs` by
    (gvs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  drule_all entry_list_layout_lift >> strip_tac >>
  simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
       abi_encoder_layout_valid_def] >> strip_tac >>
  irule entry_static_layout_tuple_length >> simp[]
QED

Resume entry_source_conversion_layout[struct]:
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[Once value_has_type_def, AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `LENGTH (MAP FST fields) = LENGTH tvs` by
    (drule LIST_REL_LENGTH >> simp[]) >>
  `values_have_types tvs (MAP SND l)` by
    (drule struct_has_type_values_have_types >> simp[MAP_ZIP]) >>
  `LIST_REL (\ty tv. !v av. value_has_type tv v /\
     vyper_to_abi (env \\ id) ty v = SOME av ==>
     abi_encoder_layout_valid (vyper_to_abi_type (env \\ id) ty) av)
     (MAP SND fields) tvs` by
    (gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >> metis_tac[]) >>
  drule_all entry_list_layout_lift >> strip_tac >>
  simp[vyper_to_abi_types_MAP, abi_encoder_layout_valid_def] >> strip_tac >>
  irule entry_static_layout_tuple_length >> simp[]
QED

Finalise entry_source_conversion_layout

Theorem entry_source_list_conversion_layout:
  !tys vs avs.
  EVERY (entry_abi_support env) tys /\
  LIST_REL (\ty v. ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys vs /\
  vyper_to_abi_list env tys vs = SOME avs ==>
  LIST_REL abi_encoder_layout_valid (MAP (vyper_to_abi_type env) tys) avs
Proof
  Induct_on `tys` >> Cases_on `vs` >>
  simp[vyper_to_abi_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> conj_tac
  >- (irule entry_source_conversion_layout >>
      goal_assum (drule_at Any) >> simp[] >> qexists_tac `h` >> simp[]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED
