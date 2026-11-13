Theory entryReachBodySourceInverse
Ancestors
  entryReachBodyConversionSupport entryReachBodyScalarConversion
  entryReachBodyListInverse entryReachBodySparseInverse
  vyperTyping vyperABI vyperValue vyperTypeABI vyperTypeDefaults
  vyperABIRoundtrip list rich_list finite_map alist pair

Theorem entry_typed_list_inverse[local]:
  !tys tvs vs avs.
  LIST_REL (\ty tv. !v av. value_has_type tv v /\
    vyper_to_abi env ty v = SOME av ==> abi_to_vyper env ty av = SOME v) tys tvs /\
  values_have_types tvs vs /\ vyper_to_abi_list env tys vs = SOME avs ==>
  abi_to_vyper_list env tys avs = SOME vs
Proof
  Induct_on `tys`
  >- (Cases_on `vs` >> simp[vyper_to_abi_def, abi_to_vyper_def]) >>
  Cases_on `tvs` >> Cases_on `vs` >>
  simp[value_has_type_def, Once vyper_to_abi_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `abi_to_vyper_list env tys avs' = SOME t'` by metis_tac[] >>
  `abi_to_vyper env h'' av = SOME h'` by metis_tac[] >> simp[]
QED

Theorem entry_source_conversion_inverse:
  !env ty. entry_abi_support env ty ==>
  !tv v av. evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av ==> abi_to_vyper env ty av = SOME v
Proof
  ho_match_mp_tac entry_abi_support_ind >> rpt strip_tac
  >- metis_tac[entry_scalar_forward_inverse]
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume entry_source_conversion_inverse[array]:
  Cases_on `bd`
  >~ [`Fixed n`] >-
    (gvs[Once evaluate_type_def, AllCaseEqs()] >>
     Cases_on `v` >> gvs[Once value_has_type_def] >>
     Cases_on `a` >> gvs[Once value_has_type_def, AllCaseEqs()] >>
     `abi_to_vyper env (ArrayT ty (Fixed n)) (ListV avs) =
       SOME (ArrayV (SArrayV l))` suffices_by
       simp[Once abi_to_vyper_def, AllCaseEqs()] >>
     irule entry_sparse_conversion_inverse >>
     reverse conj_tac
     >- (qexists_tac `tv'` >> simp[Once value_has_type_def] >>
         metis_tac[default_value_has_type_thm, vyper_to_abi_default_value]) >>
     rpt strip_tac >> first_x_assum irule >> simp[] >>
     drule sparse_has_type_all_have_type >>
     simp[all_have_type_EVERY, EVERY_MAP, EVERY_MEM] >>
     metis_tac[ALOOKUP_MEM, SND]) >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[Once value_has_type_def] >>
  Cases_on `a` >> gvs[Once value_has_type_def, AllCaseEqs()] >>
  `EVERY (\v. !av. vyper_to_abi env ty v = SOME av ==>
     abi_to_vyper env ty av = SOME v) l` by
    (gvs[all_have_type_EVERY, EVERY_MEM] >> metis_tac[]) >>
  drule_all entry_same_conversion_inverse >>
  drule entry_same_conversion_length >>
  simp[compatible_bound_def, make_array_value_def]
QED

Resume entry_source_conversion_inverse[tuple]:
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[Once value_has_type_def] >>
  Cases_on `a` >> gvs[Once value_has_type_def, AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `LIST_REL (\ty tv. !v av. value_has_type tv v /\
     vyper_to_abi env ty v = SOME av ==> abi_to_vyper env ty av = SOME v)
     ts tvs` by (gvs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  metis_tac[entry_typed_list_inverse]
QED

Resume entry_source_conversion_inverse[struct]:
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[Once value_has_type_def, AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `LENGTH (MAP FST fields) = LENGTH tvs` by
    (drule LIST_REL_LENGTH >> simp[]) >>
  `values_have_types tvs (MAP SND l)` by
    (drule struct_has_type_values_have_types >> simp[MAP_ZIP]) >>
  `LIST_REL (\ty tv. !v av. value_has_type tv v /\
     vyper_to_abi (env \\ id) ty v = SOME av ==>
     abi_to_vyper (env \\ id) ty av = SOME v) (MAP SND fields) tvs` by
    (gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >> metis_tac[]) >>
  drule_all entry_typed_list_inverse >> strip_tac >>
  drule struct_has_type_map_fst >> simp[MAP_ZIP] >> strip_tac >>
  metis_tac[ZIP_UNZIP, UNZIP_MAP]
QED

Finalise entry_source_conversion_inverse

Theorem entry_source_list_conversion_inverse:
  !tys vs avs.
  EVERY (entry_abi_support env) tys /\
  LIST_REL (\ty v. ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys vs /\
  vyper_to_abi_list env tys vs = SOME avs ==>
  abi_to_vyper_list env tys avs = SOME vs
Proof
  rpt strip_tac >> irule entry_list_conversion_inverse >>
  goal_assum (drule_at Any) >>
  gvs[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
  irule entry_source_conversion_inverse >>
  goal_assum (drule_at Any) >> metis_tac[]
QED
