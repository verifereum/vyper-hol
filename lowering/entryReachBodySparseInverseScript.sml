Theory entryReachBodySparseInverse
Ancestors
  entryReachBodyListInverse entryReachBodySortedLookup vyperTyping
  vyperTypeABI vyperABI vyperValue alist pair list rich_list option arithmetic

Theorem entry_inverse_list_snoc[local]:
  !ts avs vs ty av v.
    abi_to_vyper_list env ts avs = SOME vs /\
    abi_to_vyper env ty av = SOME v ==>
    abi_to_vyper_list env (ts ++ [ty]) (avs ++ [av]) = SOME (vs ++ [v])
Proof
  Induct_on `ts` >> Cases_on `avs` >>
  simp[Once abi_to_vyper_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[Once abi_to_vyper_def] >>
  first_x_assum drule >> disch_then drule >> simp[]
QED

Theorem entry_sparse_dense_inverse[local]:
  !n avs.
    abi_to_vyper env ty (default_to_abi tv) = SOME (default_value tv) /\
    (!k v av. k < n /\ ALOOKUP sparse k = SOME v /\
      vyper_to_abi env ty v = SOME av ==>
      abi_to_vyper env ty av = SOME v) /\
    vyper_to_abi_sparse env ty tv n sparse = SOME avs ==>
    LENGTH avs = n /\
    abi_to_vyper_list env (REPLICATE n ty) avs =
      SOME (GENLIST (\k. case ALOOKUP sparse k of
        NONE => default_value tv | SOME v => v) n)
Proof
  Induct_on `n` >> simp[Once vyper_to_abi_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `(_ ==> _ /\ _)` mp_tac >>
  (impl_tac >- (rpt strip_tac >> `k < SUC n` by simp[] >> metis_tac[])) >>
  strip_tac >> simp[] >>
  simp[GENLIST, SNOC_APPEND] >>
  rewrite_tac[GSYM REPLICATE, GSYM SNOC_REPLICATE, SNOC_APPEND] >>
  pure_rewrite_tac[CONJUNCT1 REPLICATE] >>
  irule entry_inverse_list_snoc >> simp[] >>
  `n < SUC n` by simp[] >> metis_tac[]
QED

Theorem entry_sparse_reconstruct[local]:
  SORTED $< (MAP FST sparse) /\ sparse_has_type tv n sparse ==>
  enumerate_static_array (default_value tv) 0
    (GENLIST (\k. case ALOOKUP sparse k of
       NONE => default_value tv | SOME v => v) n) = sparse
Proof
  strip_tac >> irule entry_sorted_lookup_unique >>
  simp[enumerate_static_array_sorted] >> gen_tac >>
  Cases_on `k < n`
  >- (qspec_then `default_value tv` mp_tac enumerate_static_array_ALOOKUP >>
      disch_then (qspecl_then [`0`, `GENLIST (\k. case ALOOKUP sparse k of
        NONE => default_value tv | SOME v => v) n`, `k`] mp_tac) >>
      simp[EL_GENLIST] >> Cases_on `ALOOKUP sparse k` >> simp[] >>
      drule ALOOKUP_MEM >>
      drule sparse_has_type_not_default >>
      simp[EVERY_MAP, EVERY_MEM] >> metis_tac[SND]) >>
  `ALOOKUP sparse k = NONE` by
    (Cases_on `ALOOKUP sparse k` >> simp[] >> drule ALOOKUP_MEM >>
     drule sparse_has_type_all_less >> simp[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  simp[ALOOKUP_FAILS, MEM_MAP, EXISTS_PROD, MEM_enumerate_static_array_iff]
QED

Theorem entry_sparse_conversion_inverse:
  evaluate_type env ty = SOME tv /\
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV sparse)) /\
  abi_to_vyper env ty (default_to_abi tv) = SOME (default_value tv) /\
  (!k v av. k < n /\ ALOOKUP sparse k = SOME v /\
    vyper_to_abi env ty v = SOME av ==> abi_to_vyper env ty av = SOME v) /\
  vyper_to_abi_sparse env ty tv n sparse = SOME avs ==>
  abi_to_vyper env (ArrayT ty (Fixed n)) (ListV avs) =
    SOME (ArrayV (SArrayV sparse))
Proof
  rpt strip_tac >> drule_all entry_sparse_dense_inverse >> strip_tac >>
  gvs[Once value_has_type_def] >>
  drule_all entry_sparse_reconstruct >> strip_tac >>
  simp[Once abi_to_vyper_def, compatible_bound_def, make_array_value_def]
QED
