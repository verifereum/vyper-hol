Theory ctorDeployMemoryRunMemEntrySparse
Ancestors
  vyperValue vyperTyping vyperABI abiStaticSparseProps sorting alist

Theorem ctor_canonical_sparse_absent:
  !n sparse avs k.
    vyper_to_abi_sparse env ty tv n sparse = SOME avs /\
    k < n /\ ALOOKUP sparse k = NONE ==>
    EL k avs = default_to_abi tv
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[Once vyper_to_abi_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac canonical_sparse_length >>
  Cases_on `k = n` >> gvs[listTheory.EL_APPEND_EQN] >>
  gvs[listTheory.EL_APPEND_EQN] >> first_x_assum irule >>
  simp[] >> qexists_tac `sparse` >> simp[]
QED

Theorem ctor_enumerate_sorted[local]:
  !dense n. SORTED $< (MAP FST (enumerate_static_array d n dense))
Proof
  Induct >> simp[enumerate_static_array_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[sortingTheory.SORTED_EQ, listTheory.EVERY_MAP,
    listTheory.EVERY_MEM, MEM_enumerate_static_array_iff] >>
  rpt strip_tac >> gvs[listTheory.MEM_MAP, MEM_enumerate_static_array_iff] >>
  PairCases_on `y'` >> gvs[MEM_enumerate_static_array_iff] >> decide_tac
QED

Theorem ctor_lookup_lower_bound[local]:
  (!y. MEM y (MAP FST xs) ==> n < y) /\
  ALOOKUP (xs : (num # 'a) list) k = SOME v ==> n < k
Proof
  strip_tac >> drule alistTheory.ALOOKUP_MEM >> strip_tac >>
  first_x_assum irule >> simp[listTheory.MEM_MAP] >>
  qexists_tac `(k,v)` >> simp[]
QED

Theorem ctor_sorted_lookup_ext[local]:
  !xs ys : (num # 'a) list.
    SORTED $< (MAP FST xs) /\ SORTED $< (MAP FST ys) /\
    (!k. ALOOKUP xs k = ALOOKUP ys k) ==> xs = ys
Proof
  Induct >- (Cases >> simp[] >> PairCases_on `h` >>
    simp[] >> disj2_tac >> qexists_tac `h0` >> simp[]) >>
  gen_tac >> PairCases_on `h` >> Cases >> simp[] >-
    (disj2_tac >> qexists_tac `h0` >> simp[]) >>
  PairCases_on `h` >> simp[sortingTheory.SORTED_EQ] >>
  strip_tac >>
  `h0 = h0'` by
    (Cases_on `h0 = h0'` >> simp[] >>
     qpat_assum `!k. _ = _` (qspec_then `h0` mp_tac) >>
     qpat_x_assum `!k. _ = _` (qspec_then `h0'` mp_tac) >>
     simp[] >> rpt strip_tac >>
     metis_tac[ctor_lookup_lower_bound, arithmeticTheory.LESS_ANTISYM]) >>
  gvs[] >> conj_tac
  >- (qpat_x_assum `!k. _ = _` (qspec_then `h0` mp_tac) >> simp[]) >>
  first_x_assum irule >> simp[] >> gen_tac >>
  Cases_on `k = h0`
  >- (gvs[] >> Cases_on `ALOOKUP xs h0` >>
      Cases_on `ALOOKUP t h0` >> gvs[] >>
      metis_tac[ctor_lookup_lower_bound, prim_recTheory.LESS_REFL]) >>
  qpat_x_assum `!k. _ = _` (qspec_then `k` mp_tac) >> simp[]
QED

Theorem ctor_enumerate_sparse_reconstruct:
  SORTED $< (MAP FST sparse) /\
  EVERY (\(k,v). k < LENGTH dense /\ v <> d) sparse /\
  (!k. k < LENGTH dense ==>
    EL k dense = case ALOOKUP sparse k of NONE => d | SOME v => v) ==>
  enumerate_static_array d 0 dense = sparse
Proof
  strip_tac >> irule ctor_sorted_lookup_ext >>
  simp[ctor_enumerate_sorted] >> gen_tac >>
  Cases_on `k < LENGTH dense`
  >- (qspec_then `d` mp_tac enumerate_static_array_ALOOKUP >>
      disch_then (qspecl_then [`0`, `dense`, `k`] mp_tac) >>
      simp[] >> disch_then SUBST1_TAC >>
      first_x_assum drule >>
      Cases_on `ALOOKUP sparse k` >> simp[] >> strip_tac >> gvs[] >>
      drule alistTheory.ALOOKUP_MEM >>
      strip_tac >> gvs[listTheory.EVERY_MEM] >>
      first_x_assum drule >> simp[]) >>
  Cases_on `ALOOKUP sparse k`
  >- (Cases_on `ALOOKUP (enumerate_static_array d 0 dense) k` >> simp[] >>
      drule alistTheory.ALOOKUP_MEM >>
      simp[MEM_enumerate_static_array_iff]) >>
  drule alistTheory.ALOOKUP_MEM >>
  strip_tac >> gvs[listTheory.EVERY_MEM] >> first_x_assum drule >> simp[]
QED
