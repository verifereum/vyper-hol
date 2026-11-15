Theory dispatchedDecodeCast
Ancestors dispatchedDecodeDomain vyperCalldata vyperValueOperation vyperValue
  vyperTypeABI list rich_list sorting

Theorem cast_fixed_list[local]:
  !ts vs acc. LIST_REL (\t v. safe_cast t v = SOME v) ts vs ==>
  safe_cast_list ts vs acc = SOME (REVERSE acc ++ vs)
Proof
  Induct >> Cases_on `vs` >> simp[safe_cast_def] >>
  rpt strip_tac >> simp[safe_cast_def] >>
  first_x_assum irule >> simp[]
QED

Theorem cast_fixed_replicate[local]:
  !vs t. EVERY (\v. safe_cast t v = SOME v) vs ==>
  LIST_REL (\t v. safe_cast t v = SOME v) (REPLICATE (LENGTH vs) t) vs
Proof
  Induct >> simp[]
QED

Theorem cast_fixed_array[local]:
  LENGTH vs = n /\ EVERY (\v. safe_cast t v = SOME v) vs ==>
  safe_cast (ArrayTV t (Fixed n)) (ArrayV (make_array_value t (Fixed n) vs)) =
  SOME (ArrayV (make_array_value t (Fixed n) vs))
Proof
  rpt strip_tac >>
  `EVERY (\(k,v). k < n) (enumerate_static_array (default_value t) 0 vs)` by
    (simp[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >>
     gvs[MEM_enumerate_static_array_iff]) >>
  `EVERY (\v. safe_cast t v = SOME v)
     (MAP SND (enumerate_static_array (default_value t) 0 vs))` by
    (gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
     PairCases_on `y` >> gvs[MEM_enumerate_static_array_iff] >>
     metis_tac[MEM_EL]) >>
  `EVERY (\v. v <> default_value t)
     (MAP SND (enumerate_static_array (default_value t) 0 vs))` by
    (simp[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
     PairCases_on `y` >> gvs[MEM_enumerate_static_array_iff]) >>
  drule cast_fixed_replicate >> strip_tac >> drule cast_fixed_list >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[] >> strip_tac >>
  simp[make_array_value_def, Once safe_cast_def,
    enumerate_static_array_sorted, ZIP_MAP_MAP, MAP_ID]
QED

Theorem cd_word_value_safe_cast[local]:
  cd_cast_domain tv /\ cd_word_value tv w = SOME v ==>
  safe_cast tv v = SOME v
Proof
  Cases_on `tv` >> simp[cd_word_value_def]
  >- (rename1 `BaseTV bt` >> Cases_on `bt` >>
      simp[cd_word_value_def, safe_cast_def, cd_cast_domain_def,
        AllCaseEqs()] >> rpt strip_tac >> gvs[]
      >- gvs[within_int_bound_def]
      >- (Cases_on `b` >> gvs[cd_word_value_def, cd_cast_domain_def,
            AllCaseEqs(), LENGTH_TAKE, byteTheory.LENGTH_word_to_bytes,
            fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
      simp[fcpLib.INDEX_CONV ``dimindex(:160)``]) >>
  simp[cd_word_value_def, safe_cast_def, cd_cast_domain_def,
    AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem cd_decode_safe_cast_mutual[local]:
  (!nat cd tv p v. cd_cast_domain tv /\ cd_decode nat cd tv p = SOME v ==>
     safe_cast tv v = SOME v) /\
  (!nat cd t base i k vs. cd_cast_domain t /\
     cd_decode_elems nat cd t base i k = SOME vs ==>
     LENGTH vs = k /\ EVERY (\v. safe_cast t v = SOME v) vs) /\
  (!nat cd ts p ofs vs. EVERY cd_cast_domain ts /\
     cd_decode_list nat cd ts p ofs = SOME vs ==>
     LIST_REL (\t v. safe_cast t v = SOME v) ts vs)
Proof
  ho_match_mp_tac cd_decode_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[Once cd_decode_def, cd_cast_domain_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >- simp[safe_cast_def, cd_bytes_def, LENGTH_TAKE]
  >- simp[safe_cast_def, cd_bytes_def, LENGTH_TAKE]
  >- (drule cast_fixed_replicate >> strip_tac >> drule cast_fixed_list >>
      disch_then (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
      simp[Once safe_cast_def])
  >- (irule cast_fixed_array >> simp[])
  >- (drule cast_fixed_list >> disch_then (qspec_then `[]` mp_tac) >>
      simp[] >> strip_tac >> simp[Once safe_cast_def])
  >- (gvs[EVERY_MAP, combinTheory.o_DEF] >>
      `LENGTH vs = LENGTH fs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
      drule cast_fixed_list >> disch_then (qspec_then `[]` mp_tac) >>
      simp[] >> strip_tac >> simp[Once safe_cast_def, MAP_ZIP])
  >- simp[Once safe_cast_def] >>
  irule cd_word_value_safe_cast >> simp[cd_cast_domain_def] >> metis_tac[]
QED

Theorem cd_decode_safe_cast:
  cd_cast_domain tv /\ cd_decode nat cd tv p = SOME v ==>
  safe_cast tv v = SOME v
Proof
  metis_tac[cd_decode_safe_cast_mutual]
QED

Theorem calldata_decode_args_safe_cast:
  !tvs ofs vals. EVERY cd_cast_domain tvs /\
    calldata_decode_args cd tvs ofs = SOME vals ==>
    LIST_REL (\tv v. safe_cast tv v = SOME v) tvs vals
Proof
  Induct >> simp[calldata_decode_args_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[cd_decode_safe_cast]
QED
