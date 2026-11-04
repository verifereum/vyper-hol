Theory bodySimAugPlaceStore
Ancestors
  bodySimAugPlaceLoad stmtSimAssignAttr valueEncodingProps valueEncodingProofs
  valueEncoding targetPlaceSim vyperValue vyperTyping vyperValueOperation alist arithmetic list sorting relation
Libs
  wordsLib

Theorem aug_place_fields_rebuild:
  !fs vals fld k ctv child base mem mem'.
    struct_has_type fs vals /\ fields_val_wf vals fs /\
    fields_in_memory vals fs base mem /\
    mem_field_offset fs fld = SOME (k,ctv) /\
    val_in_memory ctv child (base+k) mem' /\
    (!q n. q+n <= base+k \/ base+k+type_memory_size ctv <= q ==>
      mem_bytes_at q n mem' = mem_bytes_at q n mem) ==>
    fields_in_memory (AFUPDKEY fld (K child) vals) fs base mem'
Proof
  Induct >> gen_tac >> Cases_on `vals` >>
  simp[value_has_type_def, mem_field_offset_def] >>
  rename1 `struct_has_type (ft::fs) (fv::vs)` >>
  PairCases_on `ft` >> PairCases_on `fv` >>
  simp[value_has_type_def, mem_field_offset_def, val_in_memory_def,
       val_wf_def, AFUPDKEY_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `ft0 = fld` >> gvs[AllCaseEqs()]
  >- (simp[val_in_memory_def] >>
      irule (cj 2 valueEncodingProofsTheory.val_in_memory_mem_agree_proof) >>
      conj_tac >- simp[] >>
      qexists_tac `mem` >> simp[] >>
      first_x_assum irule >> simp[])
  >> PairCases_on `z` >> gvs[] >> simp[val_in_memory_def] >>
  conj_tac
  >- (irule (cj 1 valueEncodingProofsTheory.val_in_memory_mem_agree_proof) >>
      conj_tac >- simp[] >> qexists_tac `mem` >> simp[] >>
      first_x_assum irule >> simp[]) >>
  first_x_assum irule >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  qexistsl_tac [`ctv`, `z0`, `mem`] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  simp[AC ADD_ASSOC ADD_COMM]
QED

Theorem aug_place_elems_rebuild:
  !vs i tv child base mem mem'.
    i < LENGTH vs /\ elems_val_wf vs tv /\
    elems_in_memory vs base tv mem /\
    val_in_memory tv child (base+i*type_memory_size tv) mem' /\
    (!q n. q+n <= base+i*type_memory_size tv \/
       base+(i+1)*type_memory_size tv <= q ==>
       mem_bytes_at q n mem' = mem_bytes_at q n mem) ==>
    elems_in_memory (LUPDATE child i vs) base tv mem'
Proof
  Induct >> simp[] >> Cases_on `i` >>
  simp[val_in_memory_def, val_wf_def, LUPDATE_def] >> rpt gen_tac >> strip_tac
  >- (irule (cj 3 valueEncodingProofsTheory.val_in_memory_mem_agree_proof) >>
      conj_tac >- simp[] >> qexists_tac `mem` >> simp[] >>
      first_x_assum irule >> simp[]) >>
  simp[val_in_memory_def] >> conj_tac
  >- (irule (cj 1 valueEncodingProofsTheory.val_in_memory_mem_agree_proof) >>
      conj_tac >- simp[] >> qexists_tac `mem` >> simp[] >>
      first_x_assum irule >> simp[MULT_CLAUSES] ) >>
  first_x_assum irule >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  reverse conj_tac >- gvs[MULT_CLAUSES, AC ADD_ASSOC ADD_COMM] >>
  qexists_tac `mem` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  pure_rewrite_tac [MULT_CLAUSES, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] >>
  rule_assum_tac (PURE_REWRITE_RULE
    [MULT_CLAUSES, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]) >> decide_tac
QED

Theorem aug_place_tuple_rebuild:
  !tvs vs i child base mem mem'.
    LENGTH vs = LENGTH tvs /\ i < LENGTH tvs /\
    tuple_val_wf vs tvs /\ tuple_in_memory vs tvs base mem /\
    val_in_memory (EL i tvs) child
      (base+type_memory_size_list (TAKE i tvs)) mem' /\
    (!q n. q+n <= base+type_memory_size_list (TAKE i tvs) \/
       base+type_memory_size_list (TAKE i tvs)+type_memory_size (EL i tvs) <= q ==>
       mem_bytes_at q n mem' = mem_bytes_at q n mem) ==>
    tuple_in_memory (LUPDATE child i vs) tvs base mem'
Proof
  Induct >> gen_tac >> Cases_on `vs` >> simp[] >>
  Cases_on `i` >>
  simp[val_in_memory_def, val_wf_def, LUPDATE_def, type_memory_size_def] >>
  rpt gen_tac >> strip_tac
  >- (irule (cj 5 valueEncodingProofsTheory.val_in_memory_mem_agree_proof) >>
      conj_tac >- simp[] >> qexists_tac `mem` >> simp[] >>
      first_x_assum irule >> simp[]) >>
  simp[val_in_memory_def] >> conj_tac
  >- (irule (cj 1 valueEncodingProofsTheory.val_in_memory_mem_agree_proof) >>
      conj_tac >- simp[] >> qexists_tac `mem` >> simp[] >>
      first_x_assum irule >> simp[]) >>
  first_x_assum irule >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  reverse conj_tac >- gvs[AC ADD_ASSOC ADD_COMM] >>
  qexists_tac `mem` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem aug_place_kvs_all:
  !al base tv mem.
    kvs_in_memory al base tv mem <=>
    (!j v. MEM (j,v) al ==>
      val_in_memory tv v (base+j*type_memory_size tv) mem)
Proof
  Induct >> simp[val_in_memory_def] >> gen_tac >> PairCases_on `h` >>
  simp[val_in_memory_def] >> metis_tac[]
QED

Theorem aug_place_kvs_insert:
  !al k child base tv mem.
    SORTED $< (MAP FST al) /\
    val_in_memory tv child (base+k*type_memory_size tv) mem /\
    (!j v. MEM (j,v) al /\ j <> k ==>
      val_in_memory tv v (base+j*type_memory_size tv) mem) ==>
    kvs_in_memory (insert_sarray k child al) base tv mem
Proof
  Induct >> simp[insert_sarray_def, val_in_memory_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  gvs[SORTED_EQ, transitive_def] >>
  simp[Once insert_sarray_def] >>
  Cases_on `k = h0`
  >- (gvs[val_in_memory_def, aug_place_kvs_all] >>
      fs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[LESS_ANTISYM]) >>
  Cases_on `k < h0`
  >- (simp[val_in_memory_def, aug_place_kvs_all] >>
      fs[MEM_MAP, pairTheory.EXISTS_PROD] >>
      metis_tac[LESS_ANTISYM, LESS_TRANS]) >>
  simp[val_in_memory_def] >>
  first_x_assum irule >> simp[]
QED

Theorem aug_place_lookup_insert:
  !al k v j.
    ALOOKUP (insert_sarray k v al) j =
      if j = k then SOME v else ALOOKUP al j
Proof
  Induct >- simp[insert_sarray_def, EQ_SYM_EQ] >>
  gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> simp[Once insert_sarray_def] >>
  Cases_on `k = h0` >> Cases_on `k < h0` >> Cases_on `j = k` >>
  gvs[] >> Cases_on `j = h0` >> gvs[]
QED

Theorem aug_place_sparse_rebuild:
  !al k child base tv bound mem'.
    SORTED $< (MAP FST al) /\
    val_in_memory tv child (base+k*type_memory_size tv) mem' /\
    (!j v. MEM (j,v) al /\ j <> k ==>
      val_in_memory tv v (base+j*type_memory_size tv) mem') /\
    (!j. j < bound /\ j <> k /\ ALOOKUP al j = NONE ==>
      val_in_memory tv (default_value tv) (base+j*type_memory_size tv) mem') ==>
    val_in_memory (ArrayTV tv (Fixed bound))
      (ArrayV (SArrayV (if child = default_value tv then ADELKEY k al
                       else insert_sarray k child al))) base mem'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `child = default_value tv` >>
  simp[val_in_memory_def]
  >- (conj_tac
      >- (simp[aug_place_kvs_all, ADELKEY_def, MEM_FILTER] >>
          rpt strip_tac >> first_x_assum irule >> simp[]) >>
      rpt strip_tac >> gvs[ALOOKUP_ADELKEY, AllCaseEqs()] >>
      Cases_on `i = k` >> gvs[]) >>
  conj_tac
  >- (irule aug_place_kvs_insert >> simp[]) >>
  rpt strip_tac >> gvs[aug_place_lookup_insert, AllCaseEqs()]
QED
