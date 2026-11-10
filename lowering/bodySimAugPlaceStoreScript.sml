Theory bodySimAugPlaceStore
Ancestors
  bodySimAugPlaceLoad stmtSimAssignAttr valueEncodingProps valueEncodingProofs
  valueEncoding valueEncodingDefs targetPlaceSim vyperValue vyperTyping vyperState vyperValueOperation alist arithmetic list sorting relation
  stmtSimDeclStore vyperPlaceStatePreservation vyperLookup stmtSimAssignStore
  exprSimHyps vyperTypeInvariants exprLoweringProps compileEnv loweringStateRelDefs exprSimBuffer
  venomState loweringPosts exprSimProps exprSimSource exprSimDefs exprSimHypsDefs
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

Theorem aug_place_cells_disjoint:
  !j k sz base. j <> k ==>
    base+j*sz+sz <= base+k*sz \/ base+k*sz+sz <= base+j*sz
Proof
  rpt strip_tac >> Cases_on `j < k`
  >- (disj1_tac >>
      `(j+1)*sz <= k*sz` by simp[LE_MULT_RCANCEL] >>
      pure_rewrite_tac [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] >>
      rule_assum_tac (PURE_REWRITE_RULE
        [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >> decide_tac) >>
  disj2_tac >>
  `(k+1)*sz <= j*sz` by simp[LE_MULT_RCANCEL] >>
  pure_rewrite_tac [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] >>
  rule_assum_tac (PURE_REWRITE_RULE
    [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >> decide_tac
QED

Theorem aug_place_cell_preserved:
  !tv v base j k mem mem'.
    j <> k /\ val_wf tv v /\
    val_in_memory tv v (base+j*type_memory_size tv) mem /\
    (!q n. q+n <= base+k*type_memory_size tv \/
       base+k*type_memory_size tv+type_memory_size tv <= q ==>
       mem_bytes_at q n mem' = mem_bytes_at q n mem) ==>
    val_in_memory tv v (base+j*type_memory_size tv) mem'
Proof
  rpt strip_tac >>
  irule (cj 1 valueEncodingProofsTheory.val_in_memory_mem_agree_proof) >>
  conj_tac >- simp[] >> qexists_tac `mem` >> simp[] >>
  sym_tac >> first_x_assum irule >> metis_tac[aug_place_cells_disjoint]
QED

Theorem aug_place_kvs_wf_all:
  !al tv bound.
    kvs_val_wf al tv bound <=>
    (!j v. MEM (j,v) al ==> j < bound /\ val_wf tv v)
Proof
  Induct >> simp[val_wf_def] >> gen_tac >> PairCases_on `h` >>
  simp[val_wf_def] >> metis_tac[]
QED

Theorem aug_place_sparse_memory:
  !al k child base tv bound mem mem'.
    SORTED $< (MAP FST al) /\
    val_wf (ArrayTV tv (Fixed bound)) (ArrayV (SArrayV al)) /\
    val_in_memory (ArrayTV tv (Fixed bound)) (ArrayV (SArrayV al)) base mem /\
    val_in_memory tv child (base+k*type_memory_size tv) mem' /\
    (!q n. q+n <= base+k*type_memory_size tv \/
       base+k*type_memory_size tv+type_memory_size tv <= q ==>
       mem_bytes_at q n mem' = mem_bytes_at q n mem) ==>
    val_in_memory (ArrayTV tv (Fixed bound))
      (ArrayV (SArrayV (if child = default_value tv then ADELKEY k al
                       else insert_sarray k child al))) base mem'
Proof
  rpt gen_tac >> strip_tac >> irule aug_place_sparse_rebuild >>
  gvs[val_wf_def, val_in_memory_def, aug_place_kvs_all, aug_place_kvs_wf_all] >>
  conj_tac
  >- (rpt strip_tac >> irule aug_place_cell_preserved >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`k`, `mem`] >> gvs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
  rpt strip_tac >> irule aug_place_cell_preserved >>
  conj_tac >- simp[cj 1 val_wf_default_value_proof] >>
  qexistsl_tac [`k`, `mem`] >> gvs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]
QED

Theorem aug_place_update_list:
  !vs i child. i < LENGTH vs ==>
    TAKE i vs ++ [child] ++ DROP (SUC i) vs = LUPDATE child i vs
Proof
  Induct >> simp[] >> Cases_on `i` >> simp[LUPDATE_def]
QED

Theorem aug_place_step_memory:
  !tv sb k ctv a old a' child base mem mem'.
    mem_step_offset tv sb = SOME (k,ctv) /\
    value_has_type tv a /\ val_wf tv a /\ val_in_memory tv a base mem /\
    evaluate_subscripts tv a [sb] = INL old /\
    assign_subscripts tv a [sb] (Replace child) = INL a' /\
    val_in_memory ctv child (base+k) mem' /\
    (!q n. q+n <= base+k \/ base+k+type_memory_size ctv <= q ==>
      mem_bytes_at q n mem' = mem_bytes_at q n mem) ==>
    val_in_memory tv a' base mem'
Proof
  rpt gen_tac >> strip_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
      gvs[mem_step_offset_def] >> Cases_on `tv` >>
      gvs[mem_step_offset_def] >>
      Cases_on `a` >> gvs[assign_subscripts_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      gvs[assign_subscripts_def, array_set_index_def, value_has_type_def, AllCaseEqs()] >>
      rename1 `ArrayTV ety bd` >> Cases_on `bd` >>
      gvs[val_wf_def, mem_step_offset_def]
      >- (gvs[aug_place_update_list, val_in_memory_def] >> conj_tac
          >- (`mem_bytes_at base' 32 mem' = mem_bytes_at base' 32 mem`
                by (first_x_assum irule >> simp[]) >>
              gvs[mem_word_at_def, mem_bytes_at_def, ADD1]) >>
          irule aug_place_elems_rebuild >>
          conj_tac >- simp[] >> conj_tac >- simp[] >>
          reverse conj_tac
          >- (pure_rewrite_tac[ADD_ASSOC] >>
              once_rewrite_tac[ADD_COMM] >>
              metis_tac[ADD_ASSOC, ADD_COMM]) >>
          qexists_tac `mem` >> simp[] >> rpt strip_tac >>
          first_x_assum irule >>
          pure_rewrite_tac[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] >>
          rule_assum_tac (PURE_REWRITE_RULE
            [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >> decide_tac) >>
      irule aug_place_sparse_memory >>
      conj_tac >- simp[] >>
      conj_tac >- simp[val_wf_def] >>
      conj_tac >- simp[] >> qexists_tac `mem` >> simp[] >> rpt strip_tac >>
      first_x_assum irule >> decide_tac) >>
  Cases_on `tv` >> gvs[mem_step_offset_def] >>
  Cases_on `a` >>
  gvs[value_has_type_def, assign_subscripts_def, val_wf_def,
      val_in_memory_def, AllCaseEqs()] >>
  irule aug_place_fields_rebuild >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  qexistsl_tac [`ctv`, `k`, `mem`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem aug_place_elems_wf_update:
  !vs i tv child. elems_val_wf vs tv /\ val_wf tv child ==>
    elems_val_wf (LUPDATE child i vs) tv
Proof
  Induct >> simp[val_wf_def] >> Cases_on `i` >>
  simp[LUPDATE_def, val_wf_def]
QED

Theorem aug_place_kvs_wf_insert:
  !al k child tv bound.
    kvs_val_wf al tv bound /\ k < bound /\ val_wf tv child ==>
    kvs_val_wf (insert_sarray k child al) tv bound
Proof
  Induct >> simp[insert_sarray_def, val_wf_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  gvs[val_wf_def] >> simp[Once insert_sarray_def] >>
  Cases_on `k = h0` >> Cases_on `k < h0` >> simp[val_wf_def]
QED

Theorem aug_place_step_wf:
  !tv sb k ctv a a' child.
    mem_step_offset tv sb = SOME (k,ctv) /\
    value_has_type tv a /\ val_wf tv a /\
    assign_subscripts tv a [sb] (Replace child) = INL a' /\
    val_wf ctv child ==> val_wf tv a'
Proof
  rpt gen_tac >> strip_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
      gvs[mem_step_offset_def] >> Cases_on `tv` >>
      gvs[mem_step_offset_def] >> Cases_on `a` >>
      gvs[assign_subscripts_def] >> rename1 `ArrayV av` >>
      Cases_on `av` >>
      gvs[assign_subscripts_def, array_set_index_def, value_has_type_def,
          AllCaseEqs()] >> rename1 `ArrayTV ety bd` >> Cases_on `bd` >>
      gvs[val_wf_def, mem_step_offset_def]
      >- simp[aug_place_update_list, val_wf_def, aug_place_elems_wf_update] >>
      IF_CASES_TAC
      >- (gvs[aug_place_kvs_wf_all, ADELKEY_def, MEM_FILTER] >> metis_tac[]) >>
      irule aug_place_kvs_wf_insert >> simp[]) >>
  Cases_on `tv` >> gvs[mem_step_offset_def] >> Cases_on `a` >>
  gvs[value_has_type_def, assign_subscripts_def, val_wf_def, AllCaseEqs()] >>
  drule aug_place_field_type >> strip_tac >>
  irule fields_val_wf_update >> metis_tac[]
QED

Theorem aug_place_step_rebuild:
  !tv sb k ctv a old a' child base mem mem'.
    mem_step_offset tv sb = SOME (k,ctv) /\
    value_has_type tv a /\ val_wf tv a /\ val_in_memory tv a base mem /\
    evaluate_subscripts tv a [sb] = INL old /\
    assign_subscripts tv a [sb] (Replace child) = INL a' /\
    value_has_type ctv child /\ val_wf ctv child /\
    val_in_memory ctv child (base+k) mem' /\
    (!q n. q+n <= base+k \/ base+k+type_memory_size ctv <= q ==>
      mem_bytes_at q n mem' = mem_bytes_at q n mem) ==>
    val_wf tv a' /\ val_in_memory tv a' base mem'
Proof
  rpt strip_tac
  >- (irule aug_place_step_wf >> metis_tac[]) >>
  irule aug_place_step_memory >> metis_tac[]
QED

Theorem aug_place_assign_cons:
  !tv a sb path etv v a'.
    subscript_type tv sb = SOME etv /\
    assign_subscripts tv a (sb::path) (Replace v) = INL a' ==>
    ?old child.
      evaluate_subscripts tv a [sb] = INL old /\
      assign_subscripts etv old path (Replace v) = INL child /\
      assign_subscripts tv a [sb] (Replace child) = INL a'
Proof
  rpt gen_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
      simp[subscript_type_def, assign_subscripts_def] >>
      Cases_on `a` >> simp[assign_subscripts_def] >>
      Cases_on `tv` >>
      simp[subscript_type_def, assign_subscripts_def, evaluate_subscripts_def,
           AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `a` >> Cases_on `tv` >>
  simp[subscript_type_def, assign_subscripts_def, evaluate_subscripts_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem aug_place_fields_wf_project:
  !fs vals fld ctv v.
    struct_has_type fs vals /\ fields_val_wf vals fs /\
    ALOOKUP fs fld = SOME ctv /\ ALOOKUP vals fld = SOME v ==>
    val_wf ctv v
Proof
  Induct >> gen_tac >> Cases_on `vals` >> simp[value_has_type_def] >>
  PairCases_on `h` >> PairCases_on `h'` >>
  simp[value_has_type_def, val_wf_def] >> rpt gen_tac >>
  Cases_on `h0 = fld` >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem aug_place_elems_wf_project:
  !vs tv i. elems_val_wf vs tv /\ i < LENGTH vs ==>
    val_wf tv (EL i vs)
Proof
  Induct >> simp[val_wf_def] >> rpt gen_tac >> Cases_on `i` >>
  simp[val_wf_def]
QED

Theorem aug_place_tuple_wf_project:
  !tvs vs i. tuple_val_wf vs tvs /\ i < LENGTH vs /\ i < LENGTH tvs ==>
    val_wf (EL i tvs) (EL i vs)
Proof
  Induct >> gen_tac >> Cases_on `vs` >> simp[val_wf_def] >>
  Cases_on `i` >> simp[val_wf_def]
QED

Theorem aug_place_step_wf_project:
  !tv a sb k ctv old.
    mem_step_offset tv sb = SOME (k,ctv) /\ value_has_type tv a /\
    val_wf tv a /\ evaluate_subscripts tv a [sb] = INL old ==>
    val_wf ctv old
Proof
  rpt gen_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
      Cases_on `tv` >> simp[mem_step_offset_def] >>
      Cases_on `a` >> simp[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      simp[value_has_type_def, val_wf_def, evaluate_subscripts_def,
           array_index_def, oEL_THM, subscript_type_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[]
      >- (irule aug_place_tuple_wf_project >> simp[]) 
      >- (Cases_on `b` >> gvs[mem_step_offset_def] >>
          irule aug_place_elems_wf_project >> simp[]) >>
      gvs[mem_step_offset_def]
      >- simp[cj 1 val_wf_default_value_proof] >>
      gvs[aug_place_kvs_wf_all] >> metis_tac[ALOOKUP_MEM]) >>
  Cases_on `tv` >> simp[mem_step_offset_def] >>
  Cases_on `a` >> simp[value_has_type_def, val_wf_def,
    evaluate_subscripts_def, AllCaseEqs()] >> rpt strip_tac >>
  drule aug_place_field_type >> strip_tac >>
  irule aug_place_fields_wf_project >> metis_tac[]
QED

Theorem aug_place_path_mstore:
  !path tv k ptv a old a' v base s etv.
    mem_path_offset tv path = SOME (k,ptv) /\
    well_formed_type_value tv /\ value_has_type tv a /\ val_wf tv a /\
    val_in_memory tv a base s.vs_memory /\
    evaluate_subscripts tv a path = INL old /\
    assign_subscripts tv a path (Replace v) = INL a' /\
    store_lays_out etv ptv v ==>
    val_wf tv a' /\
    val_in_memory tv a' base (mstore (base+k) (typed_val_to_w256 etv v) s).vs_memory
Proof
  Induct
  >- simp[mem_path_offset_def, assign_subscripts_def, store_lays_out_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[mem_path_offset_def, AllCaseEqs()] >> PairCases_on `z` >> gvs[] >>
  drule aug_place_step_type >> strip_tac >>
  drule_all aug_place_assign_cons >> strip_tac >>
  rename1 `assign_subscripts etv' child_old path (Replace v) = INL child_new` >>
  `well_formed_type_value etv'` by metis_tac[subscript_type_well_formed] >>
  `subscripts_type tv [h] = SOME etv'` by simp[subscripts_type_def] >>
  `value_has_type etv' child_old` by metis_tac[evaluate_subscripts_type] >>
  `val_wf etv' child_old` by metis_tac[aug_place_step_wf_project] >>
  `val_in_memory etv' child_old (base'+k') s.vs_memory` by
    metis_tac[aug_place_step_project] >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path`,`a`] mp_tac) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `evaluate_subscripts etv' child_old path = INL old` by metis_tac[] >>
  first_x_assum drule_all >> strip_tac >>
  conj_tac >- (irule aug_place_step_wf >> metis_tac[]) >>
  irule aug_place_step_memory >>
  qexistsl_tac [`a`, `child_new`, `etv'`, `k'`, `s.vs_memory`, `child_old`, `h`] >>
  qpat_x_assum `evaluate_subscripts _ _ _ = evaluate_subscripts _ _ _` kall_tac >>
  qpat_x_assum `INL old = _` kall_tac >>
  reverse conj_tac >- (pure_rewrite_tac[ADD_ASSOC] >> simp[]) >>
  `z0 + type_memory_size ptv <= type_memory_size etv'` by
    metis_tac[mem_path_offset_sound] >>
  gvs[store_lays_out_def] >> rpt strip_tac >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem aug_place_memory_write_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w
    (SOME LocMemory) (Type ty) /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  store_lays_out etv ptv v /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  write_place cx (MemoryPlace id path) v es = (INL (),es') ==>
  stmt_state_rel ctx func cenv cx es'
    (mstore (w2n w) (typed_val_to_w256 etv v) s)
Proof
  rpt strip_tac >>
  gvs[place_ptr_rel_def] >>
  `evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (irule aug_place_entry_type_agrees >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
  simp[write_place_def, get_scopes_def, bind_def, lift_option_type_def,
       type_check_def, assert_def, lift_sum_def, set_scopes_def,
       return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  Cases_on `find_containing_scope id es.scopes` >>
  gvs[return_def, raise_def] >>
  rename1 `find_containing_scope id es.scopes = SOME fc` >> PairCases_on `fc` >>
  `fc2 = entry` by metis_tac[find_containing_scope_lookup, optionTheory.SOME_11] >>
  gvs[ignore_bind_def, bind_def, assert_def, return_def, raise_def,
      set_scopes_def, replace_memory_entry_def, AllCaseEqs()] >>
  Cases_on `assign_subscripts entry.type entry.value path (Replace v)` >>
  gvs[return_def, raise_def] >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (irule aug_place_lookup_typed >>
     fs[expr_sim_inv_def, state_well_typed_def] >> metis_tac[]) >>
  suspend "lift_local_store"
QED

Resume aug_place_memory_write_state_rel[lift_local_store]:
  `local_ptrs_rel func cenv es.scopes s /\ alloca_room ctx func s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `w2n b + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz /\
   val_wf entry.type entry.value /\
   val_in_memory entry.type entry.value (w2n b) s.vs_memory` by
    (qpat_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `k + type_memory_size ptv <= type_memory_size entry.type` by
    metis_tac[mem_path_offset_sound] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `w2n (b + n2w k) = w2n b + k` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >> decide_tac) >>
  qpat_assum `w2n (b + n2w k) = _` (fn th => simp_tac bool_ss [th]) >>
  qabbrev_tac `t = mstore (w2n b+k) (typed_val_to_w256 etv v) s` >>
  `val_wf entry.type x /\ val_in_memory entry.type x (w2n b) t.vs_memory` by
    (qunabbrev_tac `t` >> irule aug_place_path_mstore >> metis_tac[]) >>
  `(t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s` by
    simp[Abbr `t`, mstore_def, LET_THM, venom_state_component_equality] >>
  `!q. ~not_local_ptr cenv es.scopes q ==> lookup_var q t = lookup_var q s` by
    simp[Abbr `t`, mstore_def, LET_THM, lookup_var_def] >>
  `type_memory_size ptv = 32` by fs[store_lays_out_def] >>
  `!q n. q+n <= w2n b \/ w2n b+type_memory_size entry.type <= q ==>
      mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory` by
    (rpt strip_tac >> simp[Abbr `t`] >>
     irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `local_region cenv es.scopes s id (w2n b) sz` by simp[local_region_def] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (qunabbrev_tac `t` >> irule local_mstore_immutables_at >>
     conj_tac >- (qexistsl_tac [`id`, `sz`] >> simp[]) >>
     metis_tac[]) >>
  drule_all stmt_state_rel_write_local >> simp[Abbr `t`]
QED

Finalise aug_place_memory_write_state_rel

Theorem aug_place_memory_store_frag:
  emit_void MSTORE [dst;res_op] st = ((),sf) /\
  eval_operand dst u = SOME w /\
  eval_operand res_op u = SOME (typed_val_to_w256 etv v) /\
  stmt_state_rel ctx func cenv cx es u /\
  place_ptr_rel cenv cx u (PlaceR (MemoryPlace id path)) w
    (SOME LocMemory) (Type ty) /\
  expr_sim_inv cenv cx env es /\ lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  store_lays_out etv ptv v /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  write_place cx (MemoryPlace id path) v es = (INL (),es') ==>
  frag_exec ctx st sf (\s. s = u)
    (\s. stmt_state_rel ctx func cenv cx es' s /\
         (!x. lookup_var x s = lookup_var x u) /\
         s.vs_allocas = u.vs_allocas) R
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx func cenv cx es'
     (mstore (w2n w) (typed_val_to_w256 etv v) u)` by
    (irule aug_place_memory_write_state_rel >> metis_tac[]) >>
  imp_res_tac emitHelperPropsTheory.emitted_insts_emit_void >> imp_res_tac emit_void_extends >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st sf)` by
    simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  irule fragExecTheory.frag_exec_run_inst_seq >>
  fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND3] >>
  rpt strip_tac >> disj1_tac >> gvs[] >>
  `step_inst_base (mk_inst st.cs_next_id MSTORE [dst;res_op] []) u =
     OK (mstore (w2n w) (typed_val_to_w256 etv v) u)` by
    (irule emitHelperPropsTheory.step_MSTORE >> simp[]) >>
  gvs[run_inst_seq_def, stmt_state_rel_inst_idx,
      mstore_def, lookup_var_def, LET_THM]
QED
