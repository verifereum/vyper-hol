Theory bodyPtrPopPathStep
Ancestors bodyPtrPopSpatialSplit bodyPtrDefs robustCopyTransportPtr normalizationPrefixPtr pred_set typedCopyLayoutPtr exprSimProps loweringPosts valueEncoding
  valueEncodingProofs exprSimAggregateEncoding vyperState vyperTyping
  vyperValueOperation tupleMemoryLayout vyperPlaceStatePreservation

Theorem pop_fields_memory_offset:
  !fs vals base mem fld child k ct.
    struct_has_type fs vals /\ fields_in_memory vals fs base mem /\
    ALOOKUP vals fld = SOME child /\ mem_field_offset fs fld = SOME (k,ct) ==>
    val_in_memory ct child (base+k) mem
Proof
  Induct_on `fs` >> simp[mem_field_offset_def] >>
  PairCases >> Cases_on `vals` >> simp[value_has_type_def] >>
  PairCases_on `h` >>
  simp[value_has_type_def, val_in_memory_def, mem_field_offset_def] >>
  rpt strip_tac >> Cases_on `h0 = fld` >> gvs[AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >>
  first_x_assum drule_all >>
  `base' + type_memory_size h1 + z0 = base' + (z0 + type_memory_size h1)` by
    decide_tac >> asm_rewrite_tac []
QED

Theorem pop_step_memory_extract:
  !rt root sb child k ct base mem.
  value_has_type rt root /\
  evaluate_subscripts rt root [sb] = INL child /\
  mem_step_offset rt sb = SOME (k,ct) /\
  val_in_memory rt root base mem ==>
  val_in_memory ct child (base+k) mem
Proof
  Cases_on `sb`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `rt` >>
      simp[mem_step_offset_def] >> rpt strip_tac >>
      gvs[AllCaseEqs()] >> Cases_on `root` >> gvs[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      gvs[value_has_type_def, evaluate_subscripts_def, array_index_def,
          val_in_memory_def, AllCaseEqs(), listTheory.oEL_THM]
      >- (simp[type_memory_size_list_sum] >> irule tuple_in_memory_element >>
          simp[] >> metis_tac[values_have_types_length])
      >- (Cases_on `b` >> gvs[value_has_type_def, mem_step_offset_def] >>
          drule_all elems_in_memory_EL >> simp[])
      >- gvs[mem_step_offset_def]
      >> gvs[mem_step_offset_def] >> irule kvs_in_memory_lookup >>
         goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `rt` >> simp[mem_step_offset_def] >> rpt strip_tac >>
  Cases_on `root` >> gvs[value_has_type_def, evaluate_subscripts_def,
    val_in_memory_def, AllCaseEqs()] >>
  irule pop_fields_memory_offset >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem pop_path_memory_extract:
  !path rt root child k ct base mem.
  well_formed_type_value rt /\ value_has_type rt root /\
  evaluate_subscripts rt root path = INL child /\
  mem_path_offset rt path = SOME (k,ct) /\
  val_in_memory rt root base mem ==>
  val_in_memory ct child (base+k) mem
Proof
  Induct_on `path` >- simp[mem_path_offset_def, evaluate_subscripts_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `val_in_memory rt root addr mem` >>
  gvs[Once mem_path_offset_def, AllCaseEqs()] >>
  rename1 `mem_step_offset rt h = SOME (step0,step1)` >>
  rename1 `mem_path_offset step1 path = SOME tail` >> PairCases_on `tail` >>
  gvs[] >>
  `mem_path_offset rt [h] = SOME (step0,step1)` by
    simp[mem_path_offset_def] >>
  drule mem_path_offset_sound >>
  simp[subscripts_type_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path`, `root`] mp_tac) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `val_in_memory step1 v (addr+step0) mem` by
    (irule pop_step_memory_extract >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `well_formed_type_value step1` by
    (irule subscripts_type_well_formed >> goal_assum (drule_at Any) >>
     qexists_tac `[h]` >> simp[subscripts_type_def]) >>
  `value_has_type step1 v` by
    (irule evaluate_subscripts_type >>
     qexistsl_tac [`root`, `[h]`, `rt`] >> simp[subscripts_type_def]) >>
  `evaluate_subscripts step1 v path = INL child` by metis_tac[] >>
  first_x_assum drule_all >>
  pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >> simp[]
QED

Theorem pop_step_robust_memory_extract:
  !rt root sb child k ct base mem dirty.
  value_has_type rt root /\
  evaluate_subscripts rt root [sb] = INL child /\
  mem_step_offset rt sb = SOME (k,ct) /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory rt root base m) ==>
  !m. mem_agree_outside dirty mem m ==>
    val_in_memory ct child (base+k) m
Proof
  metis_tac[pop_step_memory_extract]
QED

Theorem pop_path_robust_memory_extract:
  !path rt root child k ct base mem dirty.
  well_formed_type_value rt /\ value_has_type rt root /\
  evaluate_subscripts rt root path = INL child /\
  mem_path_offset rt path = SOME (k,ct) /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory rt root base m) ==>
  !m. mem_agree_outside dirty mem m ==>
    val_in_memory ct child (base+k) m
Proof
  metis_tac[pop_path_memory_extract]
QED

Theorem pop_stride_intervals_apart:
  !i j stride. i <> j ==>
    i * stride + stride <= j * stride \/
    j * stride + stride <= i * stride
Proof
  rpt strip_tac >> Cases_on `i < j`
  >- (disj1_tac >>
      `SUC i <= j` by decide_tac >>
      drule arithmeticTheory.LESS_MONO_MULT >> disch_then (qspec_then `stride` mp_tac) >>
      pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  disj2_tac >> `SUC j <= i` by decide_tac >>
  drule arithmeticTheory.LESS_MONO_MULT >> disch_then (qspec_then `stride` mp_tac) >>
  pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac
QED

Theorem pop_window_robust_frame:
  !tv v p q n dirty mem mem' writes.
  val_wf tv v /\ (p+type_memory_size tv <= q \/ q+n <= p) /\
  (!x. x IN writes ==> q <= x /\ x < q+n) /\
  mem_agree_outside writes mem' mem /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v p m) ==>
  !m. mem_agree_outside dirty mem' m ==> val_in_memory tv v p m
Proof
  rpt gen_tac >> strip_tac >>
  `val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >> simp[] >>
  qexistsl_tac [`mem`, `mem'`, `dirty`, `dirty`, `writes`] >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  fs[mem_agree_outside_def] >>
  qpat_x_assum `!x. x IN writes ==> _` drule >> decide_tac
QED

Theorem pop_array_sibling_robust_frame:
  !i j tv v base dirty mem mem' writes.
  i <> j /\ val_wf tv v /\
  (!x. x IN writes ==>
    base+j*type_memory_size tv <= x /\
    x < base+j*type_memory_size tv+type_memory_size tv) /\
  mem_agree_outside writes mem' mem /\
  (!m. mem_agree_outside dirty mem m ==>
    val_in_memory tv v (base+i*type_memory_size tv) m) ==>
  !m. mem_agree_outside dirty mem' m ==>
    val_in_memory tv v (base+i*type_memory_size tv) m
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `!m. mem_agree_outside dirty mem m ==> val_in_memory tv v (addr+i*type_memory_size tv) m` >>
  `i*type_memory_size tv+type_memory_size tv <= j*type_memory_size tv \/
   j*type_memory_size tv+type_memory_size tv <= i*type_memory_size tv` by
    (irule pop_stride_intervals_apart >> simp[]) >>
  rpt strip_tac >> irule pop_window_robust_frame >> simp[] >>
  qexistsl_tac [`dirty`, `mem`, `mem'`, `type_memory_size tv`,
               `addr+j*type_memory_size tv`, `writes`] >>
  fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >> decide_tac
QED

Theorem pop_elems_robust_replace:
  !vs tv j new off dirty mem mem' writes.
  elems_val_wf vs tv /\ j < LENGTH vs /\
  (!x. x IN writes ==>
    off+j*type_memory_size tv <= x /\
    x < off+j*type_memory_size tv+type_memory_size tv) /\
  mem_agree_outside writes mem' mem /\
  (!m. mem_agree_outside dirty mem m ==> elems_in_memory vs off tv m) /\
  (!m. mem_agree_outside dirty mem' m ==>
    val_in_memory tv new (off+j*type_memory_size tv) m) ==>
  !m. mem_agree_outside dirty mem' m ==>
    elems_in_memory (LUPDATE new j vs) off tv m
Proof
  rpt strip_tac >> irule elems_in_memory_intro >>
  simp[] >> rpt strip_tac >> rename1 `i < LENGTH vs` >>
  Cases_on `i = j` >- gvs[listTheory.EL_LUPDATE] >>
  simp[listTheory.EL_LUPDATE] >>
  `val_wf tv (EL i vs)` by
    (irule exprSimPopTheory.elems_val_wf_EL >> goal_assum (drule_at Any) >> simp[]) >>
  `!m. mem_agree_outside dirty mem m ==>
    val_in_memory tv (EL i vs) (off+i*type_memory_size tv) m` by
    (rpt strip_tac >> qpat_x_assum `!m. _ ==> elems_in_memory _ _ _ _` drule >>
     strip_tac >> irule elems_in_memory_EL >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all pop_array_sibling_robust_frame >> simp[]
QED

Theorem pop_robust_header_frame:
  !base w dirty mem mem' writes.
  (!x. x IN writes ==> base+32 <= x) /\
  mem_agree_outside writes mem' mem /\
  (!m. mem_agree_outside dirty mem m ==> mem_word_at base m = w) ==>
  !m. mem_agree_outside dirty mem' m ==> mem_word_at base m = w
Proof
  rpt gen_tac >> strip_tac >> rename1 `!m. mem_agree_outside dirty mem' m ==> mem_word_at addr m = w` >>
  `!i. addr <= i /\ i < addr+32 ==> i NOTIN dirty` by
    (drule representationCleanPtrTheory.robust_mem_word_at_clean >> simp[]) >>
  `!i. addr <= i /\ i < addr+32 ==> i NOTIN writes` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     qpat_x_assum `!x. x IN writes ==> _` drule >> decide_tac) >>
  `mem_word_at addr mem = w` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `mem_word_at addr mem = mem_word_at addr mem'` by
    (irule pop_clean_word_agreement >> qexists_tac `writes` >> simp[]) >>
  rpt strip_tac >>
  `mem_word_at addr m = mem_word_at addr mem'` by
    (irule pop_clean_word_agreement >> qexists_tac `dirty` >> simp[]) >> metis_tac[]
QED

Theorem pop_dynarray_robust_replace:
  !vs tv cap j new addr dirty mem mem' writes.
  elems_val_wf vs tv /\ j < LENGTH vs /\
  (!x. x IN writes ==>
    addr+32+j*type_memory_size tv <= x /\
    x < addr+32+j*type_memory_size tv+type_memory_size tv) /\
  mem_agree_outside writes mem' mem /\
  (!m. mem_agree_outside dirty mem m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) addr m) /\
  (!m. mem_agree_outside dirty mem' m ==>
    val_in_memory tv new (addr+32+j*type_memory_size tv) m) ==>
  !m. mem_agree_outside dirty mem' m ==>
    val_in_memory (ArrayTV tv (Dynamic cap))
      (ArrayV (DynArrayV (LUPDATE new j vs))) addr m
Proof
  rpt gen_tac >> strip_tac >>
  `!m. mem_agree_outside dirty mem m ==>
    mem_word_at addr m = n2w (LENGTH vs)` by
    (rpt strip_tac >>
     qpat_x_assum `!m. _ ==> val_in_memory (ArrayTV _ _) _ _ _` drule >>
     simp[val_in_memory_def]) >>
  `!m. mem_agree_outside dirty mem' m ==>
    mem_word_at addr m = n2w (LENGTH vs)` by
    (rpt strip_tac >> irule pop_robust_header_frame >>
     qexistsl_tac [`dirty`, `mem`, `mem'`, `writes`] >> simp[] >> rpt strip_tac >>
     qpat_x_assum `!x. x IN writes ==> _` drule >> decide_tac) >>
  `!m. mem_agree_outside dirty mem m ==> elems_in_memory vs (addr+32) tv m` by
    (rpt strip_tac >>
     qpat_x_assum `!m. _ ==> val_in_memory (ArrayTV _ _) _ _ _` drule >>
     simp[val_in_memory_def]) >>
  `!m. mem_agree_outside dirty mem' m ==>
    elems_in_memory (LUPDATE new j vs) (addr+32) tv m` by
    (rpt strip_tac >> irule pop_elems_robust_replace >> simp[] >>
     qexistsl_tac [`dirty`, `mem`, `mem'`, `writes`] >>
     fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  simp[val_in_memory_def]
QED

Theorem pop_insert_sarray_members:
  !kvs j new i v.
  SORTED $< (MAP FST kvs) /\ MEM (i,v) (insert_sarray j new kvs) ==>
  (i = j /\ v = new) \/ (i <> j /\ MEM (i,v) kvs)
Proof
  Induct_on `kvs` >> simp[insert_sarray_def] >> PairCases >>
  rpt gen_tac >> Cases_on `j = h0` >> Cases_on `j < h0` >>
  simp[insert_sarray_def, sortingTheory.less_sorted_eq,
       listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
  rpt strip_tac >> gvs[]
  >- (first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
      (impl_tac >- metis_tac[]) >> rpt strip_tac >> gvs[] >> decide_tac)
  >- (first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
      (impl_tac >- metis_tac[]) >> rpt strip_tac >> gvs[] >> decide_tac) >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem pop_sparse_update_lookup:
  !kvs tv j new i.
  ALOOKUP (if new = default_value tv then ADELKEY j kvs
           else insert_sarray j new kvs) i =
  if i = j then (if new = default_value tv then NONE else SOME new)
  else ALOOKUP kvs i
Proof
  Induct_on `kvs`
  >- (rpt gen_tac >> Cases_on `new = default_value tv` >>
      Cases_on `i = j` >> simp[insert_sarray_def, alistTheory.ALOOKUP_ADELKEY,
        alistTheory.ADELKEY_def]) >>
  simp[insert_sarray_def, alistTheory.ALOOKUP_ADELKEY] >> PairCases >> rpt gen_tac >> Cases_on `new = default_value tv` >>
  simp[alistTheory.ALOOKUP_ADELKEY] >>
  Cases_on `j = h0` >> Cases_on `j < h0` >>
  Cases_on `i = j` >> Cases_on `i = h0` >> gvs[insert_sarray_def]
  >- (first_x_assum (qspecl_then [`tv`, `i`, `new`, `i`] mp_tac) >> simp[]) >>
  first_x_assum (qspecl_then [`tv`, `j`, `new`, `i`] mp_tac) >> simp[]
QED

Theorem pop_kvs_val_wf_every:
  !kvs tv cap. kvs_val_wf kvs tv cap <=>
    EVERY (\(i,v). i < cap /\ val_wf tv v) kvs
Proof
  Induct_on `kvs` >> simp[val_wf_def] >> PairCases >>
  simp[val_wf_def, boolTheory.CONJ_ASSOC]
QED

Theorem pop_sparse_sibling_robust_frame:
  !kvs tv cap i j addr dirty mem mem' writes.
  kvs_val_wf kvs tv cap /\ i < cap /\ i <> j /\
  (!x. x IN writes ==> addr+j*type_memory_size tv <= x /\
    x < addr+j*type_memory_size tv+type_memory_size tv) /\
  mem_agree_outside writes mem' mem /\
  (!m. mem_agree_outside dirty mem m ==>
    val_in_memory (ArrayTV tv (Fixed cap)) (ArrayV (SArrayV kvs)) addr m) ==>
  !m. mem_agree_outside dirty mem' m ==>
    val_in_memory tv (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
      (addr+i*type_memory_size tv) m
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP kvs i` >> simp[]
  >- (rpt strip_tac >> irule pop_array_sibling_robust_frame >> simp[] >>
      simp[valueEncodingProofsTheory.val_wf_default_value_proof] >>
      qexistsl_tac [`dirty`, `j`, `mem`, `mem'`, `writes`] >>
      fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
      rpt strip_tac >>
      qpat_x_assum `!m. _ ==> val_in_memory (ArrayTV _ _) _ _ _` drule >>
      simp[val_in_memory_def]) >>
  rename1 `ALOOKUP kvs i = SOME v` >>
  `MEM (i,v) kvs` by metis_tac[alistTheory.ALOOKUP_MEM] >>
  `val_wf tv v` by
    (fs[pop_kvs_val_wf_every, listTheory.EVERY_MEM] >>
     qpat_x_assum `!e. MEM e kvs ==> _` (qspec_then `(i,v)` mp_tac) >> simp[]) >>
  rpt strip_tac >> irule pop_array_sibling_robust_frame >> simp[] >>
  qexistsl_tac [`dirty`, `j`, `mem`, `mem'`, `writes`] >>
  fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  rpt strip_tac >>
  `kvs_in_memory kvs addr tv m'` by
    (qpat_x_assum `!m. _ ==> val_in_memory (ArrayTV _ _) _ _ _` drule >>
     simp[val_in_memory_def]) >>
  drule_all kvs_in_memory_lookup >> simp[]
QED

Theorem pop_sparse_kvs_robust_replace:
  !kvs tv cap j new addr dirty mem mem' writes.
  kvs_val_wf kvs tv cap /\ SORTED $< (MAP FST kvs) /\
  (!x. x IN writes ==> addr+j*type_memory_size tv <= x /\
    x < addr+j*type_memory_size tv+type_memory_size tv) /\
  mem_agree_outside writes mem' mem /\
  (!m. mem_agree_outside dirty mem m ==> kvs_in_memory kvs addr tv m) /\
  (!m. mem_agree_outside dirty mem' m ==>
    val_in_memory tv new (addr+j*type_memory_size tv) m) ==>
  !m. mem_agree_outside dirty mem' m ==>
    kvs_in_memory (if new = default_value tv then ADELKEY j kvs
                   else insert_sarray j new kvs) addr tv m
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  simp[kvs_in_memory_every, listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >>
  rpt gen_tac >> strip_tac >> rename1 `val_in_memory tv v (addr+i*_) m` >>
  `(i = j /\ v = new) \/ (i <> j /\ MEM (i,v) kvs)` by
    (Cases_on `new = default_value tv` >> gvs[alistTheory.MEM_ADELKEY] >>
     drule_all pop_insert_sarray_members >> simp[]) 
  >- gvs[] >>
  `val_wf tv v` by
    (fs[pop_kvs_val_wf_every, listTheory.EVERY_MEM] >>
     qpat_x_assum `!e. MEM e kvs ==> _` (qspec_then `(i,v)` mp_tac) >> simp[]) >>
  `!m. mem_agree_outside dirty mem m ==>
    val_in_memory tv v (addr+i*type_memory_size tv) m` by
    (rpt strip_tac >>
     qpat_x_assum `!m. _ ==> kvs_in_memory _ _ _ _` drule >>
     simp[kvs_in_memory_every, listTheory.EVERY_MEM] >>
     disch_then drule >> simp[]) >>
  drule_all pop_array_sibling_robust_frame >> simp[]
QED

Theorem pop_sparse_robust_replace:
  !kvs tv cap j new addr dirty mem mem' writes.
  kvs_val_wf kvs tv cap /\ SORTED $< (MAP FST kvs) /\ j < cap /\
  (!x. x IN writes ==> addr+j*type_memory_size tv <= x /\
    x < addr+j*type_memory_size tv+type_memory_size tv) /\
  mem_agree_outside writes mem' mem /\
  (!m. mem_agree_outside dirty mem m ==>
    val_in_memory (ArrayTV tv (Fixed cap)) (ArrayV (SArrayV kvs)) addr m) /\
  (!m. mem_agree_outside dirty mem' m ==>
    val_in_memory tv new (addr+j*type_memory_size tv) m) ==>
  !m. mem_agree_outside dirty mem' m ==>
    val_in_memory (ArrayTV tv (Fixed cap))
      (ArrayV (SArrayV (if new = default_value tv then ADELKEY j kvs
                       else insert_sarray j new kvs))) addr m
Proof
  rpt gen_tac >> strip_tac >>
  `!m. mem_agree_outside dirty mem m ==> kvs_in_memory kvs addr tv m` by
    (rpt strip_tac >>
     qpat_x_assum `!m. _ ==> val_in_memory (ArrayTV _ _) _ _ _` drule >>
     simp[val_in_memory_def]) >>
  rpt strip_tac >> simp[val_in_memory_def] >> conj_tac
  >- (drule_all pop_sparse_kvs_robust_replace >> simp[]) >>
  rpt gen_tac >> strip_tac >> rename1 `i < cap` >>
  Cases_on `i = j`
  >- (gvs[pop_sparse_update_lookup] >>
      qpat_x_assum `!m. _ ==> val_in_memory tv new _ _` drule >> simp[]) >>
  `ALOOKUP kvs i = NONE` by
    (qpat_x_assum `ALOOKUP _ i = NONE` mp_tac >>
     simp[pop_sparse_update_lookup]) >>
  drule_all pop_sparse_sibling_robust_frame >> simp[]
QED

Theorem pop_fields_robust_replace:
  !fs vals fld k ct new addr dirty mem mem' writes.
  struct_has_type fs vals /\ fields_val_wf vals fs /\
  mem_field_offset fs fld = SOME (k,ct) /\
  (!x. x IN writes ==> addr+k <= x /\ x < addr+k+type_memory_size ct) /\
  mem_agree_outside writes mem' mem /\
  (!m. mem_agree_outside dirty mem m ==> fields_in_memory vals fs addr m) /\
  (!m. mem_agree_outside dirty mem' m ==> val_in_memory ct new (addr+k) m) ==>
  !m. mem_agree_outside dirty mem' m ==>
    fields_in_memory (AFUPDKEY fld (K new) vals) fs addr m
Proof
  Induct_on `fs` >> simp[mem_field_offset_def] >> PairCases >>
  Cases_on `vals` >> simp[value_has_type_def] >> PairCases_on `h` >>
  simp[value_has_type_def, val_wf_def, mem_field_offset_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = fld` >> gvs[AllCaseEqs()]
  >- (rpt strip_tac >> simp[alistTheory.AFUPDKEY_def, val_in_memory_def] >>
      `val_in_memory (StructTV fs) (StructV t) (addr+type_memory_size ct) m` suffices_by
        simp[val_in_memory_def] >>
      irule pop_window_robust_frame >> simp[val_wf_def] >>
      qexistsl_tac [`dirty`, `mem`, `mem'`, `type_memory_size ct`, `addr`, `writes`] >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!m. _ ==> fields_in_memory _ _ _ _` drule >>
      simp[val_in_memory_def]) >>
  PairCases_on `z` >> gvs[] >>
  `!m. mem_agree_outside dirty mem m ==>
    fields_in_memory t fs (addr+type_memory_size h1) m` by
    (rpt strip_tac >>
     qpat_x_assum `!m. _ ==> fields_in_memory _ _ _ _` drule >>
     simp[val_in_memory_def]) >>
  rpt strip_tac >> simp[alistTheory.AFUPDKEY_def, val_in_memory_def] >> conj_tac
  >- (irule pop_window_robust_frame >> simp[] >>
      qexistsl_tac [`dirty`, `mem`, `mem'`, `type_memory_size ct`,
        `addr+(z0+type_memory_size h1)`, `writes`] >>
      fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
      rpt strip_tac >>
      qpat_x_assum `!m. _ ==> fields_in_memory ((_,_)::_) _ _ _` drule >>
      simp[val_in_memory_def]) >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`dirty`, `mem`, `mem'`, `writes`] >>
  fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem pop_replace_index_list[local]:
  !vs j (new:'a). j < LENGTH vs ==>
    TAKE j vs ++ [new] ++ DROP (SUC j) vs = LUPDATE new j vs
Proof
  Induct_on `vs` >> simp[] >> Cases_on `j` >> simp[listTheory.LUPDATE_def]
QED

Theorem pop_step_robust_memory_replace:
  !rt root sb old updated k ct new addr dirty mem mem' writes.
  well_formed_type_value rt /\ value_has_type rt root /\ val_wf rt root /\
  evaluate_subscripts rt root [sb] = INL old /\
  assign_subscripts rt root [sb] (Replace new) = INL updated /\
  mem_step_offset rt sb = SOME (k,ct) /\
  (!x. x IN writes ==> addr+k <= x /\ x < addr+k+type_memory_size ct) /\
  mem_agree_outside writes mem' mem /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory rt root addr m) /\
  (!m. mem_agree_outside dirty mem' m ==> val_in_memory ct new (addr+k) m) ==>
  !m. mem_agree_outside dirty mem' m ==> val_in_memory rt updated addr m
Proof
  Cases_on `sb`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `rt` >>
      simp[mem_step_offset_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
      Cases_on `root` >> gvs[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      gvs[value_has_type_def, assign_subscripts_def, evaluate_subscripts_def,
        array_set_index_def, array_index_def, AllCaseEqs()]
      >- (Cases_on `b` >>
          gvs[value_has_type_def, val_wf_def, mem_step_offset_def,
              pop_replace_index_list] >>
          irule pop_dynarray_robust_replace >> simp[] >>
          qexistsl_tac [`dirty`, `mem`, `mem'`, `writes`] >>
          fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
      gvs[mem_step_offset_def, val_wf_def] >>
      irule pop_sparse_robust_replace >> simp[] >>
      qexistsl_tac [`dirty`, `mem`, `mem'`, `writes`] >>
      fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  Cases_on `rt` >> simp[mem_step_offset_def] >> rpt strip_tac >>
  Cases_on `root` >>
  gvs[value_has_type_def, assign_subscripts_def, evaluate_subscripts_def,
    AllCaseEqs(), val_wf_def, val_in_memory_def] >>
  irule pop_fields_robust_replace >> simp[] >>
  qexistsl_tac [`dirty`, `mem`, `mem'`, `writes`] >>
  fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED
