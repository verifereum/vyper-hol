(*
 * Stores at an assignment place
 *
 * A place target's fragment (targetPlaceSim's target_post) leaves a pointer
 * w that place_ptr_rel relates to the source's place p: a local's region
 * offset in memory, or a slot in storage or transient storage.  The lowering
 * then stores the value there, and the source writes it with write_place.
 * These lemmas run the store from a state related at the source state
 * before the write to one related at the state after it.
 *
 * TOP-LEVEL:
 *   place_store_word_run  — one MSTORE, SSTORE or TSTORE of a word, as
 *                           compile_assign_value's word case, AugAssign
 *                           and a tuple's word element store it
 *   place_store_value_run — compile_assign_value at any location, the
 *                           value's type widening to the place's
 *   place_store_empty_run — the zero length word an empty value stores
 *)

Theory placeStore
Ancestors
  placeStoreMemory placeStoreStorage placeStoreDyn
  stmtSimDefs exprSimHypsDefs typedCopyDomain vyperStoragePlaceProvenance
  loweringPosts fragGasMode exprSimProps localPtrsProps stmtSimDeclPath
  emitHelper venomExecSemantics venomInst exprLoweringProps accountsRelProps vyperLookup vyperPlaceStatePreservation
  valueEncodingTyping vyperStoragePlaceRegion
  stmtLowering exprLowering compileEnv
  vyperInterpreter vyperState vyperValue vyperTypeSystem
  venomState valueEncoding vyperTyping valueEncodingProps valueEncodingProofs
  arithmetic list

Theorem place_store_default_typed[local]:
  (!tv. value_has_type tv (default_value tv)) /\
  (!tvs. values_have_types tvs (MAP default_value tvs)) /\
  (!ftypes. struct_has_type ftypes
      (MAP (\(id,t). (id,default_value t)) ftypes)) /\
  (!p:string # type_value. value_has_type (SND p) (default_value (SND p)))
Proof
  ho_match_mp_tac
    (legacyInduction.mutual_ind_from_ops
      (TypeBase.induction_of ``:type_value``)) >>
  simp[default_value_def, default_value_tuple_MAP, default_value_struct_MAP,
       value_has_type_def] >>
  conj_tac
  >- (Cases >> simp_tac (boss_ss() ++ fcpLib.FCP_ss)
        [default_value_def, value_has_type_def, within_int_bound_def,
         fcpLib.INDEX_CONV ``dimindex(:160)``] >>
      Cases_on `b'` >> simp[default_value_def, value_has_type_def]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `b` >>
      simp[default_value_def, value_has_type_def]) >>
  rpt gen_tac >> PairCases_on `p` >> simp[value_has_type_def]
QED

Theorem place_store_elements_read[local]:
  !vs tv b mem i old.
    elems_in_memory vs b tv mem /\ all_have_type tv vs /\
    oEL i vs = SOME old ==>
    value_has_type tv old /\
    val_in_memory tv old (b + i * type_memory_size tv) mem
Proof
  Induct >> simp[val_in_memory_def, value_has_type_def, oEL_def] >>
  rpt gen_tac >> Cases_on `i` >>
  simp[oEL_def] >> strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`tv`, `b + type_memory_size tv`, `mem`] mp_tac) >>
  disch_then (qspecl_then [`n`, `old`] mp_tac) >>
  `b + SUC n * type_memory_size tv =
   b + type_memory_size tv + n * type_memory_size tv` by
    (pure_rewrite_tac [MULT_CLAUSES] >>
     metis_tac [ADD_ASSOC, ADD_COMM]) >>
  asm_rewrite_tac []
QED

Theorem place_store_tuple_read[local]:
  !vs tvs b mem i old.
    tuple_in_memory vs tvs b mem /\ values_have_types tvs vs /\
    oEL i vs = SOME old ==>
    value_has_type (EL i tvs) old /\
    val_in_memory (EL i tvs) old
      (b + type_memory_size_list (TAKE i tvs)) mem
Proof
  Induct >> simp[val_in_memory_def, value_has_type_def, oEL_def] >>
  Cases_on `tvs` >> simp[value_has_type_def] >>
  rpt gen_tac >> Cases_on `i` >>
  simp[oEL_def, val_in_memory_def, type_memory_size_def] >>
  strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`t`, `b + type_memory_size h`, `mem`] mp_tac) >>
  disch_then (qspecl_then [`n`, `old`] mp_tac) >>
  asm_rewrite_tac [ADD_ASSOC]
QED

Theorem place_store_fields_read[local]:
  !fields tvs b mem id k tv old.
    fields_in_memory fields tvs b mem /\ struct_has_type tvs fields /\
    mem_field_offset tvs id = SOME (k,tv) /\ ALOOKUP fields id = SOME old ==>
    value_has_type tv old /\ val_in_memory tv old (b+k) mem
Proof
  Induct >> simp[value_has_type_def, val_in_memory_def] >>
  Cases_on `h` >> Cases_on `tvs` >> simp[value_has_type_def] >>
  Cases_on `h` >> rpt gen_tac >>
  simp[value_has_type_def, val_in_memory_def, mem_field_offset_def] >>
  strip_tac >> gvs[] >>
  Cases_on `q = id` >> gvs[AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >>
  first_x_assum drule >> disch_then drule >>
  disch_then (qspecl_then [`id`, `z0`, `tv`, `old`] mp_tac) >>
  `b + (z0 + type_memory_size r') = b + type_memory_size r' + z0` by
    metis_tac[ADD_ASSOC, ADD_COMM] >>
  asm_rewrite_tac []
QED

Theorem place_store_sparse_read[local]:
  !kvs tv n b mem i old.
    kvs_in_memory kvs b tv mem /\ sparse_has_type tv n kvs /\
    ALOOKUP kvs i = SOME old ==>
    value_has_type tv old /\
    val_in_memory tv old (b + i * type_memory_size tv) mem
Proof
  Induct >> simp[val_in_memory_def, value_has_type_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[val_in_memory_def, value_has_type_def] >> strip_tac >>
  Cases_on `h0 = i` >> gvs[] >> metis_tac[]
QED

Theorem place_store_step_read:
  !tv sub k ctv a b mem old.
    mem_step_offset tv sub = SOME (k,ctv) /\ value_has_type tv a /\
    val_in_memory tv a b mem /\ evaluate_subscripts tv a [sub] = INL old ==>
    value_has_type ctv old /\ val_in_memory ctv old (b+k) mem
Proof
  rpt gen_tac >> strip_tac >>
  drule mem_step_offset_shape >> strip_tac >> gvs[]
  >- (Cases_on `a` >>
      gvs[value_has_type_def, val_in_memory_def, evaluate_subscripts_def,
          AllCaseEqs()] >>
      drule_all place_store_fields_read >> simp[])
  >- (Cases_on `a` >> gvs[value_has_type_def] >>
      Cases_on `a'` >>
      gvs[value_has_type_def, val_in_memory_def, evaluate_subscripts_def,
          vyperValueOperationTheory.array_index_def, AllCaseEqs()] >>
      metis_tac[place_store_sparse_read, place_store_default_typed])
  >- (Cases_on `a` >> gvs[value_has_type_def] >>
      Cases_on `a'` >>
      gvs[value_has_type_def, val_in_memory_def, evaluate_subscripts_def,
          vyperValueOperationTheory.array_index_def, AllCaseEqs()] >>
      drule_all place_store_elements_read >>
      `b + (Num i * type_memory_size ctv + 32) =
       b + 32 + Num i * type_memory_size ctv` by
        metis_tac[ADD_ASSOC, ADD_COMM] >>
      asm_rewrite_tac []) >>
  Cases_on `a` >> gvs[value_has_type_def] >>
  Cases_on `a'` >>
  gvs[value_has_type_def, val_in_memory_def, evaluate_subscripts_def,
      vyperValueOperationTheory.array_index_def, AllCaseEqs()] >>
  drule_all place_store_tuple_read >> simp[]
QED

Theorem place_store_bytes_agree[local]:
  !b n mem mem'.
    (!q. b <= q /\ q < b+n ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    mem_bytes_at b n mem = mem_bytes_at b n mem'
Proof
  rpt gen_tac >> strip_tac >> irule LIST_EQ >>
  simp[valueEncodingProofsTheory.LENGTH_mem_bytes_at_proof] >>
  rpt strip_tac >> rename1 `i < n` >>
  first_x_assum (qspec_then `b+i` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
  simp[valueEncodingProofsTheory.EL_mem_bytes_at]
QED

Theorem place_store_value_frame[local]:
  !tv v b lo hi mem mem'.
    value_has_type tv v /\ val_in_memory tv v b mem /\
    (b + type_memory_size tv <= lo \/ hi <= b) /\
    (!q. q < lo \/ hi <= q ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    val_in_memory tv v b mem'
Proof
  rpt gen_tac >> strip_tac >>
  (irule val_in_memory_mem_agree >> conj_tac
   >- metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]) >>
  qexistsl_tac [`type_memory_size tv`, `mem`] >>
  asm_rewrite_tac [LESS_EQ_REFL] >>
  irule place_store_bytes_agree >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem place_store_elements_prefix_frame[local]:
  !vs tv b mem mem'.
    elems_in_memory vs b tv mem /\ elems_val_wf vs tv /\
    mem_bytes_at b (LENGTH vs * type_memory_size tv) mem =
      mem_bytes_at b (LENGTH vs * type_memory_size tv) mem' ==>
    elems_in_memory vs b tv mem'
Proof
  Induct_on `vs` >> simp[val_in_memory_def, val_wf_def] >>
  rpt gen_tac >> strip_tac >>
  drule mem_bytes_at_agree_window >> strip_tac >> conj_tac
  >- (irule val_in_memory_mem_agree >> simp[] >>
      qexistsl_tac [`type_memory_size tv`, `mem`] >> simp[] >>
      first_x_assum irule >> simp[ADD1, LEFT_ADD_DISTRIB]) >>
  first_x_assum irule >> simp[] >>
  qexists_tac `mem` >> simp[] >> sym_tac >>
  first_x_assum irule >> simp[ADD1, LEFT_ADD_DISTRIB]
QED

Theorem place_store_elements_indexed[local]:
  !vs b tv mem.
    elems_in_memory vs b tv mem <=>
    !i. i < LENGTH vs ==>
        val_in_memory tv (EL i vs) (b+i*type_memory_size tv) mem
Proof
  Induct >> simp[val_in_memory_def] >> rpt gen_tac >> eq_tac
  >- (strip_tac >> Cases >> simp[] >> strip_tac >>
      first_x_assum (qspec_then `n` mp_tac) >>
      asm_rewrite_tac [MULT_CLAUSES, GSYM ADD_ASSOC] >>
      metis_tac[ADD_COMM]) >>
  strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
  asm_rewrite_tac [MULT_CLAUSES, GSYM ADD_ASSOC, EL, TL, LESS_MONO_EQ] >>
  metis_tac[ADD_COMM]
QED

Theorem place_store_index_frame[local]:
  !tv v b i j mem mem'.
    value_has_type tv v /\ val_in_memory tv v (b+j*type_memory_size tv) mem /\
    j <> i /\
    (!q. q < b+i*type_memory_size tv \/
         b+i*type_memory_size tv+type_memory_size tv <= q ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    val_in_memory tv v (b+j*type_memory_size tv) mem'
Proof
  rpt gen_tac >> strip_tac >>
  irule place_store_value_frame >> conj_tac >- asm_rewrite_tac [] >>
  qexistsl_tac [`b+i*type_memory_size tv+type_memory_size tv`,
    `b+i*type_memory_size tv`, `mem`] >> asm_rewrite_tac [] >>
  Cases_on `j < i`
  >- (disj1_tac >>
      `j*type_memory_size tv+type_memory_size tv <= i*type_memory_size tv` by
        (rewrite_tac[GSYM MULT] >> irule LESS_MONO_MULT >> simp[]) >>
      decide_tac) >>
  disj2_tac >>
  `i*type_memory_size tv+type_memory_size tv <= j*type_memory_size tv` by
    (rewrite_tac[GSYM MULT] >> irule LESS_MONO_MULT >> simp[]) >>
  decide_tac
QED

Theorem place_store_elements_rebuild[local]:
  !vs tv b mem mem' i child.
    all_have_type tv vs /\ elems_in_memory vs b tv mem /\ i < LENGTH vs /\
    val_in_memory tv child (b+i*type_memory_size tv) mem' /\
    (!q. q < b+i*type_memory_size tv \/
         b+i*type_memory_size tv+type_memory_size tv <= q ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    elems_in_memory (LUPDATE child i vs) b tv mem'
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[place_store_elements_indexed, LENGTH_LUPDATE] >>
  qx_gen_tac `j` >> strip_tac >>
  simp[EL_LUPDATE] >> Cases_on `j = i` >- asm_rewrite_tac [] >>
  asm_rewrite_tac [] >>
  `value_has_type tv (EL j vs)` by
    (gvs[all_have_type_EVERY, EVERY_EL]) >>
  `val_in_memory tv (EL j vs) (b+j*type_memory_size tv) mem` by
    metis_tac[place_store_elements_indexed] >>
  irule place_store_index_frame >> conj_tac >- asm_rewrite_tac [] >>
  qexistsl_tac [`i`, `mem`] >> asm_rewrite_tac []
QED

Theorem place_store_fields_rebuild[local]:
  !fields tvs b mem mem' id k tv child.
    struct_has_type tvs fields /\ fields_in_memory fields tvs b mem /\
    mem_field_offset tvs id = SOME (k,tv) /\
    val_in_memory tv child (b+k) mem' /\
    (!q. q < b+k \/ b+k+type_memory_size tv <= q ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    fields_in_memory (AFUPDKEY id (K child) fields) tvs b mem'
Proof
  Induct
  >- (Cases >> simp[value_has_type_def, mem_field_offset_def]) >>
  Cases_on `h` >> Cases_on `tvs` >> simp[value_has_type_def] >>
  Cases_on `h` >> rpt gen_tac >>
  simp[value_has_type_def, val_in_memory_def, mem_field_offset_def] >>
  strip_tac >> gvs[] >>
  Cases_on `q = id` >> gvs[AllCaseEqs()]
  >- (simp[alistTheory.AFUPDKEY_def, val_in_memory_def] >>
      `val_in_memory (StructTV t) (StructV fields)
         (b + type_memory_size r') mem'` suffices_by
        simp[val_in_memory_def] >>
      irule place_store_value_frame >>
      conj_tac >- simp[value_has_type_def] >>
      qexistsl_tac [`b+type_memory_size r'`, `b`, `mem`] >>
      asm_rewrite_tac [val_in_memory_def, LESS_EQ_REFL] >> simp[]) >>
  PairCases_on `z` >> gvs[] >>
  simp[alistTheory.AFUPDKEY_def, val_in_memory_def] >> conj_tac
  >- (irule place_store_value_frame >>
      conj_tac >- asm_rewrite_tac [] >>
      qexistsl_tac [`b+(z0+type_memory_size r')+type_memory_size tv`,
                    `b+(z0+type_memory_size r')`, `mem`] >>
      asm_rewrite_tac [GSYM ADD_ASSOC] >> decide_tac) >>
  first_x_assum irule >>
  conj_tac >- asm_rewrite_tac [] >>
  qexistsl_tac [`z0`, `mem`, `tv`] >>
  `b + type_memory_size r' + z0 = b + (z0 + type_memory_size r')` by
    metis_tac[ADD_ASSOC, ADD_COMM] >>
  `b + type_memory_size r' + (z0 + type_memory_size tv) =
   b + (z0 + (type_memory_size r' + type_memory_size tv))` by
    metis_tac[ADD_ASSOC, ADD_COMM] >>
  asm_rewrite_tac []
QED

Theorem place_store_dynarray_rebuild[local]:
  !vs tv n b mem mem' i child.
    value_has_type (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) b mem /\
    i < LENGTH vs /\
    val_in_memory tv child (b+32+i*type_memory_size tv) mem' /\
    (!q. q < b+32+i*type_memory_size tv \/
         b+32+i*type_memory_size tv+type_memory_size tv <= q ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    val_in_memory (ArrayTV tv (Dynamic n))
      (ArrayV (DynArrayV (LUPDATE child i vs))) b mem'
Proof
  rpt gen_tac >> simp[value_has_type_def, val_in_memory_def] >> strip_tac >>
  conj_tac
  >- (`mem_bytes_at b 32 mem = mem_bytes_at b 32 mem'` by
        (irule place_store_bytes_agree >> rpt strip_tac >>
         qpat_x_assum `!q. _` (qspec_then `q` mp_tac) >>
         impl_tac >- decide_tac >> simp[]) >>
      drule mem_bytes_at_agree_window >> strip_tac >>
      qpat_x_assum `!off2. _` (qspec_then `b` mp_tac) >> simp[]) >>
  `b+32+i*type_memory_size tv = b+(i*type_memory_size tv+32)` by
    metis_tac[ADD_ASSOC, ADD_COMM] >>
  `b+32+i*type_memory_size tv+type_memory_size tv =
   b+(type_memory_size tv+(i*type_memory_size tv+32))` by
    metis_tac[ADD_ASSOC, ADD_COMM] >>
  irule place_store_elements_rebuild >> asm_rewrite_tac [] >>
  qexists_tac `mem` >> asm_rewrite_tac []
QED

Theorem place_store_sparse_indexed[local]:
  !kvs tv n b mem.
    ALL_DISTINCT (MAP FST kvs) /\ EVERY (\kv. FST kv < n) kvs ==>
    (val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) b mem <=>
     !j. j < n ==> val_in_memory tv
       (case ALOOKUP kvs j of NONE => default_value tv | SOME v => v)
       (b+j*type_memory_size tv) mem)
Proof
  rpt gen_tac >> strip_tac >>
  `kvs_in_memory kvs b tv mem <=>
   !j v. MEM (j,v) kvs ==>
     val_in_memory tv v (b+j*type_memory_size tv) mem` by
    (qid_spec_tac `kvs` >> Induct >> simp[val_in_memory_def] >>
     gen_tac >> PairCases_on `h` >> simp[val_in_memory_def] >> metis_tac[]) >>
  asm_rewrite_tac [val_in_memory_sarray] >> eq_tac
  >- (strip_tac >> rpt strip_tac >> Cases_on `ALOOKUP kvs j` >> simp[] >>
      metis_tac[alistTheory.ALOOKUP_MEM]) >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >>
      `j < n` by (gvs[EVERY_MEM] >>
        qpat_x_assum `!kv. _` (qspec_then `(j,v)` mp_tac) >> simp[]) >>
      `ALOOKUP kvs j = SOME v` by
        metis_tac[alistTheory.ALOOKUP_ALL_DISTINCT_MEM] >>
      first_x_assum (qspec_then `j` mp_tac) >> asm_rewrite_tac [] >> simp[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> asm_rewrite_tac [] >> simp[]
QED

Theorem place_store_sparse_rebuild[local]:
  !kvs tv n b mem mem' i child.
    value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) b mem /\
    i < n /\ val_in_memory tv child (b+i*type_memory_size tv) mem' /\
    (!q. q < b+i*type_memory_size tv \/
         b+i*type_memory_size tv+type_memory_size tv <= q ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    val_in_memory (ArrayTV tv (Fixed n))
      (ArrayV (SArrayV (if child = default_value tv then ADELKEY i kvs
                       else insert_sarray i child kvs))) b mem'
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `ks = if child = default_value tv then ADELKEY i kvs
                   else insert_sarray i child kvs` >>
  `SORTED $< (MAP FST ks)` by
    (gvs[value_has_type_def, Abbr `ks`] >> IF_CASES_TAC >>
     simp[vyperAssignPreservesTypeTheory.ADELKEY_SORTED,
          vyperAssignPreservesTypeTheory.insert_sarray_SORTED]) >>
  `!j. MEM j (MAP FST kvs) ==> j < n` by
    (gvs[value_has_type_def] >> drule sparse_has_type_all_less >>
     simp[EVERY_MEM, MEM_MAP, pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >>
     metis_tac[]) >>
  `!j. MEM j (MAP FST ks) ==> j < n` by
    (simp[Abbr `ks`] >> IF_CASES_TAC
     >- (simp[alistTheory.ADELKEY_def, MEM_MAP, MEM_FILTER, pairTheory.EXISTS_PROD] >>
         metis_tac[MEM_MAP, pairTheory.FST]) >>
     simp[vyperAssignPreservesTypeTheory.MEM_MAP_FST_insert_sarray] >>
     metis_tac[]) >>
  `array_set_index (ArrayTV tv (Fixed n)) (SArrayV kvs) (&i) child =
     INL (ArrayV (SArrayV ks))` by
    simp[vyperValueOperationTheory.array_set_index_def, Abbr `ks`] >>
  `!j. j < n ==>
     (case ALOOKUP ks j of NONE => default_value tv | SOME v => v) =
     if j = i then child else
       (case ALOOKUP kvs j of NONE => default_value tv | SOME v => v)` by
    (rpt strip_tac >> Cases_on `j = i` >> gvs[]
     >- (drule vyperArrayTheory.array_index_after_set_same >>
         simp[vyperValueOperationTheory.array_index_def] >>
         Cases_on `ALOOKUP ks i` >> simp[]) >>
     drule_at (Pat `array_set_index _ _ _ _ = _`)
       vyperArrayTheory.array_index_after_set_other >>
     disch_then (qspec_then `&j` mp_tac) >>
     simp[vyperValueOperationTheory.array_index_def] >>
     Cases_on `ALOOKUP ks j` >> Cases_on `ALOOKUP kvs j` >> simp[]) >>
  `ALL_DISTINCT (MAP FST ks)` by metis_tac[SORTED_lt_ALL_DISTINCT] >>
  `EVERY (\kv. FST kv < n) ks` by
    (simp[EVERY_MEM] >> metis_tac[MEM_MAP]) >>
  asm_simp_tac std_ss [place_store_sparse_indexed] >>
  qx_gen_tac `j` >> strip_tac >>
  qpat_x_assum `!j. j < n ==> _ = _` (qspec_then `j` mp_tac) >>
  asm_rewrite_tac [] >> disch_then SUBST1_TAC >>
  Cases_on `j = i` >- asm_rewrite_tac [] >> asm_rewrite_tac [] >>
  `value_has_type tv (case ALOOKUP kvs j of NONE => default_value tv | SOME v => v) /\
   val_in_memory tv (case ALOOKUP kvs j of NONE => default_value tv | SOME v => v)
     (b+j*type_memory_size tv) mem` by
    (Cases_on `ALOOKUP kvs j` >> gvs[value_has_type_def, val_in_memory_sarray]
     >- simp[place_store_default_typed] >>
     drule_all place_store_sparse_read >> simp[]) >>
  irule place_store_index_frame >> conj_tac >- asm_rewrite_tac [] >>
  qexistsl_tac [`i`, `mem`] >> asm_rewrite_tac []
QED

Theorem place_store_step_rebuild:
  !tv sub k ctv a a' child b mem mem'.
    mem_step_offset tv sub = SOME (k,ctv) /\ value_has_type tv a /\
    val_in_memory tv a b mem /\
    assign_subscripts tv a [sub] (Replace child) = INL a' /\
    val_in_memory ctv child (b+k) mem' /\
    (!q. q < b+k \/ b+k+type_memory_size ctv <= q ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    val_in_memory tv a' b mem'
Proof
  rpt gen_tac >> strip_tac >>
  drule mem_step_offset_shape >> strip_tac >> gvs[]
  >- (Cases_on `a` >>
      gvs[value_has_type_def, assign_subscripts_def, AllCaseEqs()] >>
      simp[val_in_memory_def] >> irule place_store_fields_rebuild >>
      conj_tac >- asm_rewrite_tac [] >>
      qexistsl_tac [`k`, `mem`, `ctv`] >>
      asm_rewrite_tac [GSYM ADD_ASSOC] >>
      gvs[val_in_memory_def]) 
  >- (Cases_on `a` >> gvs[value_has_type_def] >>
      rename1 `val_in_memory _ (ArrayV av) b mem` >> Cases_on `av` >>
      gvs[value_has_type_def, assign_subscripts_def,
          vyperValueOperationTheory.array_index_def, AllCaseEqs()] >>
      gvs[vyperValueOperationTheory.array_set_index_def] >>
      `Num i * type_memory_size ctv + type_memory_size ctv =
       type_memory_size ctv + Num i * type_memory_size ctv` by
        metis_tac[ADD_COMM] >>
      irule place_store_sparse_rebuild >>
      asm_rewrite_tac [value_has_type_def] >> qexists_tac `mem` >>
      asm_rewrite_tac [GSYM ADD_ASSOC])
  >- (Cases_on `a` >> gvs[value_has_type_def] >>
      rename1 `val_in_memory _ (ArrayV av) b mem` >> Cases_on `av` >>
      gvs[value_has_type_def, assign_subscripts_def,
          vyperValueOperationTheory.array_index_def, AllCaseEqs()] >>
      gvs[vyperValueOperationTheory.array_set_index_def, AllCaseEqs()] >>
      `!vs:value list. !j v. j < LENGTH vs ==>
         TAKE j vs ++ [v] ++ DROP (SUC j) vs = LUPDATE v j vs` by
        (Induct >> simp[] >> rpt gen_tac >> Cases_on `j` >>
         simp[LUPDATE_DEF]) >>
      qpat_x_assum `!vs j v. _`
        (qspecl_then [`l`, `Num i`, `child`] mp_tac) >>
      asm_rewrite_tac [] >> disch_then SUBST1_TAC >>
      `b+32+Num i*type_memory_size ctv =
       b+(Num i*type_memory_size ctv+32)` by
        metis_tac[ADD_ASSOC, ADD_COMM] >>
      `b+32+Num i*type_memory_size ctv+type_memory_size ctv =
       b+(type_memory_size ctv+(Num i*type_memory_size ctv+32))` by
        metis_tac[ADD_ASSOC, ADD_COMM] >>
      irule place_store_dynarray_rebuild >>
      asm_rewrite_tac [value_has_type_def] >> qexists_tac `mem` >>
      asm_rewrite_tac []) >>
  Cases_on `a` >> gvs[value_has_type_def] >>
      rename1 `val_in_memory _ (ArrayV av) b mem` >> Cases_on `av` >>
  gvs[value_has_type_def, assign_subscripts_def,
      vyperValueOperationTheory.array_index_def,
      vyperValueOperationTheory.array_set_index_def, AllCaseEqs()]
QED

Theorem place_store_dynarray_prefix_frame:
  !et n vs b mem mem'.
    val_in_memory (ArrayTV et (Dynamic n)) (ArrayV (DynArrayV vs)) b mem /\
    val_wf (ArrayTV et (Dynamic n)) (ArrayV (DynArrayV vs)) /\
    mem_bytes_at b (32 + LENGTH vs * type_memory_size et) mem =
      mem_bytes_at b (32 + LENGTH vs * type_memory_size et) mem' ==>
    val_in_memory (ArrayTV et (Dynamic n)) (ArrayV (DynArrayV vs)) b mem'
Proof
  rpt gen_tac >> simp[val_in_memory_def, val_wf_def] >> strip_tac >>
  drule mem_bytes_at_agree_window >> strip_tac >> conj_tac
  >- (qpat_x_assum `!off2. _` (qspec_then `b` mp_tac) >> simp[]) >>
  irule place_store_elements_prefix_frame >> simp[] >>
  qexists_tac `mem` >> simp[] >> sym_tac >>
  first_x_assum irule >> simp[]
QED

Theorem place_store_tuple_read_frame[local]:
  !vs tvs i b mem mem'.
    values_have_types tvs vs /\ tuple_in_memory vs tvs b mem /\
    i < LENGTH tvs /\
    val_in_memory (EL i tvs) (EL i vs)
      (b + type_memory_size_list (TAKE i tvs)) mem' /\
    (!q. q < b + type_memory_size_list (TAKE i tvs) \/
         b + type_memory_size_list (TAKE i tvs) +
           type_memory_size (EL i tvs) <= q ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    tuple_in_memory vs tvs b mem'
Proof
  Induct >> Cases_on `tvs` >> simp[value_has_type_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `i` >>
  gvs[val_in_memory_def, type_memory_size_def]
  >- (`val_in_memory (TupleTV t) (ArrayV (TupleV vs))
         (b + type_memory_size h) mem'` suffices_by
        simp[val_in_memory_def] >>
      irule place_store_value_frame >>
      conj_tac >- simp[value_has_type_def] >>
      qexistsl_tac [`b + type_memory_size h`, `b`, `mem`] >>
      asm_rewrite_tac [val_in_memory_def] >> simp[]) >>
  conj_tac
  >- (irule place_store_value_frame >> conj_tac >- asm_rewrite_tac [] >>
      qexistsl_tac
        [`b + (type_memory_size h + type_memory_size_list (TAKE n t)) +
           type_memory_size (EL n t)`,
         `b + (type_memory_size h + type_memory_size_list (TAKE n t))`,
         `mem`] >> simp[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
  first_x_assum irule >> conj_tac >- asm_rewrite_tac [] >>
  qexistsl_tac [`n`, `mem`] >>
  fs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]
QED

Theorem place_store_afupd_read[local]:
  !al id v. ALOOKUP al id = SOME v ==> AFUPDKEY id (K v) al = al
Proof
  Induct >> simp[alistTheory.ALOOKUP_def] >> PairCases >>
  simp[alistTheory.ALOOKUP_def, alistTheory.AFUPDKEY_def] >>
  rpt gen_tac >> Cases_on `h0 = id` >> simp[]
QED

Theorem place_store_sparse_read_frame[local]:
  !kvs tv n b mem mem' i.
    value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) b mem /\
    i < n /\ val_in_memory tv
      (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
      (b+i*type_memory_size tv) mem' /\
    (!q. q < b+i*type_memory_size tv \/
         b+i*type_memory_size tv+type_memory_size tv <= q ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) b mem'
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP FST kvs)` by
    (gvs[value_has_type_def] >> metis_tac[SORTED_lt_ALL_DISTINCT]) >>
  `EVERY (\kv. FST kv < n) kvs` by
    (gvs[value_has_type_def] >> drule sparse_has_type_all_less >>
     simp[EVERY_MEM, MEM_MAP, pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >>
     metis_tac[]) >>
  asm_simp_tac std_ss [place_store_sparse_indexed] >>
  qx_gen_tac `j` >> strip_tac >> Cases_on `j = i` >- gvs[] >>
  `value_has_type tv (case ALOOKUP kvs j of NONE => default_value tv | SOME v => v) /\
   val_in_memory tv (case ALOOKUP kvs j of NONE => default_value tv | SOME v => v)
     (b+j*type_memory_size tv) mem` by
    (Cases_on `ALOOKUP kvs j` >> gvs[value_has_type_def, val_in_memory_sarray]
     >- simp[place_store_default_typed] >>
     drule_all place_store_sparse_read >> simp[]) >>
  irule place_store_index_frame >> conj_tac >- asm_rewrite_tac [] >>
  qexistsl_tac [`i`, `mem`] >> asm_rewrite_tac []
QED

Theorem place_store_step_read_frame:
  !tv sub k ctv a child b mem mem'.
    mem_step_offset tv sub = SOME (k,ctv) /\ value_has_type tv a /\
    val_in_memory tv a b mem /\ evaluate_subscripts tv a [sub] = INL child /\
    val_in_memory ctv child (b+k) mem' /\
    (!q. q < b+k \/ b+k+type_memory_size ctv <= q ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    val_in_memory tv a b mem'
Proof
  rpt gen_tac >> strip_tac >>
  drule mem_step_offset_shape >> strip_tac >> gvs[]
  >- (Cases_on `a` >>
      gvs[value_has_type_def, evaluate_subscripts_def, AllCaseEqs()] >>
      `assign_subscripts (StructTV fs) (StructV l) [AttrSubscript id]
         (Replace child) = INL (StructV l)` by
        (simp[assign_subscripts_def] >> metis_tac[place_store_afupd_read]) >>
      `value_has_type (StructTV fs) (StructV l)` by simp[value_has_type_def] >>
      irule place_store_step_rebuild >>
      qexists_tac `StructV l` >>
      goal_assum (drule_at (Pat `assign_subscripts _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `mem_step_offset _ _ = _`)) >>
      qexists_tac `mem` >> fs[AC ADD_ASSOC ADD_COMM] >> metis_tac[])
  >- (Cases_on `a` >> gvs[value_has_type_def] >>
      rename1 `val_in_memory _ (ArrayV av) b mem` >> Cases_on `av` >>
      gvs[value_has_type_def, evaluate_subscripts_def,
          vyperValueOperationTheory.array_index_def, AllCaseEqs()] >>
      irule place_store_sparse_read_frame >>
      asm_rewrite_tac [value_has_type_def] >>
      qexistsl_tac [`Num i`, `mem`] >>
      fs[AC ADD_ASSOC ADD_COMM] >> metis_tac[])
  >- (Cases_on `a` >> gvs[value_has_type_def] >>
      rename1 `val_in_memory _ (ArrayV av) b mem` >> Cases_on `av` >>
      gvs[value_has_type_def, evaluate_subscripts_def,
          vyperValueOperationTheory.array_index_def, AllCaseEqs()] >>
      `Num i < LENGTH l /\ EL (Num i) l = child` by
        gvs[listTheory.oEL_THM, AllCaseEqs()] >>
      `LUPDATE child (Num i) l = l` by metis_tac[LUPDATE_SAME] >>
      `val_in_memory (ArrayTV ctv (Dynamic n))
         (ArrayV (DynArrayV (LUPDATE child (Num i) l))) b mem'` suffices_by
        asm_rewrite_tac [] >>
      irule place_store_dynarray_rebuild >>
      asm_rewrite_tac [value_has_type_def] >>
      conj_tac >- fs[AC ADD_ASSOC ADD_COMM] >> qexists_tac `mem` >>
      fs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
  Cases_on `a` >> gvs[value_has_type_def] >>
  rename1 `val_in_memory _ (ArrayV av) b mem` >> Cases_on `av` >>
  gvs[value_has_type_def, evaluate_subscripts_def,
      vyperValueOperationTheory.array_index_def, val_in_memory_def, AllCaseEqs()] >>
  irule place_store_tuple_read_frame >> conj_tac >- asm_rewrite_tac [] >>
  qexistsl_tac [`Num i`, `mem`] >>
  gvs[listTheory.oEL_THM, AllCaseEqs()] >> metis_tac[]
QED

Theorem place_store_step_unread_frame:
  !tv sub k ctv a b mem mem' err.
    mem_step_offset tv sub = SOME (k,ctv) /\ value_has_type tv a /\
    val_in_memory tv a b mem /\ evaluate_subscripts tv a [sub] = INR err /\
    (!q. q < b+k \/ b+k+type_memory_size ctv <= q ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    val_in_memory tv a b mem'
Proof
  rpt gen_tac >> strip_tac >>
  drule mem_step_offset_shape >> strip_tac >> gvs[]
  >- (Cases_on `a` >>
      gvs[value_has_type_def, evaluate_subscripts_def, AllCaseEqs()] >>
      drule mem_field_offset_sound >> strip_tac >>
      drule struct_has_type_map_fst >>
      metis_tac[alistTheory.ALOOKUP_NONE, alistTheory.ALOOKUP_MEM,
                listTheory.MEM_MAP, pairTheory.FST])
  >- (Cases_on `a` >> gvs[value_has_type_def] >>
      rename1 `val_in_memory _ (ArrayV av) b mem` >> Cases_on `av` >>
      gvs[value_has_type_def, evaluate_subscripts_def,
          vyperValueOperationTheory.array_index_def, AllCaseEqs()])
  >- (Cases_on `a` >> gvs[value_has_type_def] >>
      rename1 `val_in_memory _ (ArrayV av) b mem` >> Cases_on `av` >>
      gvs[value_has_type_def, evaluate_subscripts_def,
          vyperValueOperationTheory.array_index_def, AllCaseEqs()] >>
      `LENGTH l <= Num i` by gvs[listTheory.oEL_THM, AllCaseEqs()] >>
      `LENGTH l * type_memory_size ctv <= Num i * type_memory_size ctv` by
        (irule LESS_MONO_MULT >> asm_rewrite_tac []) >>
      irule place_store_dynarray_prefix_frame >>
      conj_tac
      >- (`value_has_type (ArrayTV ctv (Dynamic n))
             (ArrayV (DynArrayV l))` by simp[value_has_type_def] >>
          metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]) >>
      qexists_tac `mem` >> asm_rewrite_tac [] >>
      irule place_store_bytes_agree >> rpt strip_tac >>
      qpat_x_assum `!q. _` irule >> decide_tac) >>
  Cases_on `a` >> gvs[value_has_type_def] >>
  rename1 `val_in_memory _ (ArrayV av) b mem` >> Cases_on `av` >>
  gvs[value_has_type_def, evaluate_subscripts_def,
      vyperValueOperationTheory.array_index_def, AllCaseEqs()] >>
  drule values_have_types_length >> gvs[listTheory.oEL_THM, AllCaseEqs()]
QED

Theorem place_store_read_cons[local]:
  !tv sub k ctv a path.
    mem_step_offset tv sub = SOME (k,ctv) ==>
    evaluate_subscripts tv a (sub::path) =
      (case evaluate_subscripts tv a [sub] of
       INL child => evaluate_subscripts ctv child path | INR err => INR err)
Proof
  rpt gen_tac >> strip_tac >>
  drule mem_step_offset_shape >> strip_tac >> gvs[] >>
  Cases_on `a` >>
  simp[evaluate_subscripts_def, subscript_type_def] >>
  imp_res_tac mem_field_offset_sound >> simp[] >>
  rpt (CASE_TAC >> simp[])
QED

Theorem place_store_path_unread_frame:
  !path tv k ltv a b mem mem' err.
    mem_path_offset tv path = SOME (k,ltv) /\ value_has_type tv a /\
    val_in_memory tv a b mem /\ evaluate_subscripts tv a path = INR err /\
    (!q. q < b+k \/ b+k+type_memory_size ltv <= q ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    val_in_memory tv a b mem'
Proof
  Induct >- simp[evaluate_subscripts_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[mem_path_offset_def, AllCaseEqs(), pairTheory.EXISTS_PROD] >>
  rename1 `mem_step_offset tv h = SOME (j,ctv)` >>
  rename1 `mem_path_offset ctv path = SOME (r,ltv)` >>
  `!q. q < b+j \/ b+j+type_memory_size ctv <= q ==>
       mem_bytes_at q 1 mem = mem_bytes_at q 1 mem'` by
    (drule mem_path_offset_sound >> strip_tac >> rpt strip_tac >>
     qpat_x_assum `!q. _` irule >> decide_tac) >>
  drule place_store_read_cons >>
  disch_then (qspecl_then [`a`, `path`] mp_tac) >>
  Cases_on `evaluate_subscripts tv a [h]` >> gvs[] >> strip_tac
  >- (drule_all place_store_step_read >> strip_tac >>
      `val_in_memory ctv x (b+j) mem'` by
        (first_x_assum irule >> goal_assum (drule_at Any) >>
         conj_tac >- metis_tac[] >>
         qexistsl_tac [`r`, `ltv`, `mem`] >> fs[AC ADD_ASSOC ADD_COMM] >>
         metis_tac[]) >>
      irule place_store_step_read_frame >>
      conj_tac >- asm_rewrite_tac [] >>
      goal_assum (drule_at (Pat `evaluate_subscripts _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `mem_step_offset _ _ = _`)) >>
      qexists_tac `mem` >> fs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
  irule place_store_step_unread_frame >> conj_tac >- asm_rewrite_tac [] >>
  goal_assum (drule_at (Pat `evaluate_subscripts _ _ _ = INR _`)) >>
  goal_assum (drule_at (Pat `mem_step_offset _ _ = _`)) >>
  qexists_tac `mem` >> fs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]
QED

Theorem place_store_assign_cons[local]:
  !tv sub k ctv a old path v.
    mem_step_offset tv sub = SOME (k,ctv) /\
    evaluate_subscripts tv a [sub] = INL old ==>
    assign_subscripts tv a (sub::path) (Replace v) =
      (case assign_subscripts ctv old path (Replace v) of
       INL child => assign_subscripts tv a [sub] (Replace child)
       | INR err => INR err)
Proof
  rpt gen_tac >> strip_tac >>
  drule mem_step_offset_shape >> strip_tac >> gvs[]
  >- (drule mem_field_offset_sound >> strip_tac >>
      Cases_on `a` >>
      gvs[evaluate_subscripts_def, assign_subscripts_def, AllCaseEqs()] >>
      Cases_on `assign_subscripts ctv old path (Replace v)` >> simp[]) >>
  Cases_on `a` >>
  gvs[evaluate_subscripts_def, assign_subscripts_def, subscript_type_def,
      AllCaseEqs()] >>
  qmatch_goalsub_abbrev_tac `assign_subscripts et old path (Replace v)` >>
  Cases_on `assign_subscripts et old path (Replace v)` >> simp[]
QED

Theorem place_store_path_assign:
  !path tv k ltv a b mem mem' v old result.
    mem_path_offset tv path = SOME (k,ltv) /\ value_has_type tv a /\
    val_in_memory tv a b mem /\ value_has_type ltv v /\
    val_in_memory ltv v (b+k) mem' /\
    evaluate_subscripts tv a path = INL old /\
    assign_subscripts tv a path (Replace v) = INL result /\
    (!q. q < b+k \/ b+k+type_memory_size ltv <= q ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    val_in_memory tv result b mem'
Proof
  Induct >- simp[mem_path_offset_def, assign_subscripts_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[mem_path_offset_def, AllCaseEqs(), pairTheory.EXISTS_PROD] >>
  rename1 `mem_step_offset tv h = SOME (j,ctv)` >>
  rename1 `mem_path_offset ctv path = SOME (r,ltv)` >>
  `!q. q < b+j \/ b+j+type_memory_size ctv <= q ==>
       mem_bytes_at q 1 mem = mem_bytes_at q 1 mem'` by
    (drule mem_path_offset_sound >> strip_tac >> rpt strip_tac >>
     qpat_x_assum `!q. _` irule >> decide_tac) >>
  drule place_store_read_cons >>
  disch_then (qspecl_then [`a`, `path`] mp_tac) >>
  Cases_on `evaluate_subscripts tv a [h]` >> gvs[] >> strip_tac
  >- (drule_all place_store_step_read >> strip_tac >>
      drule_all place_store_assign_cons >>
      disch_then (qspecl_then [`path`, `v`] mp_tac) >>
      Cases_on `assign_subscripts ctv x path (Replace v)` >> gvs[] >>
      strip_tac >>
      `val_in_memory ctv x' (b+j) mem'` by
        (first_x_assum irule >>
         goal_assum (drule_at (Pat `assign_subscripts _ _ _ _ = _`)) >>
         goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
         qexistsl_tac [`mem`, `old`] >>
         fs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
      irule place_store_step_rebuild >> qexists_tac `a` >>
      goal_assum (drule_at (Pat `mem_step_offset _ _ = _`)) >>
      goal_assum (drule_at (Pat `val_in_memory _ _ _ mem'`)) >>
      qexists_tac `mem` >> fs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
  gvs[]
QED

Theorem place_store_replace_memory_entry:
  !entry path v entry' k ltv b mem mem'.
    mem_path_offset entry.type path = SOME (k,ltv) /\
    value_has_type entry.type entry.value /\
    val_in_memory entry.type entry.value b mem /\ value_has_type ltv v /\
    val_in_memory ltv v (b+k) mem' /\
    replace_memory_entry entry path v = INL entry' /\
    (!q. q < b+k \/ b+k+type_memory_size ltv <= q ==>
         mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') ==>
    entry'.type = entry.type /\ val_in_memory entry'.type entry'.value b mem'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[replace_memory_entry_def, AllCaseEqs()]
  >- (irule place_store_path_assign >>
      goal_assum (drule_at (Pat `assign_subscripts _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
      goal_assum (drule_at (Pat `evaluate_subscripts _ _ _ = _`)) >>
      qexists_tac `mem` >> fs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
  irule place_store_path_unread_frame >> conj_tac >- asm_rewrite_tac [] >>
  goal_assum (drule_at (Pat `evaluate_subscripts _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
  qexists_tac `mem` >> fs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]
QED

Theorem place_store_local_ptrs_replace:
  !func cenv sc sc' s mem' id path v entry entry' p sz bw k tv.
    local_ptrs_rel func cenv sc s /\
    lookup_scopes id sc = SOME entry /\
    lookup_scopes id sc' = SOME entry' /\
    (!n. n <> id ==> lookup_scopes n sc' = lookup_scopes n sc) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME bw /\
    mem_path_offset entry.type path = SOME (k,tv) /\
    value_has_type entry.type entry.value /\ value_has_type tv v /\
    replace_memory_entry entry path v = INL entry' /\
    val_wf entry'.type entry'.value /\
    val_in_memory tv v (w2n bw+k) mem' /\
    (!q. q < w2n bw+k \/ w2n bw+k+type_memory_size tv <= q ==>
         mem_bytes_at q 1 s.vs_memory = mem_bytes_at q 1 mem') ==>
    local_ptrs_rel func cenv sc' (s with vs_memory := mem')
Proof
  rpt gen_tac >> strip_tac >>
  `local_region cenv sc s id (w2n bw) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `local_backed func p s (w2n bw) sz /\
   w2n bw + sz <= s.vs_alloca_next /\
   type_memory_size entry.type <= sz /\
   val_in_memory entry.type entry.value (w2n bw) s.vs_memory` by
    (fs[local_ptrs_rel_def] >>
     first_x_assum drule_all >> simp[] >> metis_tac[]) >>
  `entry'.type = entry.type /\
   val_in_memory entry'.type entry'.value (w2n bw) mem'` by
    (drule_all place_store_replace_memory_entry >> simp[]) >>
  `!n b sz'. n <> id /\ local_region cenv sc s n b sz' ==>
       regions_disjoint (w2n bw) sz b sz'` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  drule mem_path_offset_sound >> strip_tac >>
  `!n b sz'. n <> id /\ local_region cenv sc s n b sz' ==>
       mem_bytes_at b sz' s.vs_memory = mem_bytes_at b sz' mem'` by
    (rpt strip_tac >> irule place_store_bytes_agree >> rpt strip_tac >>
     qpat_x_assum `!q. _ ==> mem_bytes_at q 1 _ = _` irule >>
     `regions_disjoint (w2n bw) sz b sz'` by metis_tac[] >>
     fs[regions_disjoint_def] >> decide_tac) >>
  irule local_ptrs_rel_write_local >>
  qexistsl_tac [`entry'`, `id`, `p`, `sc`, `s`, `sz`, `bw`] >>
  gvs[lookup_var_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem place_store_word_representation:
  !tenv dty tv v a mem.
    is_word_type dty /\ evaluate_type tenv dty = SOME tv /\
    value_has_type tv v /\
    mem_word_at a mem = typed_val_to_w256 tv v ==>
    val_in_memory tv v a mem
Proof
  Cases_on `dty` >> simp[is_word_type_def, evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, typed_val_to_w256_def,
      is_word_type_def]
QED

Theorem place_store_empty_representation:
  !tenv dty tv a mem.
    has_length_word dty /\ evaluate_type tenv dty = SOME tv /\
    mem_word_at a mem = 0w ==>
    val_in_memory tv (default_value tv) a mem /\
    32 <= type_memory_size tv
Proof
  Cases_on `dty` >>
  simp[has_length_word_def, is_bytestring_type_def, evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[is_bytestring_type_def, has_length_word_def] >>
  simp[default_value_def, val_in_memory_def, type_memory_size_def] >>
  simp[mem_bytes_at_def] >>
  Cases_on `b` >>
  gvs[has_length_word_def, is_bytestring_type_def, default_value_def,
      val_in_memory_def, type_memory_size_def]
QED

Theorem place_store_local_immutables_frame:
  !ctx func cenv cx es s t id b sz.
    stmt_state_rel ctx func cenv cx es s /\
    local_region cenv es.scopes s id b sz /\
    t.vs_data_section = s.vs_data_section /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!q. q < b \/ b+sz <= q ==>
         mem_bytes_at q 1 s.vs_memory = mem_bytes_at q 1 t.vs_memory) ==>
    immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t
Proof
  rpt gen_tac >> strip_tac >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s /\
   immutable_alloca_sep func cenv cx es s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  Cases_on `cenv.ce_is_ctor`
  >- (fs[immutables_rel_def, immutable_alloca_sep_def] >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!name tv v byte_offset. _ ==> immutable_value_admissible _ _ /\ _` drule_all >>
      strip_tac >>
      `regions_disjoint byte_offset (type_memory_size tv) b sz` by
        metis_tac[] >>
      `mem_bytes_at byte_offset (type_memory_size tv) s.vs_memory =
       mem_bytes_at byte_offset (type_memory_size tv) t.vs_memory` by
        (irule place_store_bytes_agree >> rpt strip_tac >>
         qpat_x_assum `!q. _ ==> mem_bytes_at q 1 _ = _` irule >>
         fs[regions_disjoint_def] >> decide_tac) >>
      `val_in_memory tv v byte_offset t.vs_memory` by
        (irule val_in_memory_mem_agree >>
         conj_tac >- metis_tac[loweringSliceTheory.immutable_admissible_val_wf] >>
         qexistsl_tac [`type_memory_size tv`, `s.vs_memory`] >>
         simp[]) >>
      metis_tac[]) >>
  fs[immutables_rel_def] >> metis_tac[]
QED

Theorem place_store_scalar_dead_bytes:
  !ty tenv leaf.
    is_word_type ty /\ evaluate_type tenv ty = SOME leaf ==>
    type_slot_size leaf = 1 /\
    (!st base j b. ~dead_bytes st base leaf j b)
Proof
  Cases_on `ty` >> simp[is_word_type_def, evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[is_word_type_def, dead_bytes_def, type_slot_size_def]
QED

Theorem place_store_dead_bytes_update_frame[local]:
  !tv base slot u st j b.
    base + type_slot_size tv <= dimword (:256) /\
    slot < dimword (:256) /\
    (slot < base \/ base + type_slot_size tv <= slot) ==>
    (dead_bytes (update_storage (n2w slot) u st) base tv j b <=>
     dead_bytes st base tv j b)
Proof
  rpt strip_tac >> irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
  `i < dimword (:256)` by decide_tac >>
  `i <> slot` by decide_tac >>
  simp[vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM, wordsTheory.n2w_11]
QED

Theorem place_store_array_dead_children[local]:
  !tv n idx base rest u st j b.
    idx < n /\ rest < type_slot_size tv /\
    base + n * type_slot_size tv <= dimword (:256) /\
    (dead_bytes (update_storage (n2w (base + idx * type_slot_size tv + rest)) u st)
       (base + idx * type_slot_size tv) tv j b <=>
     dead_bytes st (base + idx * type_slot_size tv) tv j b) ==>
    !a. a < n ==>
    (dead_bytes (update_storage (n2w (base + idx * type_slot_size tv + rest)) u st)
       (base + a * type_slot_size tv) tv j b <=>
     dead_bytes st (base + a * type_slot_size tv) tv j b)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `a = idx` >- gvs[] >>
  `idx * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `a * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  irule place_store_dead_bytes_update_frame >> simp[] >>
  Cases_on `idx < a`
  >- (`idx * type_slot_size tv + type_slot_size tv <= a * type_slot_size tv` by
        (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
      decide_tac) >>
  `a < idx` by decide_tac >>
  `a * type_slot_size tv + type_slot_size tv <= idx * type_slot_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  decide_tac
QED

Theorem place_store_dead_list_split[local]:
  !pre post st base j b.
    dead_bytes_list st base (pre ++ post) j b <=>
    dead_bytes_list st base pre j b \/
    dead_bytes_list st (base + type_slot_size_list pre) post j b
Proof
  Induct >> asm_simp_tac std_ss [APPEND, dead_bytes_def, type_slot_size_def,
                                arithmeticTheory.ADD_ASSOC, DISJ_ASSOC]
QED

Theorem place_store_dead_fields_list[local]:
  !fs st base j b.
    dead_bytes_fields st base fs j b <=>
    dead_bytes_list st base (MAP SND fs) j b
Proof
  Induct >> simp[dead_bytes_def] >> Cases_on `h` >> simp[dead_bytes_def]
QED

Theorem place_store_dead_list_as_tuple[local]:
  !st base tvs j b.
    dead_bytes st base (TupleTV tvs) j b = dead_bytes_list st base tvs j b
Proof
  simp[dead_bytes_def]
QED

Theorem place_store_list_dead_child[local]:
  !pre elem post base rest u st j b.
    rest < type_slot_size elem /\
    base + type_slot_size_list (pre ++ elem::post) <= dimword (:256) /\
    (dead_bytes (update_storage (n2w (base + type_slot_size_list pre + rest)) u st)
       (base + type_slot_size_list pre) elem j b <=>
     dead_bytes st (base + type_slot_size_list pre) elem j b) ==>
    (dead_bytes_list (update_storage (n2w (base + type_slot_size_list pre + rest)) u st)
       base (pre ++ elem::post) j b <=>
     dead_bytes_list st base (pre ++ elem::post) j b)
Proof
  rpt gen_tac >> strip_tac >>
  `type_slot_size_list (pre ++ elem::post) =
   type_slot_size_list pre + type_slot_size elem + type_slot_size_list post` by
    simp[vyperStorageRegionWriteTheory.type_slot_size_list_sum, SUM_APPEND] >>
  `dead_bytes_list (update_storage (n2w (base' + type_slot_size_list pre + rest)) u st)
     base' pre j b <=> dead_bytes_list st base' pre j b` by
    (pure_rewrite_tac[GSYM place_store_dead_list_as_tuple] >>
     irule place_store_dead_bytes_update_frame >>
     simp[type_slot_size_def] >> decide_tac) >>
  `dead_bytes_list (update_storage (n2w (base' + type_slot_size_list pre + rest)) u st)
     (base' + type_slot_size_list pre + type_slot_size elem) post j b <=>
   dead_bytes_list st (base' + type_slot_size_list pre + type_slot_size elem) post j b` by
    (pure_rewrite_tac[GSYM place_store_dead_list_as_tuple] >>
     irule place_store_dead_bytes_update_frame >>
     simp[type_slot_size_def] >> decide_tac) >>
  simp[place_store_dead_list_split, dead_bytes_def]
QED

Theorem place_store_subregion_dead_bytes:
  !root path off leaf.
    storage_subregion root path off leaf ==>
    !ty tenv base u st j b.
      is_word_type ty /\ evaluate_type tenv ty = SOME leaf /\
      base + type_slot_size root <= dimword (:256) ==>
      (dead_bytes (update_storage (n2w (base+off)) u st) base root j b <=>
       dead_bytes st base root j b)
Proof
  ho_match_mp_tac storage_subregion_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  fs[Once storage_subregion_def] >> rpt gen_tac >> strip_tac
  >- (drule_all place_store_scalar_dead_bytes >> simp[]) >>
  FIRST [rename1 `dead_bytes _ _ (ArrayTV _ (Fixed _)) _ _` >> suspend "fixed",
         rename1 `dead_bytes _ _ (ArrayTV _ (Dynamic _)) _ _` >> suspend "dynamic",
         rename1 `dead_bytes _ _ (StructTV _) _ _` >> suspend "struct",
         rename1 `dead_bytes _ _ (TupleTV _) _ _` >> suspend "tuple"]
QED

Resume place_store_subregion_dead_bytes[fixed]:
  rpt gen_tac >> strip_tac >>
  drule_all place_store_scalar_dead_bytes >> strip_tac >>
  drule_all storage_subregion_bounds >> strip_tac >>
  gvs[type_slot_size_def] >>
  `Num i * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `!a. a < n ==>
    (dead_bytes (update_storage (n2w (base' + (rest + Num i * type_slot_size root))) u st)
      (base' + a * type_slot_size root) root j b <=>
     dead_bytes st (base' + a * type_slot_size root) root j b)` by
    (`base' + (rest + Num i * type_slot_size root) =
      base' + Num i * type_slot_size root + rest` by decide_tac >>
     asm_rewrite_tac [] >> match_mp_tac place_store_array_dead_children >>
     asm_rewrite_tac [] >> conj_tac >- decide_tac >>
     first_x_assum drule >> disch_then irule >>
     conj_tac >- decide_tac >> goal_assum (drule_at Any) >> simp[]) >>
  pure_rewrite_tac[dead_bytes_def] >>
  qpat_x_assum `!a. a < n ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
Resume place_store_subregion_dead_bytes[dynamic]:
  rpt gen_tac >> strip_tac >>
  drule_all place_store_scalar_dead_bytes >> strip_tac >>
  drule_all storage_subregion_bounds >> strip_tac >>
  gvs[type_slot_size_def] >>
  `Num i * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `base' + (rest + (Num i * type_slot_size root + 1)) =
   (base' + 1) + Num i * type_slot_size root + rest` by decide_tac >>
  asm_rewrite_tac [] >>
  `!a. a < n ==>
    (dead_bytes (update_storage (n2w ((base' + 1) + Num i * type_slot_size root + rest)) u st)
      ((base' + 1) + a * type_slot_size root) root j b <=>
     dead_bytes st ((base' + 1) + a * type_slot_size root) root j b)` by
    (match_mp_tac place_store_array_dead_children >>
     asm_rewrite_tac [] >> rpt conj_tac >- decide_tac >- decide_tac >>
     first_x_assum drule >> disch_then irule >>
     conj_tac >- decide_tac >> goal_assum (drule_at Any) >> simp[]) >>
  `lookup_storage (n2w base')
    (update_storage (n2w ((base' + 1) + Num i * type_slot_size root + rest)) u st) =
   lookup_storage (n2w base') st` by
    (`base' < dimword (:256)` by decide_tac >>
     `(base' + 1) + Num i * type_slot_size root + rest < dimword (:256)` by decide_tac >>
     qpat_x_assum `base' + (rest + _) = _` kall_tac >>
     simp[vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
          combinTheory.APPLY_UPDATE_THM, wordsTheory.n2w_11]) >>
  pure_rewrite_tac[dead_bytes_def] >> asm_rewrite_tac [] >>
  qpat_x_assum `!a. a < n ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
Resume place_store_subregion_dead_bytes[struct]:
  rpt gen_tac >> strip_tac >>
  drule_all place_store_scalar_dead_bytes >> strip_tac >>
  drule_all storage_subregion_bounds >> strip_tac >>
  drule vyperPlaceTypingTheory.struct_field_slot_offset >> strip_tac >>
  gvs[GSYM vyperStorageRegionWriteTheory.type_slot_size_list_sum,
      vyperStorageRegionWriteTheory.type_slot_size_fields_list, type_slot_size_def,
      dead_bytes_def, place_store_dead_fields_list, MAP_APPEND, combinTheory.o_DEF] >>
  `SUM (MAP (\x. type_slot_size (SND x)) pre) =
   type_slot_size_list (MAP SND pre)` by
    simp[vyperStorageRegionWriteTheory.type_slot_size_list_sum, listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  `base' + (rest + SUM (MAP (\x. type_slot_size (SND x)) pre)) =
   base' + type_slot_size_list (MAP SND pre) + rest` by decide_tac >>
  pure_asm_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  irule place_store_list_dead_child >>
  asm_rewrite_tac [] >> conj_tac >- decide_tac >>
  first_x_assum drule >> disch_then irule >>
  conj_tac
  >- (qpat_x_assum `base' + type_slot_size_list _ <= _` mp_tac >>
      simp[vyperStorageRegionWriteTheory.type_slot_size_list_sum, SUM_APPEND] >> decide_tac) >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume place_store_subregion_dead_bytes[tuple]:
  rpt gen_tac >> strip_tac >>
  drule_all place_store_scalar_dead_bytes >> strip_tac >>
  drule_all storage_subregion_bounds >> strip_tac >>
  drule vyperStorageRegionWriteTheory.tuple_component_region_split >> strip_tac >>
  gvs[type_slot_size_def, dead_bytes_def] >>
  `base' + (rest + type_slot_size_list pre) =
   base' + type_slot_size_list pre + rest` by decide_tac >>
  pure_asm_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  irule place_store_list_dead_child >>
  asm_rewrite_tac [] >> conj_tac >- decide_tac >>
  first_x_assum drule >> disch_then irule >>
  conj_tac
  >- (qpat_x_assum `base' + type_slot_size_list _ <= _` mp_tac >>
      simp[vyperStorageRegionWriteTheory.type_slot_size_list_sum, SUM_APPEND] >> decide_tac) >>
  goal_assum (drule_at Any) >> simp[]
QED
Finalise place_store_subregion_dead_bytes

Theorem place_store_scalar_storage_dead:
  !cx tr k leaf ty tenv u st.
    storage_place_region cx (StoragePlace tr k leaf) /\
    is_word_type ty /\ evaluate_type tenv ty = SOME leaf ==>
    storage_dead cx tr (update_storage k u st) = storage_dead cx tr st
Proof
  rpt gen_tac >> strip_tac >>
  gvs[storage_place_region_def] >>
  irule storage_dead_update_in_region >>
  goal_assum (drule_at Any) >> strip_tac >>
  drule_all place_store_scalar_dead_bytes >> strip_tac >>
  drule_all storage_subregion_bounds >> strip_tac >>
  `w2n root + delta < dimword (:256)` by decide_tac >>
  `root + n2w delta = n2w (w2n root + delta)` by
    rewrite_tac[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  `w2n (root + n2w delta) = w2n root + delta` by
    (asm_rewrite_tac [] >> simp[wordsTheory.w2n_n2w]) >>
  asm_rewrite_tac [] >> conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  rpt gen_tac >> irule place_store_subregion_dead_bytes >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >> goal_assum (drule_at Any)
QED

Theorem place_store_memory_state:
  !ctx func cenv cx ee ff s id path v entry p sz bw k tv mem'.
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
    lookup_scopes id ee.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME bw /\
    mem_path_offset entry.type path = SOME (k,tv) /\
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
    value_has_type tv v /\ val_in_memory tv v (w2n bw+k) mem' /\
    LENGTH s.vs_memory <= LENGTH mem' /\
    (!q. q < w2n bw+k \/ w2n bw+k+type_memory_size tv <= q ==>
         mem_bytes_at q 1 s.vs_memory = mem_bytes_at q 1 mem') ==>
    stmt_state_rel ctx func cenv cx ff (s with vs_memory := mem')
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `find_containing_scope id ee.scopes` >>
  gvs[write_place_def, vyperStateTheory.bind_def, get_scopes_def,
      lift_option_type_def, vyperStateTheory.return_def, raise_def] >>
  PairCases_on `x` >>
  gvs[vyperStateTheory.bind_def, ignore_bind_def, lift_sum_def,
      type_check_def, assert_def, set_scopes_def,
      vyperStateTheory.return_def, raise_def, AllCaseEqs()] >>
  Cases_on `replace_memory_entry x2 path v` >>
  gvs[vyperStateTheory.return_def, raise_def] >>
  drule find_containing_scope_lookup >> strip_tac >> gvs[] >>
  drule find_containing_scope_structure >> strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >>
  qmatch_goalsub_abbrev_tac `ee with scopes := sc'` >>
  `lookup_scopes id sc' = SOME entry' /\
   (!n. n <> id ==> lookup_scopes n sc' = lookup_scopes n ee.scopes)` by
    (simp[Abbr `sc'`] >> metis_tac[lookup_scopes_update,
                                              lookup_scopes_update_other]) >>
  drule mem_path_offset_sound >> strip_tac >>
  `value_has_type entry'.type entry'.value` by
    metis_tac[replace_memory_entry_value_type] >>
  `val_wf entry'.type entry'.value` by metis_tac[value_has_type_val_wf] >>
  `local_ptrs_rel func cenv ee.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `local_ptrs_rel func cenv sc' (s with vs_memory := mem')` by
    (irule place_store_local_ptrs_replace >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `local_region cenv ee.scopes s id (w2n bw) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor
     ee (s with vs_memory := mem')` by
    (irule place_store_local_immutables_frame >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`ctx`, `func`] >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `entry'.type = entry.type` by metis_tac[replace_memory_entry_type] >>
  `!n b z. local_region cenv sc' (s with vs_memory := mem') n b z ==>
            local_region cenv ee.scopes s n b z` by
    (rpt gen_tac >> Cases_on `n = id` >>
     gvs[local_region_def, lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `ee.scopes = _` kall_tac >>
  `immutable_alloca_sep func cenv cx (ee with scopes := sc')
     (s with vs_memory := mem')` by
    (irule immutable_alloca_sep_fields >>
     qexistsl_tac [`s`, `ee`] >> simp[] >>
     fs[stmt_state_rel_def] >> metis_tac[]) >>
  irule stmt_state_rel_allocas_frame >>
  simp[] >>
  conj_tac
  >- (fs[stmt_state_rel_def, immutable_base_zero_def] >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!x. cenv.ce_imm_alloca = SOME x ==> _` drule >>
      rename1 `eval_operand immop _ = _` >>
      Cases_on `immop` >> simp[eval_operand_def, lookup_var_def]) >>
  reverse conj_tac >- (qexistsl_tac [`ee`, `s`] >> simp[]) >>
  fs[stmt_state_rel_def, state_rel_def] >>
  fs[storage_rel_def, transient_rel_def, accounts_rel_def,
     immutables_rel_def, logs_rel_def, contract_storage_def,
     contract_transient_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem place_store_pointer_memory_state:
  !ctx func cenv cx env ee ff s id path v w dty tv mem'.
    stmt_state_rel ctx func cenv cx ee s /\
    expr_sim_inv cenv cx env ee /\
    place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w
      (SOME LocMemory) (Type dty) /\
    (!entry t0. lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    evaluate_type (get_tenv cx) dty = SOME tv /\
    write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
    value_has_type tv v /\ val_in_memory tv v (w2n w) mem' /\
    LENGTH s.vs_memory <= LENGTH mem' /\
    (!q. q < w2n w \/ w2n w + type_memory_size tv <= q ==>
         mem_bytes_at q 1 s.vs_memory = mem_bytes_at q 1 mem') ==>
    stmt_state_rel ctx func cenv cx ff (s with vs_memory := mem')
Proof
  rpt gen_tac >> strip_tac >>
  `?entry. lookup_scopes id ee.scopes = SOME entry` by
    (Cases_on `find_containing_scope id ee.scopes` >>
     fs[write_place_def, vyperStateTheory.bind_def, get_scopes_def,
        lift_option_type_def, vyperStateTheory.return_def, raise_def] >>
     PairCases_on `x` >> drule find_containing_scope_lookup >> metis_tac[]) >>
  gvs[place_ptr_rel_def] >>
  `value_has_type entry.type entry.value` by
    (irule vyperTypeStatePreservationTheory.lookup_scopes_well_typed_value_has_type >>
     fs[expr_sim_inv_def, vyperTypeInvariantsTheory.state_well_typed_def] >> metis_tac[]) >>
  `well_formed_type_value entry.type` by metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `w2n b + k < dimword (:256)` by
    (drule mem_path_offset_sound >> strip_tac >>
     `local_ptrs_rel func cenv ee.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
     `s.vs_alloca_next < dimword (:256)` by
       metis_tac[stmt_state_rel_def, alloca_room_next_lt] >>
     fs[local_ptrs_rel_def] >>
     first_x_assum drule >> disch_then drule >> strip_tac >> gvs[] >> decide_tac) >>
  `w2n (b + n2w k) = w2n b + k` by
    (rewrite_tac[wordsTheory.word_add_def] >> simp[]) >>
  irule place_store_memory_state >>
  simp[] >>
  qpat_assum `mem_path_offset _ _ = _` (irule_at Any) >>
  goal_assum (drule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `lookup_var _ _ = _` (irule_at Any) >>
  qexists_tac `sz` >>
  `k + w2n b = w2n (b + n2w k)` by decide_tac >>
  `k + (type_memory_size tv + w2n b) =
   type_memory_size tv + w2n (b + n2w k)` by decide_tac >>
  pure_asm_rewrite_tac [] >> rewrite_tac[] >> metis_tac[]
QED

Theorem place_store_mstore_state:
  !ctx func cenv cx env ee ff s id path v w dty tv u.
    stmt_state_rel ctx func cenv cx ee s /\
    expr_sim_inv cenv cx env ee /\
    place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w
      (SOME LocMemory) (Type dty) /\
    (!entry t0. lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    evaluate_type (get_tenv cx) dty = SOME tv /\
    write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
    value_has_type tv v /\ 32 <= type_memory_size tv /\
    val_in_memory tv v (w2n w) (mstore (w2n w) u s).vs_memory ==>
    stmt_state_rel ctx func cenv cx ff (mstore (w2n w) u s)
Proof
  rpt gen_tac >> strip_tac >>
  `mstore (w2n w) u s = s with vs_memory := (mstore (w2n w) u s).vs_memory` by
    simp[mstore_def] >>
  pop_assum SUBST1_TAC >>
  irule place_store_pointer_memory_state >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `evaluate_type _ dty = _` (irule_at Any) >>
  simp[] >> conj_tac
  >- simp[venomMemPropsTheory.LENGTH_mstore_eq] >>
  rpt strip_tac >> sym_tac >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem place_store_word_memory_state:
  !ctx func cenv cx env ee ff s id path v w dty tv.
    stmt_state_rel ctx func cenv cx ee s /\
    expr_sim_inv cenv cx env ee /\
    place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w
      (SOME LocMemory) (Type dty) /\
    (!entry t0. lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    evaluate_type (get_tenv cx) dty = SOME tv /\ is_word_type dty /\
    write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
    value_has_type tv v ==>
    stmt_state_rel ctx func cenv cx ff
      (mstore (w2n w) (typed_val_to_w256 tv v) s)
Proof
  rpt gen_tac >> strip_tac >>
  irule place_store_mstore_state >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `evaluate_type _ dty = _` (irule_at Any) >>
  simp[] >> conj_tac
  >- (drule_all word_tv_memory_size >> simp[]) >>
  irule place_store_word_representation >>
  goal_assum (drule_at Any) >> simp[mstore_mem_word_at_same] >>
  qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[]
QED

Theorem place_store_empty_memory_state:
  !ctx func cenv cx env ee ff s id path w dty tv.
    stmt_state_rel ctx func cenv cx ee s /\
    expr_sim_inv cenv cx env ee /\
    place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w
      (SOME LocMemory) (Type dty) /\
    (!entry t0. lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    evaluate_type (get_tenv cx) dty = SOME tv /\ has_length_word dty /\
    write_place cx (MemoryPlace id path) (default_value tv) ee = (INL (),ff) ==>
    stmt_state_rel ctx func cenv cx ff (mstore (w2n w) 0w s)
Proof
  rpt gen_tac >> strip_tac >>
  `value_has_type tv (default_value tv)` by
    metis_tac[vyperTypeDefaultsTheory.default_value_has_type_thm,
              vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `val_in_memory tv (default_value tv) (w2n w) (mstore (w2n w) 0w s).vs_memory /\
   32 <= type_memory_size tv` by
    (irule place_store_empty_representation >>
     simp[mstore_mem_word_at_same] >>
     qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[]) >>
  irule place_store_mstore_state >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[]
QED

Theorem place_store_backend_state:
  !ctx func cenv cx es s tr st k u es'.
    stmt_state_rel ctx func cenv cx es s /\
    st = (if tr then es.tStorage cx.txn.target
          else (lookup_account cx.txn.target es.accounts).storage) /\
    (!j b. storage_dead cx tr st j b /\ j <> w2n k ==>
           storage_dead cx tr (update_storage k u st) j b) /\
    set_storage_backend cx tr (update_storage k u st) es = (INL (),es') ==>
    stmt_state_rel ctx func cenv cx es'
      (if tr then tstore k u s else sstore k u s)
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `accounts_rel cx es s` by fs[stmt_state_rel_def, state_rel_def] >>
  `accounts_rel cx es' (if tr then tstore k u s else sstore k u s)` by
    (Cases_on `tr` >> gvs[] >>
     metis_tac[accounts_rel_sstore, accounts_rel_tstore]) >>
  `storage_rel cx cx.txn.target es'
     (if tr then tstore k u s else sstore k u s) /\
   transient_rel cx cx.txn.target es'
     (if tr then tstore k u s else sstore k u s)` by
    (qpat_x_assum `accounts_rel cx es' _` mp_tac >>
     Cases_on `tr` >> simp[] >> strip_tac >>
     drule accounts_rel_storage_transient >>
     simp[sstore_def, tstore_def]) >>
  Cases_on `tr` >>
  gvs[set_storage_backend_def, vyperStateTheory.bind_def,
      vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def,
      vyperStateTheory.update_transient_def, vyperStateTheory.return_def] >>
  fs[stmt_state_rel_def, state_rel_def] >>
  fs[sstore_def, tstore_def, local_ptrs_rel_def, local_region_def,
     local_backed_def, lookup_var_def, immutables_rel_def, logs_rel_def,
     immutable_alloca_sep_def, immutable_base_zero_def, eval_operand_def] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         irule alloca_inv_fields >> qexists_tac `s` >> simp[],
         irule alloca_room_fields >> qexists_tac `s` >> simp[],
         irule fmp_room_fields >> qexists_tac `s` >> simp[],
         (qx_gen_tac `immop` >> strip_tac >>
          qpat_x_assum `!x. cenv.ce_imm_alloca = SOME x ==> _` drule >>
          Cases_on `immop` >> simp[eval_operand_def, lookup_var_def])]
QED

Theorem place_store_encoded_backend_state[local]:
  !ctx func cenv cx ee ff s tr k tv v u.
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx (StoragePlace tr k tv) v ee = (INL (),ff) /\
    encode_value tv v = SOME [(0,u)] /\
    (!st j b. storage_dead cx tr st j b /\ j <> w2n k ==>
       storage_dead cx tr (update_storage k u st) j b) ==>
    stmt_state_rel ctx func cenv cx ff (if tr then tstore k u s else sstore k u s)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[write_place_def, write_storage_slot_def, check_not_static_def,
      get_storage_backend_def, vyperStateTheory.bind_def, ignore_bind_def,
      lift_option_type_def, vyperStateTheory.return_def, raise_def,
      check_def, assert_def, vyperStorageTheory.apply_writes_def] >>
  Cases_on `cx.txn.is_static` >> gvs[] >>
  irule place_store_backend_state >>
  goal_assum (drule_at Any) >>
  qexists_tac `if tr then ee.tStorage cx.txn.target
               else (lookup_account cx.txn.target ee.accounts).storage` >>
  simp[] >>
  qpat_x_assum `_ = (INL (),ff)` mp_tac >>
  Cases_on `tr` >>
  simp[get_storage_backend_def, vyperStateTheory.bind_def,
       vyperStateTheory.get_transient_storage_def, vyperStateTheory.get_accounts_def,
       vyperStateTheory.return_def, vfmExecutionTheory.lookup_transient_storage_def]
QED

Theorem place_store_word_backend_state:
  !ctx func cenv cx ee ff s tr k tv ty v.
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx (StoragePlace tr k tv) v ee = (INL (),ff) /\
    storage_place_region cx (StoragePlace tr k tv) /\
    is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv v ==>
    stmt_state_rel ctx func cenv cx ff
      (if tr then tstore k (typed_val_to_w256 tv v) s
             else sstore k (typed_val_to_w256 tv v) s)
Proof
  rpt gen_tac >> strip_tac >>
  irule place_store_encoded_backend_state >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all place_store_scalar_storage_dead >> simp[FUN_EQ_THM]) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  irule stmtSimAssignStorageTheory.encode_value_word_typed >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem place_store_empty_encoding[local]:
  !ty tenv tv.
    has_length_word ty /\ evaluate_type tenv ty = SOME tv ==>
    encode_value tv (default_value tv) = SOME [(0,0w)]
Proof
  Cases_on `ty` >>
  simp[has_length_word_def, is_bytestring_type_def, evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[vyperStorageTheory.encode_value_def, default_value_def,
      vyperStorageTheory.encode_dyn_bytes_slots_def,
      is_bytestring_type_def, has_length_word_def,
      vyperStorageTheory.bytes_to_slots_def,
      vyperStorageTheory.bytes_to_slots_aux_def] >>
  Cases_on `b` >>
  gvs[has_length_word_def, is_bytestring_type_def,
      vyperStorageTheory.encode_value_def, default_value_def]
QED

Theorem place_store_empty_backend_state:
  !ctx func cenv cx ee ff s tr k tv ty.
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx (StoragePlace tr k tv) (default_value tv) ee = (INL (),ff) /\
    has_length_word ty /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
    stmt_state_rel ctx func cenv cx ff
      (if tr then tstore k 0w s else sstore k 0w s)
Proof
  rpt gen_tac >> strip_tac >>
  irule place_store_encoded_backend_state >> conj_tac
  >- metis_tac[storage_dead_update_zero] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  metis_tac[place_store_empty_encoding]
QED

Theorem place_store_write_location[local]:
  !ctx func cenv cx ee ff s p w loc dty v.
    stmt_state_rel ctx func cenv cx ee s /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    write_place cx p v ee = (INL (),ff) ==>
    (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
    (loc = LocMemory \/ ~s.vs_call_ctx.cc_static)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `p` >>
  gvs[place_ptr_rel_def, slot_loc_def] >>
  `~cx.txn.is_static` by
    (Cases_on `cx.txn.is_static` >>
     fs[write_place_def, write_storage_slot_def, check_not_static_def,
        vyperStateTheory.bind_def, ignore_bind_def, assert_def, check_def,
        raise_def, vyperStateTheory.return_def]) >>
  fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  Cases_on `b` >> gvs[]
QED

Theorem place_store_emit_run:
  !ctx func loc dst_op op sa sb s w wd u.
    (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
    emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                         | _ => MSTORE) [dst_op; op] sa = ((),sb) /\
    eval_operand dst_op s = SOME w /\ eval_operand op s = SOME wd /\
    fn_has_code sa sb func /\ (loc = LocMemory \/ ~s.vs_call_ctx.cc_static) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    u = (case loc of LocStorage => sstore w wd s
                  | LocTransient => tstore w wd s
                  | _ => mstore (w2n w) wd s) ==>
    gas_marked_path F ctx func s 0
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
    (!x. lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\
    SUC s.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >> (
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[emit_void_def, emit_inst_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  conj_tac
  >- (irule emit_inst_zero_marked_path >> simp[] >>
      qexistsl_tac [`[dst_op; op]`,
        `case loc of LocStorage => SSTORE | LocTransient => TSTORE
                  | _ => MSTORE`, `[]`, `sa`, `sb`] >>
      fs[emit_void_def, emit_inst_def] >>
      gvs[] >>
      simp[step_inst_base_def, venomInstTheory.mk_inst_def,
           exec_write2_def, eval_operands_def, is_terminator_def]) >>
  gvs[] >> simp[mstore_def, sstore_def, tstore_def, lookup_var_def])
QED

(* One store of a word at the place: the store opcode of its location. *)
Theorem place_store_word_run:
  !ctx func cenv cx env ee ff s p w loc dst_op op dty dtv v sa sb.
    emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                         | _ => MSTORE) [dst_op; op] sa = ((), sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    is_word_type dty /\ expr_val_rel cx dty v op s /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p v ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand op s = SOME (typed_val_to_w256 dtv v)` by
    (fs[expr_val_rel_def] >> metis_tac[]) >>
  qabbrev_tac `u = (case loc of LocStorage => sstore w (typed_val_to_w256 dtv v) s
                  | LocTransient => tstore w (typed_val_to_w256 dtv v) s
                  | _ => mstore (w2n w) (typed_val_to_w256 dtv v) s)` >>
  `stmt_state_rel ctx func cenv cx ff u` by
    (Cases_on `p`
     >- (gvs[place_ptr_rel_def, Abbr `u`, slot_loc_def] >>
         drule_all place_store_word_backend_state >> Cases_on `b` >> gvs[])
     >- (rename1 `MemoryPlace id path` >>
         `loc = LocMemory` by fs[place_ptr_rel_def] >>
         gvs[Abbr `u`] >> irule place_store_word_memory_state >>
         qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
         qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
         qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[])
     >> gvs[place_ptr_rel_def, Abbr `u`, slot_loc_def] >>
     drule_all place_store_word_backend_state >> Cases_on `b` >> gvs[]) >>
  drule_all place_store_write_location >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
   (!x. lookup_var x u = lookup_var x s) /\
   u.vs_allocas = s.vs_allocas /\ ~u.vs_halted /\
   u.vs_current_bb = sb.cs_current_bb /\
   SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule place_store_emit_run >> simp[Abbr `u`] >>
     qpat_assum `emit_void _ _ _ = _` (irule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `u with vs_inst_idx := SUC s.vs_inst_idx` >>
  fs[stmt_state_rel_inst_idx, lookup_var_def]
QED

(* compile_assign_value at the place: a word by one store, an aggregate
   by a typed copy into memory or a copy to (transient) storage, a DynArray
   to storage by its length and live elements.  A copy at one type or of
   a bytestring is one MCOPY, which reads its source before it writes, so
   only a typed copy (compile_store_memory_typed, element by element) from
   a source the lowering does not stage first needs that source outside
   the destination, or at it with the same layout (a copy in place). *)
Theorem place_store_value_run:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty
      (case dty of
         ArrayT et (Dynamic _) =>
           SOME ((type_memory_bytes cenv et + 31) DIV 32,
                 type_memory_bytes cenv et)
       | _ => NONE)
      (type_memory_bytes cenv dty) sa = ((), sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
     ~is_bytestring_type dty /\ dty <> sty ==>
     !sw dtv. eval_operand op s = SOME sw /\
              evaluate_type (get_tenv cx) dty = SOME dtv ==>
              type_memory_size stv = 0 \/
              w2n sw + type_memory_size stv <= w2n w \/
              w2n w + type_memory_size dtv <= w2n sw \/
              sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==>
     !sw. eval_operand op s = SOME sw ==>
          w2n sw + type_memory_size stv <= s.vs_alloca_next /\
          !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                     sa.cs_next_id <= aid ==>
                     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    (loc = LocMemory ==>
     !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           w2n w + type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           0 < type_slot_size dtv) /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p v ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `loc <> LocMemory ==> loc = LocStorage \/ loc = LocTransient` by
    (Cases_on `p` >> gvs[place_ptr_rel_def] >>
     rename1 `slot_loc tr` >> Cases_on `tr` >> simp[slot_loc_def]) >>
  Cases_on `loc = LocMemory`
  >- (qspecl_then
      [`ctx`, `func`, `cenv`, `cx`, `env`, `ee`, `ff`, `s`, `p`, `w`, `loc`, `dst_op`,
       `op`, `src_loc`, `dty`, `sty`, `stv`, `v`, `sa`, `sb`]
      mp_tac place_store_value_memory_run >>
    impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
    simp[]) >>
  Cases_on `?et n. dty = ArrayT et (Dynamic n)`
  >- (qspecl_then
      [`ctx`, `func`, `cenv`, `cx`, `env`, `ee`, `ff`, `s`, `p`, `w`, `loc`, `dst_op`,
       `op`, `src_loc`, `dty`, `sty`, `stv`, `v`, `sa`, `sb`]
      mp_tac place_store_value_dyn_run >>
    impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
    simp[]) >>
  `!et n. dty <> ArrayT et (Dynamic n)` by fs[] >>
  (qspecl_then
      [`ctx`, `func`, `cenv`, `cx`, `env`, `ee`, `ff`, `s`, `p`, `w`, `loc`, `dst_op`,
       `op`, `src_loc`, `dty`, `sty`, `stv`, `v`, `sa`, `sb`]
      mp_tac place_store_value_storage_run >>
    impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
    simp[])
QED

(* An empty value at a type with a length word: a zero length word at the
   place's head. *)
Theorem place_store_empty_run:
  !ctx func cenv cx env ee ff s p w loc imm dst_op dty dtv sa sb.
    compile_store_at_loc imm dst_op (Lit 0w) (SOME loc) sa = ((), sb) /\
    loc <> LocCode /\ loc <> LocCalldata /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    has_length_word dty /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p (default_value dtv) ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = (case loc of LocStorage => sstore w 0w s
                  | LocTransient => tstore w 0w s
                  | _ => mstore (w2n w) 0w s)` >>
  `stmt_state_rel ctx func cenv cx ff u` by
    (Cases_on `p`
     >- (gvs[place_ptr_rel_def, Abbr `u`, slot_loc_def] >>
         drule_all place_store_empty_backend_state >> Cases_on `b` >> gvs[])
     >- (rename1 `MemoryPlace id path` >>
         `loc = LocMemory` by fs[place_ptr_rel_def] >>
         gvs[Abbr `u`] >> irule place_store_empty_memory_state >>
         qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
         qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
         qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[])
     >> gvs[place_ptr_rel_def]) >>
  drule_all place_store_write_location >> strip_tac >>
  `emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                         | _ => MSTORE) [dst_op; Lit 0w] sa = ((),sb)` by
    (Cases_on `loc` >> gvs[compile_store_at_loc_def]) >>
  `gas_marked_path F ctx func s 0 (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
   (!x. lookup_var x u = lookup_var x s) /\
   u.vs_allocas = s.vs_allocas /\ ~u.vs_halted /\
   u.vs_current_bb = sb.cs_current_bb /\
   SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule place_store_emit_run >> simp[Abbr `u`] >>
     qpat_assum `emit_void _ _ _ = _` (irule_at Any) >> simp[] >>
     simp[eval_operand_def]) >>
  qexists_tac `u with vs_inst_idx := SUC s.vs_inst_idx` >>
  fs[stmt_state_rel_inst_idx, lookup_var_def]
QED
