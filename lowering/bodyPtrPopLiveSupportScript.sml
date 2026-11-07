Theory bodyPtrPopLiveSupport
Ancestors bodyPtrPopArraySupport vyperTyping valueEncodingTyping valueEncoding
  abiEncoderInput bodyPtrPopRepresentationSupport valueEncodingProps
  valueEncodingProofs exprSimAggregateEncoding abiStaticSparseProps
  bodyPtrPopSpatialSplit
  typedCopyTuplePtr structChildPtr tupleMemoryLayout exprSimAggregateLayout
  pred_set list arithmetic

(* Unlike semantic supports (which allow arbitrary enlargement), these
   witnesses record the constructor layout. In particular a dynamic array
   owns only its header and current children, not its reserved capacity.
   Fixed sparse arrays include absent indices, whose defaults are encoded. *)
Inductive pop_live_support:
  (!bt v addr. well_formed_type_value (BaseTV bt) /\
    value_has_type (BaseTV bt) v ==>
    pop_live_support (BaseTV bt) v addr
      {i | addr <= i /\ i < addr + type_memory_size (BaseTV bt)}) /\
  (!k v addr. well_formed_type_value (FlagTV k) /\
    value_has_type (FlagTV k) v ==>
    pop_live_support (FlagTV k) v addr {i | addr <= i /\ i < addr+32}) /\
  (!addr. pop_live_support NoneTV NoneV addr {}) /\
  (!tv n vs addr supp.
    well_formed_type_value (ArrayTV tv (Dynamic n)) /\
    value_has_type (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) /\
    (!j. j < LENGTH vs ==> pop_live_support tv (EL j vs)
      (addr+32+j*type_memory_size tv) (supp j)) ==>
    pop_live_support (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) addr
      ({i | addr <= i /\ i < addr+32} UNION BIGUNION {supp j | j < LENGTH vs})) /\
  (!tv n kvs addr supp.
    well_formed_type_value (ArrayTV tv (Fixed n)) /\
    value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
    (!j. j < n ==> pop_live_support tv
      (case ALOOKUP kvs j of NONE => default_value tv | SOME v => v)
      (addr+j*type_memory_size tv) (supp j)) ==>
    pop_live_support (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) addr
      (BIGUNION {supp j | j < n})) /\
  (!tvs vs addr supp.
    well_formed_type_value (TupleTV tvs) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    (!j. j < LENGTH tvs ==> pop_live_support (EL j tvs) (EL j vs)
      (addr + SUM (MAP type_memory_size (TAKE j tvs))) (supp j)) ==>
    pop_live_support (TupleTV tvs) (ArrayV (TupleV vs)) addr
      (BIGUNION {supp j | j < LENGTH tvs})) /\
  (!fts fields addr supp.
    well_formed_type_value (StructTV fts) /\
    value_has_type (StructTV fts) (StructV fields) /\
    (!j. j < LENGTH fts ==> pop_live_support (SND (EL j fts)) (SND (EL j fields))
      (addr + SUM (MAP (type_memory_size o SND) (TAKE j fts))) (supp j)) ==>
    pop_live_support (StructTV fts) (StructV fields) addr
      (BIGUNION {supp j | j < LENGTH fts}))
End

Theorem pop_live_support_typed:
  !tv v addr supp. pop_live_support tv v addr supp ==>
    well_formed_type_value tv /\ value_has_type tv v
Proof
  ho_match_mp_tac pop_live_support_ind >>
  simp[well_formed_type_value_def, value_has_type_def]
QED

Theorem pop_live_support_header:
  pop_live_support (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) addr supp ==>
  {i | addr <= i /\ i < addr+32} SUBSET supp
Proof
  simp[Once pop_live_support_cases] >> rpt strip_tac >> gvs[] >>
  simp[SUBSET_UNION]
QED

Theorem pop_live_support_exists:
  !tv v addr. well_formed_type_value tv /\ value_has_type tv v ==>
    ?supp. pop_live_support tv v addr supp
Proof
  measureInduct_on `type_value_size tv` >> rpt gen_tac >> strip_tac >>
  Cases_on `tv`
  >- metis_tac[pop_live_support_rules]
  >- (Cases_on `v` >> gvs[value_has_type_def] >>
      rename1 `value_has_type (TupleTV tvs) (ArrayV av)` >>
      Cases_on `av` >> gvs[value_has_type_def] >>
      simp[Once pop_live_support_cases, value_has_type_def] >>
      simp[GSYM SKOLEM_THM, RIGHT_EXISTS_IMP_THM] >>
      rpt strip_tac >> first_x_assum irule >>
      gvs[well_formed_type_value_def,
        vyperTypeDefaultsTheory.values_have_types_LIST_REL, LIST_REL_EL_EQN,
        EVERY_EL] >>
      qspecl_then [`tvs`, `EL j tvs`] mp_tac MEM_type_value_size_TupleTV >>
      simp[vyperValueTheory.type_value_size_def, MEM_EL] >>
      impl_tac >- (qexists_tac `j` >> simp[]) >> decide_tac)
  >- (Cases_on `v` >> gvs[value_has_type_def] >>
      Cases_on `a` >> Cases_on `b` >> gvs[value_has_type_def] >>
      simp[Once pop_live_support_cases, value_has_type_def] >>
      simp[GSYM SKOLEM_THM, RIGHT_EXISTS_IMP_THM] >>
      rpt strip_tac >> first_x_assum irule >>
      gvs[well_formed_type_value_def, all_have_type_EVERY, EVERY_EL] >>
      Cases_on `ALOOKUP l j` >> simp[] >>
      metis_tac[default_value_well_typed,
        valueEncodingProofsTheory.sparse_has_type_lookup])
  >- (Cases_on `v` >> gvs[value_has_type_def] >>
      rename1 `struct_has_type fts fields` >>
      simp[Once pop_live_support_cases, value_has_type_def] >>
      simp[GSYM SKOLEM_THM, RIGHT_EXISTS_IMP_THM] >>
      rpt strip_tac >> first_x_assum irule >>
      drule struct_has_type_values_have_types >>
      gvs[well_formed_type_value_def,
        vyperTypeDefaultsTheory.values_have_types_LIST_REL, LIST_REL_EL_EQN,
        EVERY_EL, EL_MAP] >> strip_tac >> gvs[EL_MAP] >>
      qspecl_then [`fts`, `FST (EL j fts)`, `SND (EL j fts)`]
        mp_tac MEM_type_value_size_StructTV >>
      simp[vyperValueTheory.type_value_size_def, MEM_EL] >>
      impl_tac >- (qexists_tac `j` >> simp[]) >> decide_tac)
  >- metis_tac[pop_live_support_rules] >>
  Cases_on `v` >> gvs[value_has_type_def] >> metis_tac[pop_live_support_rules]

QED

Theorem pop_live_support_bounds:
  !tv v addr supp. pop_live_support tv v addr supp ==>
    supp SUBSET {i | addr <= i /\ i < addr+type_memory_size tv}
Proof
  ho_match_mp_tac pop_live_support_ind >>
  simp[type_memory_size_def, SUBSET_DEF, IN_BIGUNION] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> disch_then drule >> strip_tac >> simp[]
  >- (gvs[value_has_type_def] >>
      `j+1 <= n` by decide_tac >>
      `j*type_memory_size tv + type_memory_size tv <= n*type_memory_size tv` by
        (qsuff_tac `(j+1)*type_memory_size tv <= n*type_memory_size tv`
         >- (disch_then (mp_tac o PURE_REWRITE_RULE [RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >> decide_tac) >> irule LESS_MONO_MULT >> simp[]) >> decide_tac)
  >- (`j+1 <= n` by decide_tac >>
      `j*type_memory_size tv + type_memory_size tv <= n*type_memory_size tv` by
        (qsuff_tac `(j+1)*type_memory_size tv <= n*type_memory_size tv`
         >- (disch_then (mp_tac o PURE_REWRITE_RULE [RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >> decide_tac) >> irule LESS_MONO_MULT >> simp[]) >> decide_tac)
  >- (drule (Q.ISPEC `type_memory_size` abi_encoder_prefix_sum_bound) >>
      simp[valueEncodingProofsTheory.type_memory_size_list_sum] >> decide_tac) >>
  drule (Q.ISPEC `type_memory_size o SND` abi_encoder_prefix_sum_bound) >>
  simp[valueEncodingProofsTheory.type_memory_size_fields_sum] >> decide_tac
QED

Theorem pop_support_window:
  value_has_type tv v ==>
  pop_rep_support tv v addr {i | addr <= i /\ i < addr+type_memory_size tv}
Proof
  strip_tac >> simp[pop_rep_support_def] >> rpt strip_tac >>
  `mem_bytes_at addr (type_memory_size tv) m =
   mem_bytes_at addr (type_memory_size tv) n` by
    (irule LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
     first_x_assum (qspec_then `addr+x` mp_tac) >>
     simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  `val_wf tv v` by metis_tac[value_has_type_val_wf] >>
  eq_tac >> strip_tac >> irule (cj 1 val_in_memory_mem_agree_proof) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem pop_support_tuple:
  LENGTH vs = LENGTH tvs /\
  (!j. j < LENGTH tvs ==> pop_rep_support (EL j tvs) (EL j vs)
    (addr+SUM (MAP type_memory_size (TAKE j tvs))) (supp j)) ==>
  pop_rep_support (TupleTV tvs) (ArrayV (TupleV vs)) addr
    (BIGUNION {supp j | j < LENGTH tvs})
Proof
  strip_tac >> simp[pop_rep_support_def, val_in_memory_def] >> rpt strip_tac >>
  `!j. j < LENGTH tvs ==>
    (val_in_memory (EL j tvs) (EL j vs)
       (addr+SUM (MAP type_memory_size (TAKE j tvs))) m <=>
     val_in_memory (EL j tvs) (EL j vs)
       (addr+SUM (MAP type_memory_size (TAKE j tvs))) n)` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[pop_rep_support_def] >> disch_then irule >> metis_tac[]) >>
  eq_tac >> strip_tac >> irule tuple_in_memory_from_elements >> simp[] >>
  metis_tac[tuple_in_memory_element]
QED

Theorem pop_support_struct:
  LENGTH fields = LENGTH fts /\
  (!j. j < LENGTH fts ==> pop_rep_support (SND (EL j fts)) (SND (EL j fields))
    (addr+SUM (MAP (type_memory_size o SND) (TAKE j fts))) (supp j)) ==>
  pop_rep_support (StructTV fts) (StructV fields) addr
    (BIGUNION {supp j | j < LENGTH fts})
Proof
  strip_tac >> simp[pop_rep_support_def, val_in_memory_def,
    fields_in_memory_tuple] >> rpt strip_tac >>
  `pop_rep_support (TupleTV (MAP SND fts)) (ArrayV (TupleV (MAP SND fields))) addr
     (BIGUNION {supp j | j < LENGTH fts})` by
    (irule (SRULE[] (Q.INST [`tvs` |-> `MAP SND fts`,
        `vs` |-> `MAP SND fields`] pop_support_tuple)) >>
     fs[EL_MAP, MAP_TAKE, MAP_MAP_o, combinTheory.o_DEF]) >>
  pop_assum mp_tac >> simp[pop_rep_support_def, val_in_memory_def] >> metis_tac[]
QED

Theorem pop_support_sparse:
  value_has_type (ArrayTV tv (Fixed cap)) (ArrayV (SArrayV kvs)) /\
  (!j. j < cap ==> pop_rep_support tv
    (case ALOOKUP kvs j of NONE => default_value tv | SOME v => v)
    (addr+j*type_memory_size tv) (supp j)) ==>
  pop_rep_support (ArrayTV tv (Fixed cap)) (ArrayV (SArrayV kvs)) addr
    (BIGUNION {supp j | j < cap})
Proof
  strip_tac >> simp[pop_rep_support_def] >> rpt strip_tac >>
  `!j. j < cap ==>
    (val_in_memory tv (case ALOOKUP kvs j of NONE => default_value tv | SOME v => v)
       (addr+j*type_memory_size tv) m <=>
     val_in_memory tv (case ALOOKUP kvs j of NONE => default_value tv | SOME v => v)
       (addr+j*type_memory_size tv) n)` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[pop_rep_support_def] >> disch_then irule >> metis_tac[]) >>
  eq_tac >> strip_tac >>
  (simp[val_in_memory_def, kvs_in_memory_every, EVERY_MEM] >> conj_tac
   >- (Cases >> strip_tac >>
       `q < cap /\ ALOOKUP kvs q = SOME r` by
         (gvs[value_has_type_def] >>
          metis_tac[sorted_sparse_ALOOKUP, typed_sparse_key_bound]) >>
       first_x_assum (qspec_then `q` mp_tac) >> simp[] >>
       fs[val_in_memory_def] >> drule_all kvs_in_memory_lookup >> metis_tac[]) >>
   rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
   fs[val_in_memory_def] >> metis_tac[])
QED

Theorem pop_live_support_sound:
  !tv v addr supp. pop_live_support tv v addr supp ==>
    pop_rep_support tv v addr supp
Proof
  ho_match_mp_tac pop_live_support_ind >> rpt conj_tac
  >- metis_tac[pop_support_window]
  >- (rpt strip_tac >>
      mp_tac (Q.INST [`tv` |-> `FlagTV k`] pop_support_window) >>
      simp[type_memory_size_def])
  >- simp[pop_rep_support_def, val_in_memory_def]
  >- (rpt strip_tac >> irule pop_support_dynarray >> simp[])
  >- (rpt strip_tac >> irule pop_support_sparse >> simp[])
  >- (rpt strip_tac >> irule pop_support_tuple >> simp[] >>
      fs[value_has_type_def] >> metis_tac[values_have_types_length]) >>
  rpt strip_tac >> irule pop_support_struct >> simp[] >>
  fs[value_has_type_def] >> drule struct_has_type_values_have_types >>
  metis_tac[values_have_types_length, LENGTH_MAP]
QED

Theorem pop_live_support_last_apart:
  (!j. j < LENGTH (pre ++ [last]) ==> pop_live_support tv (EL j (pre ++ [last]))
    (addr+32+j*type_memory_size tv) (supp j)) ==>
  DISJOINT ({i | addr <= i /\ i < addr+32} UNION
    BIGUNION {supp j | j < LENGTH pre}) (supp (LENGTH pre))
Proof
  strip_tac >>
  `supp (LENGTH pre) SUBSET
    {i | addr+32+LENGTH pre*type_memory_size tv <= i /\
         i < addr+32+LENGTH pre*type_memory_size tv+type_memory_size tv}` by
    (irule pop_live_support_bounds >> qexists_tac `EL (LENGTH pre) (pre ++ [last])` >>
     first_x_assum irule >> simp[]) >>
  simp[IN_DISJOINT, IN_BIGUNION] >> rpt strip_tac
  >- (spose_not_then strip_assume_tac >> fs[SUBSET_DEF] >>
      first_x_assum drule >> decide_tac) >>
  gvs[] >>
  `supp j SUBSET {i | addr+32+j*type_memory_size tv <= i /\
         i < addr+32+j*type_memory_size tv+type_memory_size tv}` by
    (irule pop_live_support_bounds >> qexists_tac `EL j (pre ++ [last])` >>
     first_x_assum (qspec_then `j` mp_tac) >> simp[]) >>
  `j <> LENGTH pre` by decide_tac >>
  drule bodyPtrPopPathStepTheory.pop_stride_intervals_apart >>
  disch_then (qspec_then `type_memory_size tv` mp_tac) >>
  fs[SUBSET_DEF] >> rpt strip_tac >> spose_not_then strip_assume_tac >>
  qpat_x_assum `!x. x IN supp j ==> _` drule >>
  qpat_x_assum `!x. x IN supp (LENGTH pre) ==> _` drule >> decide_tac
QED

Theorem pop_live_support_split:
  pop_live_support (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV (pre ++ [last])))
    addr supp ==>
  ?left right. supp = left UNION right /\ DISJOINT left right /\
    pop_live_support (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV pre)) addr left /\
    pop_live_support tv last (addr+32+LENGTH pre*type_memory_size tv) right
Proof
  simp[Once pop_live_support_cases] >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`{i | addr <= i /\ i < addr+32} UNION
    BIGUNION {supp' j | j < LENGTH pre}`, `supp' (LENGTH pre)`] >>
  conj_tac
  >- (simp[EXTENSION, IN_BIGUNION] >>
      `!j. j < LENGTH pre+1 <=> j < LENGTH pre \/ j = LENGTH pre` by decide_tac >>
      metis_tac[]) >>
  conj_tac >- (irule pop_live_support_last_apart >> qexistsl_tac [`last`, `tv`] >> simp[]) >>
  conj_tac
  >- (irule (cj 4 pop_live_support_rules) >> simp[] >> reverse conj_tac
      >- (fs[value_has_type_def, all_have_type_EVERY, EVERY_APPEND]) >>
      rpt strip_tac >> first_x_assum (qspec_then `j` mp_tac) >> simp[EL_APPEND_EQN]) >>
  first_x_assum (qspec_then `LENGTH pre` mp_tac) >> simp[EL_APPEND_EQN]
QED
