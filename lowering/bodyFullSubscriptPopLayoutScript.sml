Theory bodyFullSubscriptPopLayout
Ancestors
  bodyFullSubscriptLayoutByte placeMemoryPathRebuild
  dynCopyMemory[qualified,ignore_grammar]
  vyperPlaceStatePreservation valueEncodingTyping vyperAssignPreservesType
  arithmetic list alist vyperTyping vyperValue vyperValueOperation vyperState
  valueEncoding valueEncodingDefs typeLayoutProps loweringPosts exprSimProps
  vyperPlaceResultTyping option rich_list pair sum integer vyperArray sorting
Libs
  pairLib

(* A read of a child contributes only observations already made by its
   container. The address is the absolute address of the child. *)
Theorem layout_fields_project[local]:
  !fields fts a id v k tv i.
    struct_has_type fts fields /\ ALOOKUP fields id = SOME v /\
    mem_field_offset fts id = SOME (k,tv) /\
    subscript_layout_byte tv v (a + k) i ==>
    subscript_layout_fields_byte fields fts a i
Proof
  Induct >> Cases_on `fts` >> simp[value_has_type_def] >>
  PairCases_on `h` >> rpt gen_tac >>
  rename1 `struct_has_type ((_,_)::_) (f::fields)` >> PairCases_on `f` >>
  rw[value_has_type_def, mem_field_offset_def,
     subscript_layout_byte_cases, AllCaseEqs()] >> gvs[] >>
  rename1 `mem_field_offset _ id = SOME z` >> PairCases_on `z` >>
  gvs[] >> disj2_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[AC ADD_ASSOC ADD_COMM] >>
  qexists `id` >> simp[]
QED

Theorem layout_elems_observe[local]:
  !vs a tv i.
    subscript_layout_elems_byte vs a tv i <=>
    ?j. j < LENGTH vs /\
        subscript_layout_byte tv (EL j vs) (a + j * type_memory_size tv) i
Proof
  Induct >> simp[subscript_layout_byte_cases] >> rpt gen_tac >>
  eq_tac >> strip_tac
  >- (qexists `0` >> simp[])
  >- (qexists `SUC j` >> simp[MULT, AC ADD_ASSOC ADD_COMM]) >>
  Cases_on `j` >> gvs[MULT, AC ADD_ASSOC ADD_COMM] >> metis_tac[]
QED

Theorem layout_tuple_project[local]:
  !vs tvs a j i.
    j < LENGTH vs /\ j < LENGTH tvs /\
    subscript_layout_byte (EL j tvs) (EL j vs)
      (a + type_memory_size_list (TAKE j tvs)) i ==>
    subscript_layout_tuple_byte vs tvs a i
Proof
  Induct >> Cases_on `tvs` >> simp[] >> rpt gen_tac >>
  Cases_on `j` >> simp[subscript_layout_byte_cases, type_memory_size_def,
                       AC ADD_ASSOC ADD_COMM] >> strip_tac >> disj2_tac >>
  first_x_assum irule >> qexists `n` >> simp[AC ADD_ASSOC ADD_COMM]
QED

Theorem layout_kvs_observe[local]:
  !kvs a tv i.
    subscript_layout_kvs_byte kvs a tv i <=>
    ?j v. MEM (j,v) kvs /\
          subscript_layout_byte tv v (a + j * type_memory_size tv) i
Proof
  Induct >> simp[subscript_layout_byte_cases] >> Cases >>
  simp[subscript_layout_byte_cases] >> metis_tac[]
QED

Theorem layout_array_project[local]:
  !tv av a j v k etv i.
    value_has_type tv (ArrayV av) /\ array_index tv av j = SOME v /\
    mem_step_offset tv (ValueSubscript (IntV j)) = SOME (k,etv) /\
    subscript_layout_byte etv v (a+k) i ==>
    subscript_layout_byte tv (ArrayV av) a i
Proof
  rpt gen_tac >> Cases_on `tv` >> Cases_on `av` >> gvs[value_has_type_def] >>
  TRY (rename1 `ArrayTV _ bd` >> Cases_on `bd` >> gvs[value_has_type_def]) >>
  rw[array_index_def, mem_step_offset_def, AllCaseEqs(), oEL_THM] >> gvs[]
  >- (simp[subscript_layout_byte_cases] >> irule layout_tuple_project >>
      qexists `Num j` >> simp[])
  >- (simp[subscript_layout_byte_cases, layout_elems_observe] >>
      disj2_tac >> qexists `Num j` >> simp[AC ADD_ASSOC ADD_COMM]) >>
  gvs[subscript_layout_byte_cases, layout_kvs_observe,
      optionTheory.option_CLAUSES, AllCaseEqs()] >>
  metis_tac[ALOOKUP_MEM]
QED

Theorem layout_step_project[local]:
  !tv a sb v off k etv i.
    value_has_type tv a /\ evaluate_subscripts tv a [sb] = INL v /\
    mem_step_offset tv sb = SOME (k,etv) /\
    subscript_layout_byte etv v (off + k) i ==>
    subscript_layout_byte tv a off i
Proof
  rpt gen_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
      simp[evaluate_subscripts_def] >> Cases_on `a` >>
      simp[evaluate_subscripts_def, AllCaseEqs()] >>
      rpt strip_tac >> irule layout_array_project >>
      goal_assum (drule_at Any) >>
      rename1 `array_index _ _ j = SOME v` >>
      qexistsl [`etv`, `j`, `k`, `v`] >> simp[AC ADD_ASSOC ADD_COMM]) >>
  Cases_on `tv` >> Cases_on `a` >>
  simp[evaluate_subscripts_def, mem_step_offset_def, value_has_type_def,
       subscript_layout_byte_cases, AllCaseEqs()] >>
  rpt strip_tac >> irule layout_fields_project >>
  simp[] >> qexistsl [`s`, `k`, `etv`, `v`] >> simp[AC ADD_ASSOC ADD_COMM]
QED

Theorem subscript_pop_layout_project:
  !path tv a v off k ptv i.
    value_has_type tv a /\ well_formed_type_value tv /\
    evaluate_subscripts tv a path = INL v /\
    mem_path_offset tv path = SOME (k,ptv) /\
    subscript_layout_byte ptv v (off + k) i ==>
    subscript_layout_byte tv a off i
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_path_offset_def, evaluate_subscripts_def] >>
  gvs[mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  rename1 `mem_step_offset tv sb = SOME (delta,etv)` >>
  `mem_path_offset tv [sb] = SOME (delta,etv)` by simp[mem_path_offset_def] >>
  drule mem_path_offset_sound >> simp[subscripts_type_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path`, `a`] assume_tac) >>
  qpat_x_assum `evaluate_subscripts tv a (sb::path) = INL v` mp_tac >>
  once_asm_rewrite_tac[] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `evaluate_subscripts tv a [sb] = INL child` >>
  `value_has_type etv child` by
    (irule evaluate_subscripts_type >> goal_assum (drule_at Any) >>
     simp[subscripts_type_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `well_formed_type_value etv` by metis_tac[subscript_type_well_formed] >>
  `subscript_layout_byte etv child (off + delta) i` by
    (first_x_assum irule >> simp[] >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[AC ADD_ASSOC ADD_COMM]) >>
  drule_all layout_step_project >> simp[]
QED

(* A sparse cell is observed through its effective value, even when an
   update drops its explicit binding because the new value is the default. *)
Theorem layout_sparse_observe[local]:
  !vs a tv n i.
    value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV vs)) ==>
    (subscript_layout_byte (ArrayTV tv (Fixed n)) (ArrayV (SArrayV vs)) a i <=>
     ?j z. j < n /\ array_index (ArrayTV tv (Fixed n)) (SArrayV vs) (&j) = SOME z /\
           subscript_layout_byte tv z (a + j * type_memory_size tv) i)
Proof
  simp[value_has_type_def, subscript_layout_byte_cases, layout_kvs_observe,
       array_index_def, AllCaseEqs()] >> rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP FST vs)` by simp[SORTED_lt_ALL_DISTINCT] >>
  eq_tac >> strip_tac
  >- (qexistsl [`j`, `v`] >>
      drule_all ALOOKUP_ALL_DISTINCT_MEM >> strip_tac >>
      drule_all ALOOKUP_sparse_has_type >> simp[])
  >- (qexistsl [`k`, `default_value tv`] >> simp[]) >>
  metis_tac[ALOOKUP_MEM]
QED

Theorem layout_dyn_observe[local]:
  subscript_layout_byte (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) a i <=>
  (a <= i /\ i < a + 32) \/
  ?j z. array_index (ArrayTV tv (Dynamic n)) (DynArrayV vs) (&j) = SOME z /\
        subscript_layout_byte tv z (a + 32 + j * type_memory_size tv) i
Proof
  simp[subscript_layout_byte_cases, layout_elems_observe, array_index_def,
       oEL_THM, AllCaseEqs()]
QED

Theorem layout_array_cell_replace[local]:
  !tv av av' k old new etv a i.
    value_has_type tv (ArrayV av) /\ value_has_type tv (ArrayV av') /\
    subscript_type tv (ValueSubscript (IntV k)) = SOME etv /\
    array_index tv av k = SOME old /\
    array_set_index tv av k new = INL (ArrayV av') /\
    (!b j. subscript_layout_byte etv new b j ==> subscript_layout_byte etv old b j) /\
    subscript_layout_byte tv (ArrayV av') a i ==>
    subscript_layout_byte tv (ArrayV av) a i
Proof
  rpt gen_tac >> strip_tac >>
  drule array_index_after_set_same >> strip_tac >>
  `!j. j <> k ==> array_index tv av' j = array_index tv av j` by
    metis_tac[array_index_after_set_other] >>
  Cases_on `tv` >> Cases_on `av` >> Cases_on `av'` >>
  gvs[value_has_type_def, subscript_type_def] >>
  TRY (rename1 `ArrayTV _ bd` >> Cases_on `bd` >> gvs[value_has_type_def]) >>
  TRY (gvs[layout_dyn_observe] >> disj2_tac) >>
  TRY (qpat_assum `sparse_has_type _ _ _` (mp_tac o REWRITE_RULE [GSYM CONJ_ASSOC]) >>
       disch_tac >> gvs[layout_sparse_observe, value_has_type_def]) >>
  TRY (gvs[array_set_index_def, AllCaseEqs()] >> NO_TAC) >>
  qexists `j` >> Cases_on `&j = k` >> gvs[] >> metis_tac[]
QED

Theorem layout_fields_replace[local]:
  !fields fts name old new tv a i.
    struct_has_type fts fields /\ ALOOKUP fields name = SOME old /\
    ALOOKUP fts name = SOME tv /\
    (!b j. subscript_layout_byte tv new b j ==> subscript_layout_byte tv old b j) /\
    subscript_layout_fields_byte (AFUPDKEY name (K new) fields) fts a i ==>
    subscript_layout_fields_byte fields fts a i
Proof
  Induct >> Cases_on `fts` >> simp[value_has_type_def] >>
  PairCases_on `h` >> rpt gen_tac >>
  rename1 `struct_has_type ((_,_)::_) (f::fields)` >> PairCases_on `f` >>
  strip_tac >> gvs[value_has_type_def] >>
  Cases_on `name = f0` >>
  gvs[AFUPDKEY_def, cj 13 subscript_layout_byte_cases] >> metis_tac[]
QED

Theorem layout_step_replace[local]:
  !tv a sb old new updated etv b i.
    value_has_type tv a /\ well_formed_type_value tv /\ value_has_type etv new /\
    subscript_type tv sb = SOME etv /\
    evaluate_subscripts tv a [sb] = INL old /\
    assign_subscripts tv a [sb] (Replace new) = INL updated /\
    (!c j. subscript_layout_byte etv new c j ==> subscript_layout_byte etv old c j) /\
    subscript_layout_byte tv updated b i ==>
    subscript_layout_byte tv a b i
Proof
  rpt gen_tac >> strip_tac >> drule_all assign_subscripts_singleton_typed >> strip_tac >>
  Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
      gvs[evaluate_subscripts_def, AllCaseEqs()] >>
      gvs[assign_subscripts_def, AllCaseEqs()] >>
      Cases_on `updated` >> gvs[] >>
      TRY (Cases_on `av` >> gvs[array_set_index_def, AllCaseEqs()] >> NO_TAC) >>
      rename1 `array_set_index tv av k new = INL (ArrayV av')` >>
      irule layout_array_cell_replace >> simp[] >>
      qexistsl [`av'`,`etv`,`k`,`new`,`old`] >> simp[]) >>
  Cases_on `tv` >> Cases_on `a` >>
  gvs[evaluate_subscripts_def, assign_subscripts_def, subscript_type_def,
      value_has_type_def, subscript_layout_byte_cases, AllCaseEqs()] >>
  irule layout_fields_replace >> metis_tac[]
QED

Theorem layout_path_replace[local]:
  !path tv a old new updated etv.
    value_has_type tv a /\ well_formed_type_value tv /\ value_has_type etv new /\
    subscripts_type tv path = SOME etv /\
    evaluate_subscripts tv a path = INL old /\
    assign_subscripts tv a path (Replace new) = INL updated /\
    (!c j. subscript_layout_byte etv new c j ==> subscript_layout_byte etv old c j) ==>
    !b i. subscript_layout_byte tv updated b i ==> subscript_layout_byte tv a b i
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[subscripts_type_def, evaluate_subscripts_def, assign_subscripts_def] >>
  gvs[subscripts_type_def, AllCaseEqs()] >>
  drule_all assign_subscripts_cons_typed >> strip_tac >>
  drule evaluate_subscripts_cons_typed >> disch_then (qspecl_then [`path`, `a`] assume_tac) >>
  gvs[] >>
  rename1 `subscript_type tv sb = SOME child_tv` >>
  `well_formed_type_value child_tv` by (drule_all subscript_type_well_formed >> simp[]) >>
  `value_has_type child_tv child` by
    (irule evaluate_subscripts_type >> qexistsl [`a`, `[sb]`, `tv`] >> simp[subscripts_type_def]) >>
  `value_has_type child_tv child'` by
    (irule assign_subscripts_type_path_preserves_type >> simp[] >>
     qexistsl [`child`, `path`, `etv`, `new`] >> simp[]) >>
  `!b i. subscript_layout_byte child_tv child' b i ==> subscript_layout_byte child_tv child b i` by
    ((metis_tac[])) >>
  rpt strip_tac >> irule layout_step_replace >> simp[] >>
  qexistsl [`child_tv`, `child'`, `child`, `sb`, `updated`] >> simp[]
QED

Theorem subscript_pop_layout_shorten:
  !path tv a vs updated etv n b i.
    value_has_type tv a /\ well_formed_type_value tv /\ vs <> [] /\
    subscripts_type tv path = SOME (ArrayTV etv (Dynamic n)) /\
    evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\
    assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
    subscript_layout_byte tv updated b i ==>
    subscript_layout_byte tv a b i
Proof
  rpt strip_tac >>
  `value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs))` by
    metis_tac[evaluate_subscripts_type] >>
  irule layout_path_replace >> simp[] >>
  qexistsl [`ArrayTV etv (Dynamic n)`, `ArrayV (DynArrayV (FRONT vs))`,
            `ArrayV (DynArrayV vs)`, `path`, `updated`] >> simp[] >>
  conj_tac
  >- (simp[subscript_layout_byte_cases, layout_elems_observe] >>
      rpt gen_tac >> strip_tac >> simp[] >> disj2_tac >>
      rename1 `k < LENGTH (FRONT vs)` >> qexists `k` >>
      gvs[LENGTH_FRONT, FRONT_EL]) >>
  gvs[value_has_type_def, all_have_type_EVERY, EVERY_EL, LENGTH_FRONT] >>
  rpt strip_tac >> rename1 `k < PRE (LENGTH vs)` >>
  `k < LENGTH (FRONT vs)` by simp[LENGTH_FRONT] >>
  `k < LENGTH vs` by decide_tac >> simp[FRONT_EL]
QED

(* All tested bytes lie within the type-sized allocation. For a sparse
   array the capacity bounds each stored index, not the number of pairs. *)
Theorem layout_range_mutual[local]:
  (!tv v a i. value_has_type tv v /\ subscript_layout_byte tv v a i ==>
     a <= i /\ i < a + type_memory_size tv) /\
  (!fs ts a i. struct_has_type ts fs /\ subscript_layout_fields_byte fs ts a i ==>
     a <= i /\ i < a + type_memory_size_fields ts) /\
  (!vs a tv i. all_have_type tv vs /\ subscript_layout_elems_byte vs a tv i ==>
     a <= i /\ i < a + LENGTH vs * type_memory_size tv) /\
  (!kvs a tv i n. sparse_has_type tv n kvs /\ subscript_layout_kvs_byte kvs a tv i ==>
     a <= i /\ i < a + n * type_memory_size tv) /\
  (!vs ts a i. values_have_types ts vs /\ subscript_layout_tuple_byte vs ts a i ==>
     a <= i /\ i < a + type_memory_size_list ts)
Proof
  ho_match_mp_tac subscript_layout_byte_cases_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[subscript_layout_byte_cases]
  >- (Cases_on `tv` >> TRY (rename1 `value_has_type (BaseTV bt) _ /\ _ ==> _` >> Cases_on `bt`) >>
      simp[value_has_type_def, type_memory_size_def])
  >- (Cases_on `tv` >> TRY (rename1 `value_has_type (BaseTV bt) _ /\ _ ==> _` >> Cases_on `bt`) >>
      simp[value_has_type_def, type_memory_size_def])
  >- (Cases_on `tv` >> simp[value_has_type_def, type_memory_size_def])
  >- (Cases_on `tv` >> TRY (rename1 `value_has_type (BaseTV bt) _ /\ _ ==> _` >> Cases_on `bt`) >>
      simp[value_has_type_def, type_memory_size_def])
  >- (Cases_on `tv` >> simp[value_has_type_def, type_memory_size_def] >>
      rename1 `value_has_type (BaseTV bt) _ /\ _ ==> _` >> Cases_on `bt` >>
      simp[value_has_type_def, type_memory_size_def] >>
      rename1 `value_has_type (BaseTV (BytesT bd)) _ /\ _ ==> _` >> Cases_on `bd` >>
      simp[value_has_type_def, type_memory_size_def] >> rpt strip_tac >>
      assume_tac (Q.SPEC `n` le_word_size_mul) >> decide_tac)
  >- (Cases_on `tv` >> simp[value_has_type_def, type_memory_size_def] >>
      rename1 `value_has_type (BaseTV bt) _ /\ _ ==> _` >> Cases_on `bt` >>
      simp[value_has_type_def, type_memory_size_def] >> rpt strip_tac >>
      assume_tac (Q.SPEC `n` le_word_size_mul) >> decide_tac)
  >- (Cases_on `tv` >> simp[value_has_type_def, type_memory_size_def])
  >- (Cases_on `tv` >> simp[value_has_type_def, type_memory_size_def] >>
      rename1 `ArrayTV etv bd` >> Cases_on `bd` >>
      simp[value_has_type_def, type_memory_size_def] >> rpt strip_tac >> gvs[] >>
      rename1 `LENGTH vs <= cap` >>
      `LENGTH vs * type_memory_size etv <= cap * type_memory_size etv` by simp[LE_MULT_RCANCEL] >>
      decide_tac)
  >- (Cases_on `tv` >> simp[value_has_type_def, type_memory_size_def] >>
      rename1 `ArrayTV etv bd` >> Cases_on `bd` >>
      simp[value_has_type_def, default_value_well_typed, type_memory_size_def] >>
      rpt strip_tac >> gvs[]
      >- metis_tac[] >>
      `type_memory_size etv + k * type_memory_size etv <= n * type_memory_size etv`
        by (ONCE_REWRITE_TAC [ADD_COMM] >>
            irule dynCopyMemoryTheory.array_copy_slot_bound >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `!j. subscript_layout_byte _ (default_value _) _ _ ==> _`
        (qspec_then `k` mp_tac) >> simp[] >> decide_tac)
  >- (Cases_on `tv` >> simp[value_has_type_def, type_memory_size_def])
  >- (Cases_on `ts` >> simp[value_has_type_def] >> PairCases_on `h` >>
      simp[value_has_type_def, type_memory_size_def] >> rpt strip_tac >> gvs[] >> decide_tac)
  >- (simp[value_has_type_def, MULT] >> rpt strip_tac >> gvs[] >> decide_tac)
  >- (simp[value_has_type_def] >> rpt strip_tac >> gvs[]
      >~ [`_ <= _ (* g *)`] >- metis_tac[] >>
      `type_memory_size tv + k * type_memory_size tv <= n * type_memory_size tv`
        by (ONCE_REWRITE_TAC [ADD_COMM] >>
            irule dynCopyMemoryTheory.array_copy_slot_bound >> first_assum ACCEPT_TAC) >> decide_tac)
  >> Cases_on `ts` >> simp[value_has_type_def, type_memory_size_def] >>
     rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem subscript_pop_layout_observation_laws:
  (!path tv a v off k ptv i.
    value_has_type tv a /\ well_formed_type_value tv /\
    evaluate_subscripts tv a path = INL v /\
    mem_path_offset tv path = SOME (k,ptv) /\
    subscript_layout_byte ptv v (off + k) i ==>
    subscript_layout_byte tv a off i) /\
  (!path tv a vs updated etv n b i.
    value_has_type tv a /\ well_formed_type_value tv /\ vs <> [] /\
    subscripts_type tv path = SOME (ArrayTV etv (Dynamic n)) /\
    evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\
    assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
    subscript_layout_byte tv updated b i ==>
    subscript_layout_byte tv a b i) /\
  (!tv v a i. value_has_type tv v /\ subscript_layout_byte tv v a i ==>
    a <= i /\ i < a + type_memory_size tv)
Proof
  rpt conj_tac
  >- ACCEPT_TAC subscript_pop_layout_project
  >- ACCEPT_TAC subscript_pop_layout_shorten
  >> ACCEPT_TAC (CONJUNCT1 layout_range_mutual)
QED
