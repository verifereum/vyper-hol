(* Full type envelopes, independent of runtime values. *)
Theory tuplePlaceGeometry
Ancestors
  exprSimProps loweringPosts compileEnv vyperTyping vyperValue valueEncoding
  list rich_list arithmetic integer pair alist
Libs
  pairLib

Theorem tuple_place_field_apart[local]:
  !fs id1 id2 k1 tv1 k2 tv2.
    mem_field_offset fs id1 = SOME (k1,tv1) /\
    mem_field_offset fs id2 = SOME (k2,tv2) /\ id1 <> id2 ==>
    k1 + type_memory_size tv1 <= k2 \/ k2 + type_memory_size tv2 <= k1
Proof
  Induct >> simp[mem_field_offset_def] >> PairCases >>
  rpt gen_tac >> simp[mem_field_offset_def] >>
  rw[optionTheory.OPTION_MAP_EQ_SOME, EXISTS_PROD] >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem tuple_place_take_size[local]:
  !tvs i j. i < j /\ j <= LENGTH tvs ==>
    type_memory_size_list (TAKE i tvs) + type_memory_size (EL i tvs) <=
    type_memory_size_list (TAKE j tvs)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `i` >> Cases_on `j` >>
  simp[type_memory_size_def] >> strip_tac >>
  first_x_assum (qspecl_then [`n`, `n'`] mp_tac) >> simp[]
QED

Theorem tuple_place_index_order[local]:
  !i j:int. i <> j /\ 0 <= i /\ 0 <= j ==> Num i < Num j \/ Num j < Num i
Proof
  rpt strip_tac >> `Num i <> Num j` by metis_tac[INT_OF_NUM] >> decide_tac
QED

Theorem tuple_place_mul_bound[local]:
  !i n s:num. i < n ==> i * s + s <= n * s
Proof
  rpt strip_tac >> rewrite_tac[GSYM MULT] >>
  irule LESS_MONO_MULT >> simp[]
QED

Theorem tuple_place_array_apart[local]:
  !i j s c. i <> j /\ 0 <= i /\ 0 <= j ==>
    c + Num i * s + s <= c + Num j * s \/
    c + Num j * s + s <= c + Num i * s
Proof
  rpt strip_tac >> drule_all tuple_place_index_order >> strip_tac
  >- (disj1_tac >> `Num i * s + s <= Num j * s` by
        metis_tac[tuple_place_mul_bound] >> decide_tac) >>
  disj2_tac >> `Num j * s + s <= Num i * s` by
    metis_tac[tuple_place_mul_bound] >> decide_tac
QED

Theorem tuple_place_tuple_apart[local]:
  !tvs i j. i <> j /\ 0 <= i /\ 0 <= j /\
    Num i < LENGTH tvs /\ Num j < LENGTH tvs ==>
    type_memory_size_list (TAKE (Num i) tvs) + type_memory_size (EL (Num i) tvs) <=
      type_memory_size_list (TAKE (Num j) tvs) \/
    type_memory_size_list (TAKE (Num j) tvs) + type_memory_size (EL (Num j) tvs) <=
      type_memory_size_list (TAKE (Num i) tvs)
Proof
  rpt strip_tac >> drule_all tuple_place_index_order >> strip_tac
  >- (disj1_tac >> irule tuple_place_take_size >> simp[]) >>
  disj2_tac >> irule tuple_place_take_size >> simp[]
QED

Theorem tuple_place_step_apart:
  !tv sb1 sb2 k1 tv1 k2 tv2.
    mem_step_offset tv sb1 = SOME (k1,tv1) /\
    mem_step_offset tv sb2 = SOME (k2,tv2) /\ sb1 <> sb2 ==>
    k1 + type_memory_size tv1 <= k2 \/ k2 + type_memory_size tv2 <= k1
Proof
  rpt strip_tac >>
  qpat_x_assum `mem_step_offset _ sb1 = _`
    (strip_assume_tac o MATCH_MP mem_step_offset_shape) >>
  qpat_x_assum `mem_step_offset _ sb2 = _`
    (strip_assume_tac o MATCH_MP mem_step_offset_shape) >> gvs[]
  >~ [`mem_field_offset`] >- metis_tac[tuple_place_field_apart]
  >~ [`TAKE`] >- (drule_all tuple_place_tuple_apart >> simp[ADD_COMM])
  >> (drule_all tuple_place_array_apart >>
      disch_then (qspecl_then [`type_memory_size tv1`, `0`] mp_tac) >>
      simp[ADD_COMM])
QED

Theorem tuple_place_paths_apart:
  !p tv q k u j v.
    mem_path_offset tv p = SOME (k,u) /\
    mem_path_offset tv q = SOME (j,v) /\
    ~(?r. q = p ++ r) /\ ~(?r. p = q ++ r) ==>
    k + type_memory_size u <= j \/ j + type_memory_size v <= k
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `q` >- simp[] >>
  simp[Ntimes mem_path_offset_def 2, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >> rename1 `mem_step_offset tv h = SOME (a,t1)` >>
  rename1 `mem_step_offset tv h' = SOME (b,t2)` >>
  Cases_on `h = h'`
  >- (gvs[] >> first_x_assum drule_all >> simp[]) >>
  drule_all tuple_place_step_apart >> strip_tac >>
  imp_res_tac mem_path_offset_sound >> decide_tac
QED

Theorem tuple_place_step_rank:
  !tv sb k u. mem_step_offset tv sb = SOME (k,u) ==>
    type_value_size u < type_value_size tv
Proof
  rpt strip_tac >> drule mem_step_offset_shape >> strip_tac >> gvs[]
  >- (drule mem_field_offset_sound >> strip_tac >>
      drule ALOOKUP_MEM >> strip_tac >>
      drule MEM_type_value_size_StructTV >> simp[])
  >> (mp_tac (Q.SPEC `tvs` MEM_type_value_size_TupleTV) >>
      simp[type_value_size_def] >> disch_then irule >> simp[EL_MEM])
QED

Theorem tuple_place_path_rank:
  !p tv k u. mem_path_offset tv p = SOME (k,u) ==>
    type_value_size u <= type_value_size tv /\
    (p <> [] ==> type_value_size u < type_value_size tv)
Proof
  Induct >> simp[mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule tuple_place_step_rank >> decide_tac
QED

Theorem tuple_place_path_append:
  !p tv q k u. mem_path_offset tv (p ++ q) = SOME (k,u) ==>
    ?a mid b. mem_path_offset tv p = SOME (a,mid) /\
      mem_path_offset mid q = SOME (b,u) /\ k = a+b
Proof
  Induct >> simp[mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[ADD_ASSOC]
QED

Definition tuple_place_no_tuple_step_def:
  tuple_place_no_tuple_step tv p <=>
    !pre sb rest k ts. p = pre ++ sb::rest ==>
      mem_path_offset tv pre <> SOME (k,TupleTV ts)
End

Theorem tuple_place_no_tuple_step_nil[simp]:
  tuple_place_no_tuple_step tv []
Proof
  simp[tuple_place_no_tuple_step_def]
QED

Theorem tuple_place_no_tuple_step_prefix:
  tuple_place_no_tuple_step tv (p ++ q) ==>
  tuple_place_no_tuple_step tv p
Proof
  simp[tuple_place_no_tuple_step_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `pre` mp_tac) >> simp[] >> metis_tac[APPEND_ASSOC, APPEND]
QED

Theorem tuple_place_no_tuple_step_cons:
  mem_step_offset tv sb = SOME (a,mid) ==>
  (tuple_place_no_tuple_step tv (sb::p) <=>
   (!ts. tv <> TupleTV ts) /\ tuple_place_no_tuple_step mid p)
Proof
  strip_tac >> simp[tuple_place_no_tuple_step_def] >> eq_tac
  >- (strip_tac >> conj_tac
      >- (first_x_assum (qspec_then `[]` mp_tac) >> simp[mem_path_offset_def]) >>
      rpt strip_tac >> first_x_assum (qspec_then `sb::pre` mp_tac) >>
      simp[mem_path_offset_def] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `pre` >>
  gvs[mem_path_offset_def, optionTheory.OPTION_MAP_EQ_SOME, EXISTS_PROD] >>
  metis_tac[]
QED

Theorem tuple_place_tuple_barrier_apart:
  !tv p q k ts j u.
    mem_path_offset tv p = SOME (k,TupleTV ts) /\
    mem_path_offset tv q = SOME (j,u) /\ MEM u ts /\
    tuple_place_no_tuple_step tv q ==>
    k + type_memory_size (TupleTV ts) <= j \/ j + type_memory_size u <= k
Proof
  rpt strip_tac >>
  `type_value_size u < type_value_size (TupleTV ts)` by
    metis_tac[MEM_type_value_size_TupleTV] >>
  Cases_on `?r. q = p ++ r`
  >- (pop_assum strip_assume_tac >> gvs[] >> Cases_on `r`
      >- (gvs[] >> decide_tac) >>
      qpat_x_assum `tuple_place_no_tuple_step _ _` mp_tac >>
      simp[tuple_place_no_tuple_step_def] >>
      disch_then (qspec_then `p` mp_tac) >> simp[] >> metis_tac[]) >>
  Cases_on `?r. p = q ++ r`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      drule tuple_place_path_append >> strip_tac >> gvs[] >>
      drule tuple_place_path_rank >> strip_tac >> gvs[]) >>
  irule tuple_place_paths_apart >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED
