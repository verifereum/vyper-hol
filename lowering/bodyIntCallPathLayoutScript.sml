(* Current semantic selections, not popped-history reads, retain their layout. *)
Theory bodyIntCallPathLayout
Ancestors
  loweringPosts exprSimProps exprSimAggregateEncoding tupleMemoryLayout
  valueEncoding valueEncodingProofs vyperTypeSystem vyperTyping vyperState vyperArray
  vyperValue vyperValueOperation list arithmetic alist
  vyperAssignPreservesType vyperTypeDefaults vyperPlaceStatePreservation

Theorem mem_field_offset_memory:
  !fs vals id k tv v b mem.
    struct_has_type fs vals /\ fields_in_memory vals fs b mem /\
    mem_field_offset fs id = SOME (k,tv) /\ ALOOKUP vals id = SOME v ==>
    val_in_memory tv v (b + k) mem
Proof
  Induct >> Cases_on `vals` >> simp[value_has_type_def] >>
  rpt gen_tac >>
  qmatch_goalsub_rename_tac `struct_has_type (fld::fs) (vl::vs)` >>
  Cases_on `fld` >> Cases_on `vl` >>
  simp[value_has_type_def, mem_field_offset_def, val_in_memory_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  first_x_assum drule_all >>
  qmatch_goalsub_rename_tac `b + (delta + type_memory_size field_tv)` >>
  `b + type_memory_size field_tv + delta =
   b + (delta + type_memory_size field_tv)` by decide_tac >>
  asm_rewrite_tac[]
QED

Theorem array_index_memory:
  !et bd av i k tv v b mem.
    value_has_type (ArrayTV et bd) (ArrayV av) /\
    val_in_memory (ArrayTV et bd) (ArrayV av) b mem /\
    mem_step_offset (ArrayTV et bd) (ValueSubscript (IntV i)) = SOME (k,tv) /\
    array_index (ArrayTV et bd) av i = SOME v ==>
    val_in_memory tv v (b + k) mem
Proof
  Cases_on `bd` >> Cases_on `av` >>
  simp[value_has_type_def, val_in_memory_def, mem_step_offset_def,
       array_index_sarray, array_index_dyn] >> rpt strip_tac >>
  gvs[AllCaseEqs()]
  >~ [`kvs_in_memory _ _ _ _`]
  >- (drule_all kvs_in_memory_lookup >> simp[]) >>
  gvs[listTheory.oEL_EQ_EL] >>
  drule_all elems_in_memory_EL >>
  `b + 32 + Num i * type_memory_size et =
   b + (Num i * type_memory_size et + 32)` by decide_tac >>
  asm_rewrite_tac[]
QED

Theorem tuple_index_memory:
  !tvs vs i k tv v b mem.
    values_have_types tvs vs /\ tuple_in_memory vs tvs b mem /\
    mem_step_offset (TupleTV tvs) (ValueSubscript (IntV i)) = SOME (k,tv) /\
    array_index (TupleTV tvs) (TupleV vs) i = SOME v ==>
    val_in_memory tv v (b + k) mem
Proof
  rpt gen_tac >>
  simp[mem_step_offset_def, vyperValueOperationTheory.array_index_def,
       listTheory.oEL_EQ_EL] >> strip_tac >> gvs[] >>
  drule values_have_types_length >> strip_tac >>
  `!ts. type_memory_size_list ts = SUM (MAP type_memory_size ts)` by
    (Induct >> simp[type_memory_size_def]) >>
  drule_all tuple_in_memory_element >> asm_rewrite_tac[]
QED

Theorem mem_step_offset_memory:
  !itv iv sb k tv v b mem.
    value_has_type itv iv /\ val_in_memory itv iv b mem /\
    mem_step_offset itv sb = SOME (k,tv) /\
    evaluate_subscripts itv iv [sb] = INL v ==>
    val_in_memory tv v (b + k) mem
Proof
  rpt gen_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript idx` >> Cases_on `idx` >>
      simp[mem_step_offset_def] >>
      Cases_on `itv` >> simp[mem_step_offset_def] >>
      Cases_on `iv` >> simp[value_has_type_def, evaluate_subscripts_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()]
      >~ [`mem_step_offset (ArrayTV _ _) _ = _`]
      >- (drule_all array_index_memory >> simp[]) >>
      rename1 `value_has_type (TupleTV _) (ArrayV av)` >>
      Cases_on `av` >> gvs[value_has_type_def, val_in_memory_def] >>
      drule_at (Pat `array_index _ _ _ = _`) tuple_index_memory >>
      simp[mem_step_offset_def]) >>
  Cases_on `itv` >> simp[mem_step_offset_def] >>
  Cases_on `iv` >>
  simp[value_has_type_def, evaluate_subscripts_def, val_in_memory_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  drule_all mem_field_offset_memory >> simp[]
QED

Theorem mem_field_offset_default_memory:
  !fs id k tv b mem.
    fields_in_memory (MAP (\(nm,t). (nm,default_value t)) fs) fs b mem /\
    mem_field_offset fs id = SOME (k,tv) ==>
    val_in_memory tv (default_value tv) (b + k) mem
Proof
  Induct >> simp[mem_field_offset_def] >>
  Cases_on `h` >> simp[mem_field_offset_def, val_in_memory_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  pairarg_tac >> gvs[] >> first_x_assum drule_all >>
  qmatch_goalsub_rename_tac `b + (delta + type_memory_size field_tv)` >>
  `b + type_memory_size field_tv + delta =
   b + (delta + type_memory_size field_tv)` by decide_tac >>
  asm_rewrite_tac[]
QED

Theorem mem_step_default_selection:
  !tv sb k etv v.
    mem_step_offset tv sb = SOME (k,etv) /\
    evaluate_subscripts tv (default_value tv) [sb] = INL v ==>
    v = default_value etv
Proof
  rpt gen_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript idx` >> Cases_on `idx` >>
      simp[mem_step_offset_def] >> Cases_on `tv` >>
      simp[mem_step_offset_def, default_value_def, default_value_tuple_MAP,
           evaluate_subscripts_def, array_index_def, oEL_EQ_EL] >>
      rpt strip_tac >> gvs[AllCaseEqs(), EL_MAP] >>
      gvs[oEL_EQ_EL, EL_MAP, default_value_def] >>
      rename1 `ArrayTV _ bd` >> Cases_on `bd` >>
      gvs[mem_step_offset_def, default_value_def, evaluate_subscripts_def,
          array_index_def, oEL_EQ_EL, AllCaseEqs()]) >>
  Cases_on `tv` >> simp[mem_step_offset_def] >>
  simp[default_value_def, default_value_struct_MAP, evaluate_subscripts_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  drule mem_field_offset_sound >> strip_tac >>
  qpat_x_assum `ALOOKUP (MAP _ _) _ = SOME _` mp_tac >>
  simp[ALOOKUP_MAP]
QED

Theorem mem_step_default_memory:
  !tv sb k etv v b mem.
    val_in_memory tv (default_value tv) b mem /\
    mem_step_offset tv sb = SOME (k,etv) /\
    evaluate_subscripts tv (default_value tv) [sb] = INL v ==>
    val_in_memory etv v (b + k) mem
Proof
  rpt gen_tac >> strip_tac >>
  drule_all mem_step_default_selection >> strip_tac >> gvs[] >>
  Cases_on `sb`
  >- (rename1 `ValueSubscript idx` >> Cases_on `idx` >>
      gvs[mem_step_offset_def] >> Cases_on `tv` >>
      gvs[mem_step_offset_def, default_value_def, default_value_tuple_MAP,
          val_in_memory_def] 
      >~ [`tuple_in_memory _ _ _ _`]
      >- (`!ts. type_memory_size_list ts = SUM (MAP type_memory_size ts)` by
            (Induct >> simp[type_memory_size_def]) >>
          drule_at (Pat `tuple_in_memory _ _ _ _`) tuple_in_memory_element >>
          simp[EL_MAP] >> disch_then (qspec_then `Num i` mp_tac) >> simp[]) >>
      rename1 `ArrayTV _ bd` >> Cases_on `bd` >>
      gvs[mem_step_offset_def, default_value_def, val_in_memory_def,
          evaluate_subscripts_def, array_index_def, oEL_EQ_EL, AllCaseEqs()]) >>
  Cases_on `tv` >> gvs[mem_step_offset_def] >>
  gvs[default_value_def, default_value_struct_MAP, val_in_memory_def] >>
  drule_all mem_field_offset_default_memory >> simp[]
QED

Theorem mem_step_selection_closed:
  !tv a sb k etv v.
    (value_has_type tv a \/ a = default_value tv) /\
    mem_step_offset tv sb = SOME (k,etv) /\
    evaluate_subscripts tv a [sb] = INL v ==>
    value_has_type etv v \/ v = default_value etv
Proof
  rpt gen_tac >> strip_tac
  >- (Cases_on `sb`
      >- (rename1 `ValueSubscript idx` >> Cases_on `idx` >>
          gvs[mem_step_offset_def] >> Cases_on `tv` >>
          gvs[mem_step_offset_def] >> Cases_on `a` >>
          gvs[value_has_type_def, evaluate_subscripts_def, AllCaseEqs()] >>
          rename1 `array_index _ av _ = SOME _` >> Cases_on `av` >>
          gvs[value_has_type_def, array_index_def, AllCaseEqs()]
          >~ [`values_have_types _ _`]
          >- (gvs[oEL_EQ_EL, values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
              disj1_tac >> first_x_assum irule >> simp[]) >>
          gvs[mem_step_offset_def, AllCaseEqs()]
          >~ [`sparse_has_type _ _ _`]
          >- (disj1_tac >> drule_all ALOOKUP_sparse_has_type >> simp[]) >>
          rename1 `value_has_type (ArrayTV _ bd) _` >> Cases_on `bd` >>
          gvs[mem_step_offset_def, value_has_type_def, AllCaseEqs()] >>
          drule_all oEL_all_have_type >> simp[]) >>
      Cases_on `tv` >> gvs[mem_step_offset_def] >>
      Cases_on `a` >>
      gvs[value_has_type_def, evaluate_subscripts_def, AllCaseEqs()] >>
      drule mem_field_offset_sound >> strip_tac >>
      drule_all struct_field_has_type >> strip_tac >> gvs[]) >>
  gvs[] >> disj2_tac >> irule mem_step_default_selection >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem mem_path_selection_memory:
  !path tv a k ptv v b mem.
    (value_has_type tv a \/ a = default_value tv) /\
    val_in_memory tv a b mem /\
    mem_path_offset tv path = SOME (k,ptv) /\
    evaluate_subscripts tv a path = INL v ==>
    val_in_memory ptv v (b + k) mem
Proof
  Induct
  >- simp[mem_path_offset_def, evaluate_subscripts_def] >>
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  gnvs[mem_path_offset_def, AllCaseEqs()] >>
  qpat_x_assum `?x. _` strip_assume_tac >>
  pairarg_tac >> gnvs[] >>
  rename1 `mem_step_offset tv sb = SOME (delta,child_tv)` >>
  rename1 `mem_path_offset child_tv path = SOME (tail_delta,result_tv)` >>
  `subscript_type tv sb = SOME child_tv` by
    (`mem_path_offset tv [sb] = SOME (delta,child_tv)` by
       simp[mem_path_offset_def] >>
     drule mem_path_offset_sound >>
     simp[subscripts_type_def, AllCaseEqs()]) >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path`,`a`] mp_tac) >>
  strip_tac >> Cases_on `evaluate_subscripts tv a [sb]` >> gnvs[] >>
  rename1 `evaluate_subscripts tv a [sb] = INL child` >>
  `val_in_memory child_tv child (b + delta) mem` by
    (qpat_x_assum `value_has_type _ _ \/ _` strip_assume_tac
     >- (drule_all mem_step_offset_memory >> simp[]) >>
     gvs[] >> drule_all mem_step_default_memory >> simp[]) >>
  drule_all mem_step_selection_closed >> disch_then assume_tac >>
  `b + (delta + tail_delta) = (b + delta) + tail_delta` by decide_tac >>
  asm_rewrite_tac[] >> first_x_assum irule >>
  qexistsl [`child`,`child_tv`] >> simp[]
QED

Theorem mem_path_selection_sub_layout:
  !path itv iv k tv v.
    value_has_type itv iv /\
    mem_path_offset itv path = SOME (k,tv) /\
    evaluate_subscripts itv iv path = INL v ==>
    sub_layout itv iv k tv v
Proof
  rpt gen_tac >> strip_tac >> simp[sub_layout_def] >>
  conj_tac
  >- (drule mem_path_offset_sound >> simp[]) >>
  rpt strip_tac >> irule mem_path_selection_memory >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `path` >> simp[]
QED
