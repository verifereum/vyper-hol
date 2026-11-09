Theory placeMemoryPathRebuild
Ancestors
  compileEnv placeMemoryStepFrame placeMemoryFieldRebuild placeMemoryIndexRebuild
  vyperState vyperTyping vyperPlaceStatePreservation vyperTypeDefaults
  loweringPosts valueEncoding valueEncodingProps valueEncodingTyping
  vyperValueOperation vyperAssignPreservesType exprSimAggregateEncoding
  arithmetic list alist exprSimProps

Theorem assign_subscripts_cons_typed:
  subscript_type tv sb = SOME etv /\
  assign_subscripts tv a (sb::path) (Replace v) = INL a' ==>
  ?child child'.
    evaluate_subscripts tv a [sb] = INL child /\
    assign_subscripts etv child path (Replace v) = INL child' /\
    assign_subscripts tv a [sb] (Replace child') = INL a'
Proof
  strip_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
      gvs[subscript_type_def] >>
      Cases_on `tv` >> gvs[subscript_type_def] >>
      Cases_on `a` >>
      gvs[assign_subscripts_def, evaluate_subscripts_def, subscript_type_def, AllCaseEqs()] >>
      metis_tac[]) >>
  Cases_on `tv` >> gvs[subscript_type_def, AllCaseEqs()] >>
  Cases_on `a` >>
  gvs[assign_subscripts_def, evaluate_subscripts_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem typed_memory_step_replace:
  value_has_type tv a /\ well_formed_type_value tv /\
  val_in_memory tv a off mem /\ mem_step_offset tv sb = SOME (k,etv) /\
  value_has_type etv child' /\
  assign_subscripts tv a [sb] (Replace child') = INL a' /\
  val_in_memory etv child' (off+k) mem' /\
  (!b n. off <= b /\ b+n <= off+type_memory_size tv /\
    (b+n <= off+k \/ off+k+type_memory_size etv <= b) ==>
    mem_bytes_at b n mem' = mem_bytes_at b n mem) ==>
  val_in_memory tv a' off mem'
Proof
  strip_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >> Cases_on `tv` >>
      gvs[mem_step_offset_def]
      >- suspend "tuple" >> suspend "array") >>
  Cases_on `tv` >> gvs[mem_step_offset_def] >> suspend "field"
QED
Resume typed_memory_step_replace[tuple]:
  Cases_on `a` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  gvs[assign_subscripts_def, array_index_def, array_set_index_def,
      AllCaseEqs(), oEL_THM, val_in_memory_tuple] >>
  `LENGTH l' = LENGTH l` by
    gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  irule tuple_update_bounded_frame >> simp[] >>
  qexists_tac `mem` >> simp[type_memory_size_def] >>
  first_assum ACCEPT_TAC
QED
Resume typed_memory_step_replace[array]:
  Cases_on `a` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> Cases_on `b` >>
  gvs[value_has_type_def, mem_step_offset_def, type_memory_size_def]
  >- suspend "dynamic" >> suspend "sparse"
QED
Resume typed_memory_step_replace[dynamic]:
  gvs[assign_subscripts_def, array_index_def, array_set_index_def,
      AllCaseEqs(), oEL_THM] >>
  `elems_val_wf l etv` by
    (drule (cj 4 value_has_type_val_wf) >> simp[]) >>
  `TAKE (Num i) l ++ [child'] ++ DROP (SUC (Num i)) l =
     LUPDATE child' (Num i) l` by
    (qpat_x_assum `Num i < LENGTH l` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> qspec_tac (`Num i`, `j`) >>
     Induct_on `l` >> Cases_on `j` >> simp[LUPDATE_def]) >>
  pop_assum SUBST1_TAC >>
  irule dynamic_array_update_frame >> simp[] >>
  qexists_tac `mem` >> simp[LEFT_ADD_DISTRIB] >> first_assum ACCEPT_TAC
QED
Resume typed_memory_step_replace[sparse]:
  gvs[assign_subscripts_def, AllCaseEqs()] >>
  gvs[array_set_index_def] >>
  irule sparse_array_update_bounded_frame >>
  qexistsl_tac [`Num i`, `l`, `mem`, `child'`] >>
  simp[value_has_type_def, array_set_index_def, LEFT_ADD_DISTRIB] >>
  first_assum ACCEPT_TAC
QED
Resume typed_memory_step_replace[field]:
  Cases_on `a` >> gvs[value_has_type_def] >>
  gvs[assign_subscripts_def, AllCaseEqs(), type_memory_size_def] >>
  irule struct_update_bounded_frame >> simp[value_has_type_def] >>
  qexists_tac `mem` >>
  simp[value_has_type_def, AC ADD_ASSOC ADD_COMM] >> first_assum ACCEPT_TAC
QED
Finalise typed_memory_step_replace

Theorem assign_subscripts_singleton_typed:
  value_has_type tv a /\ well_formed_type_value tv /\
  subscript_type tv sb = SOME etv /\ value_has_type etv z /\
  assign_subscripts tv a [sb] (Replace z) = INL a' ==>
  value_has_type tv a'
Proof
  strip_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
      gvs[subscript_type_def] >> Cases_on `tv` >>
      gvs[subscript_type_def] >> Cases_on `a` >> gvs[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
      gvs[assign_subscripts_def, array_set_index_def, AllCaseEqs()]
      >- suspend "dynamic" >> suspend "sparse") >>
  Cases_on `tv` >> gvs[subscript_type_def, AllCaseEqs()] >>
  Cases_on `a` >> gvs[value_has_type_def] >>
  gvs[assign_subscripts_def, AllCaseEqs(), value_has_type_def] >>
  irule AFUPDKEY_struct_has_type >> simp[] >> metis_tac[]
QED
Resume assign_subscripts_singleton_typed[dynamic]:
  Cases_on `b` >> gvs[value_has_type_def] >>
  irule TAKE_DROP_all_have_type >> simp[]
QED
Resume assign_subscripts_singleton_typed[sparse]:
  gvs[value_has_type_def] >> IF_CASES_TAC >> simp[] >>
  simp[ADELKEY_SORTED, insert_sarray_SORTED,
       ADELKEY_sparse_has_type, insert_sarray_sparse_has_type]
QED
Finalise assign_subscripts_singleton_typed

Theorem assign_subscripts_type_path_preserves_type:
  !path tv ptv a v a'.
    subscripts_type tv path = SOME ptv /\
    value_has_type tv a /\ well_formed_type_value tv /\
    value_has_type ptv v /\
    assign_subscripts tv a path (Replace v) = INL a' ==>
    value_has_type tv a'
Proof
  Induct >> rpt gen_tac
  >- (strip_tac >> gvs[subscripts_type_def, assign_subscripts_def]) >>
  strip_tac >> gvs[subscripts_type_def, AllCaseEqs()] >>
  drule_all assign_subscripts_cons_typed >> strip_tac >>
  `well_formed_type_value etv` by (irule subscript_type_well_formed >> metis_tac[]) >>
  `value_has_type etv child` by
    (irule evaluate_subscripts_type >>
     qexistsl_tac [`a`, `[h]`, `tv`] >> simp[subscripts_type_def]) >>
  `value_has_type etv child'` by metis_tac[] >>
  irule assign_subscripts_singleton_typed >> metis_tac[]
QED

Theorem typed_memory_replace_path_frame:
  !path tv a a' v off mem mem' k ptv.
    value_has_type tv a /\ well_formed_type_value tv /\
    val_in_memory tv a off mem /\ mem_path_offset tv path = SOME (k,ptv) /\
    value_has_type ptv v /\ assign_subscripts tv a path (Replace v) = INL a' /\
    val_in_memory ptv v (off+k) mem' /\
    (!b n. off <= b /\ b+n <= off+type_memory_size tv /\
      (b+n <= off+k \/ off+k+type_memory_size ptv <= b) ==>
      mem_bytes_at b n mem' = mem_bytes_at b n mem) ==>
    val_in_memory tv a' off mem'
Proof
  Induct >> rpt gen_tac
  >- (strip_tac >> gvs[mem_path_offset_def, assign_subscripts_def]) >>
  strip_tac >> gvs[mem_path_offset_def, AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >>
  `mem_path_offset tv [h] = SOME (k',etv)` by simp[mem_path_offset_def] >>
  drule mem_path_offset_sound >> strip_tac >>
  `subscript_type tv h = SOME etv` by
    gvs[subscripts_type_def, AllCaseEqs()] >>
  drule_all assign_subscripts_cons_typed >> strip_tac >>
  drule_all typed_memory_step_read >> strip_tac >>
  qpat_assum `mem_path_offset etv path = _`
    (mp_then Any strip_assume_tac mem_path_offset_sound) >>
  `value_has_type etv child'` by
    (irule assign_subscripts_type_path_preserves_type >> metis_tac[]) >>
  `val_in_memory etv child' (off+k') mem'` by
    (first_x_assum irule >> simp[] >> qexistsl_tac [`child`, `mem`, `v`] >>
     reverse conj_tac >- metis_tac[ADD_COMM] >>
     rpt strip_tac >>
     qpat_x_assum `!b n. _` (qspecl_then [`b`, `n`] mp_tac) >>
     (impl_tac >- decide_tac) >> simp[]) >>
  irule typed_memory_step_replace >> simp[] >>
  qexistsl_tac [`a`, `child'`, `etv`, `k'`, `mem`, `h`] >>
  reverse conj_tac >- metis_tac[ADD_COMM] >> rpt strip_tac >>
  qpat_x_assum `!b n. _ ==> mem_bytes_at _ _ _ = _`
    (qspecl_then [`b`, `n`] mp_tac) >>
  (impl_tac >- decide_tac) >> simp[]
QED

Theorem typed_memory_replace_entry_frame:
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  val_in_memory entry.type entry.value off mem /\
  mem_path_offset entry.type path = SOME (k,ptv) /\
  value_has_type ptv v /\ replace_memory_entry entry path v = INL entry' /\
  val_in_memory ptv v (off+k) mem' /\
  (!b n. off <= b /\ b+n <= off+type_memory_size entry.type /\
    (b+n <= off+k \/ off+k+type_memory_size ptv <= b) ==>
    mem_bytes_at b n mem' = mem_bytes_at b n mem) ==>
  val_in_memory entry'.type entry'.value off mem'
Proof
  strip_tac >>
  Cases_on `evaluate_subscripts entry.type entry.value path`
  >- (gvs[replace_memory_entry_def, AllCaseEqs()] >>
      irule typed_memory_replace_path_frame >> simp[] >>
      qexistsl_tac [`entry.value`, `k`, `mem`, `path`, `ptv`, `v`] >>
      simp[AC ADD_ASSOC ADD_COMM] >> first_assum ACCEPT_TAC) >>
  gvs[replace_memory_entry_def] >>
  irule typed_memory_unread_path_frame >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`k`, `mem`, `path`, `ptv`] >> simp[] >>
  first_assum ACCEPT_TAC
QED
