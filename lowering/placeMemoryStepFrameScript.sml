Theory placeMemoryStepFrame
Ancestors
  compileEnv placeMemoryDeadSuffix placeMemoryFieldRebuild placeMemoryIndexRebuild
  vyperTypeDefaults exprSimProps
  vyperPlaceStatePreservation vyperAssignPreservesType vyperValueOperation
  exprSimAggregateEncoding exprSimPop valueEncoding valueEncodingProps valueEncodingTyping
  placeMemoryTypedBase vyperState vyperTyping loweringPosts arithmetic list rich_list alist

Theorem typed_memory_step_read:
  value_has_type tv a /\ well_formed_type_value tv /\
  val_in_memory tv a off mem /\ mem_step_offset tv sb = SOME (k,etv) /\
  evaluate_subscripts tv a [sb] = INL child ==>
  value_has_type etv child /\ well_formed_type_value etv /\
  val_in_memory etv child (off+k) mem
Proof
  strip_tac >>
  `mem_path_offset tv [sb] = SOME (k,etv)` by
    simp[mem_path_offset_def] >>
  drule mem_path_offset_sound >> strip_tac >>
  `subscript_type tv sb = SOME etv` by
    gvs[subscripts_type_def, AllCaseEqs()] >>
  conj_tac >- metis_tac[evaluate_subscripts_type] >>
  conj_tac >- metis_tac[subscript_type_well_formed] >>
  Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >> Cases_on `tv` >>
      gvs[mem_step_offset_def]
      >- suspend "tuple" >> suspend "array") >>
  Cases_on `tv` >> gvs[mem_step_offset_def] >> suspend "field"
QED

Resume typed_memory_step_read[tuple]:
  Cases_on `a` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  gvs[evaluate_subscripts_def, array_index_def, oEL_def, AllCaseEqs(),
      val_in_memory_tuple] >>
  gvs[oEL_THM, AllCaseEqs()] >>
  `LENGTH l' = LENGTH l` by
    gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  gvs[tuple_in_memory_iff_EL]
QED
Resume typed_memory_step_read[array]:
  Cases_on `a` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> Cases_on `b` >>
  gvs[value_has_type_def, mem_step_offset_def, evaluate_subscripts_def,
      array_index_def, AllCaseEqs(), oEL_THM, val_in_memory_dynarray]
  >- (drule_all elems_in_memory_EL >> simp[AC ADD_ASSOC ADD_COMM]) >>
  drule_all typed_memory_sarray_element >> simp[]
QED
Resume typed_memory_step_read[field]:
  Cases_on `a` >> gvs[value_has_type_def] >>
  gvs[evaluate_subscripts_def, AllCaseEqs(), val_in_memory_struct] >>
  qpat_x_assum `well_formed_type_value _` kall_tac >>
  qpat_x_assum `mem_path_offset _ _ = _` kall_tac >>
  qpat_x_assum `subscripts_type _ _ = _` kall_tac >>
  qpat_x_assum `_ <= type_memory_size _` kall_tac >>
  qpat_x_assum `subscript_type _ _ = _` kall_tac >>
  rpt (pop_assum mp_tac) >>
  map_every qid_spec_tac [`off`, `k`, `etv`, `child`, `l'`] >>
  Induct_on `l` >> simp[mem_field_offset_def] >>
  gen_tac >> PairCases_on `h` >>
  Cases_on `l'` >> simp[value_has_type_def] >>
  PairCases_on `h` >>
  simp[value_has_type_def, val_in_memory_def, mem_field_offset_def] >>
  rpt gen_tac >> IF_CASES_TAC >>
  gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  PairCases_on `z` >> gvs[] >>
  first_x_assum drule_all >> simp[AC ADD_ASSOC ADD_COMM]
QED
Finalise typed_memory_step_read

Theorem typed_memory_step_restore:
  value_has_type tv a /\ well_formed_type_value tv /\
  val_in_memory tv a off mem /\ mem_step_offset tv sb = SOME (k,etv) /\
  evaluate_subscripts tv a [sb] = INL child /\
  val_in_memory etv child (off+k) mem' /\
  (!b n. off <= b /\ b+n <= off+type_memory_size tv /\
    (b+n <= off+k \/ off+k+type_memory_size etv <= b) ==>
    mem_bytes_at b n mem' = mem_bytes_at b n mem) ==>
  val_in_memory tv a off mem'
Proof
  strip_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >> Cases_on `tv` >>
      gvs[mem_step_offset_def]
      >- suspend "tuple" >> suspend "array") >>
  Cases_on `tv` >> gvs[mem_step_offset_def] >> suspend "field"
QED

Resume typed_memory_step_restore[tuple]:
  Cases_on `a` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  gvs[evaluate_subscripts_def, array_index_def, AllCaseEqs(), oEL_THM,
      val_in_memory_tuple] >>
  `LENGTH l' = LENGTH l` by
    gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  gvs[type_memory_size_def] >>
  `tuple_in_memory (LUPDATE (EL (Num i) l') (Num i) l') l off mem'` by
    (irule tuple_update_bounded_frame >> simp[] >>
     qexists_tac `mem` >> simp[type_memory_size_def] >> first_assum ACCEPT_TAC) >>
  gvs[LUPDATE_SAME]
QED
Resume typed_memory_step_restore[array]:
  Cases_on `a` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> Cases_on `b` >>
  gvs[value_has_type_def, mem_step_offset_def, type_memory_size_def]
  >- suspend "dynamic" >> suspend "sparse"
QED
Resume typed_memory_step_restore[dynamic]:
  gvs[evaluate_subscripts_def, array_index_def, AllCaseEqs(), oEL_THM] >>
  `elems_val_wf l etv` by
    (drule (cj 4 value_has_type_val_wf) >> simp[]) >>
  `val_in_memory (ArrayTV etv (Dynamic n))
     (ArrayV (DynArrayV (LUPDATE (EL (Num i) l) (Num i) l))) off mem'` by
    (irule dynamic_array_update_frame >> simp[] >>
     qexists_tac `mem` >> simp[LEFT_ADD_DISTRIB] >> first_assum ACCEPT_TAC) >>
  gvs[LUPDATE_SAME]
QED
Resume typed_memory_step_restore[sparse]:
  gvs[evaluate_subscripts_def, array_index_def, AllCaseEqs()] >>
  (irule typed_memory_sarray_intro >>
  reverse conj_tac >- simp[value_has_type_def] >>
  qx_gen_tac `j` >> strip_tac >> Cases_on `j = Num i` >> simp[] >>
  irule val_in_memory_mem_agree >>
  conj_tac
  >- (irule typed_memory_sparse_lookup_wf >>
      qexists_tac `n` >> irule (cj 3 value_has_type_val_wf) >>
      first_assum ACCEPT_TAC) >>
  qexistsl_tac [`type_memory_size etv`, `mem`] >> simp[] >>
  reverse conj_tac >- (drule_all typed_memory_sarray_element >> simp[]) >>
  sym_tac >>
  qspec_then `0:num` (irule o SRULE []) uniform_memory_cell_frame >>
  qexistsl_tac [`n`, `Num i`] >> simp[LEFT_ADD_DISTRIB] >>
  first_assum ACCEPT_TAC)
QED
Resume typed_memory_step_restore[field]:
  Cases_on `a` >> gvs[value_has_type_def] >>
  gvs[evaluate_subscripts_def, AllCaseEqs(), type_memory_size_def] >>
  `AFUPDKEY s (K child) l' = l'` by
    (qpat_x_assum `ALOOKUP l' s = SOME child` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Induct_on `l'` >> simp[AFUPDKEY_def] >>
     gen_tac >> PairCases_on `h` >> simp[AFUPDKEY_def] >>
     Cases_on `h0 = s` >> simp[] >> strip_tac >> gvs[]) >>
  `val_in_memory (StructTV l) (StructV (AFUPDKEY s (K child) l')) off mem'` by
    (irule struct_update_bounded_frame >> simp[value_has_type_def] >>
     qexists_tac `mem` >>
     simp[value_has_type_def, AC ADD_ASSOC ADD_COMM] >> first_assum ACCEPT_TAC) >>
  gvs[]
QED
Finalise typed_memory_step_restore

Theorem typed_memory_step_unread_frame:
  value_has_type tv a /\ well_formed_type_value tv /\
  val_in_memory tv a off mem /\ mem_step_offset tv sb = SOME (k,etv) /\
  (!child. evaluate_subscripts tv a [sb] <> INL child) /\
  (!b n. off <= b /\ b+n <= off+type_memory_size tv /\ b+n <= off+k ==>
    mem_bytes_at b n mem' = mem_bytes_at b n mem) ==>
  val_in_memory tv a off mem'
Proof
  strip_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >> Cases_on `tv` >>
      gvs[mem_step_offset_def]
      >- suspend "tuple" >> suspend "array") >>
  Cases_on `tv` >> gvs[mem_step_offset_def] >> suspend "field"
QED
Resume typed_memory_step_unread_frame[tuple]:
  Cases_on `a` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `LENGTH l' = LENGTH l` by
    gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  gvs[evaluate_subscripts_def, array_index_def, oEL_THM]
QED
Resume typed_memory_step_unread_frame[array]:
  Cases_on `a` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> Cases_on `b` >>
  gvs[value_has_type_def, mem_step_offset_def, evaluate_subscripts_def,
      array_index_def, AllCaseEqs(), oEL_THM, type_memory_size_def]
  >- (irule dynamic_array_dead_suffix_frame >>
      conj_tac >- decide_tac >>
      conj_tac
      >- (irule (cj 4 value_has_type_val_wf) >> simp[]) >>
      qexistsl_tac [`off + 32 + Num i * type_memory_size etv`, `mem`] >>
      simp[AC ADD_ASSOC ADD_COMM, LE_MULT_RCANCEL]) >>
  Cases_on `ALOOKUP l (Num i)` >> gvs[]
QED
Resume typed_memory_step_unread_frame[field]:
  Cases_on `a` >> gvs[value_has_type_def] >>
  drule mem_field_offset_sound >> strip_tac >>
  drule struct_has_type_map_fst >> strip_tac >>
  gvs[evaluate_subscripts_def, AllCaseEqs()] >>
  `ALOOKUP l' s = NONE` by (Cases_on `ALOOKUP l' s` >> gvs[]) >>
  gvs[alistTheory.ALOOKUP_NONE] >>
  metis_tac[alistTheory.ALOOKUP_NONE, optionTheory.NOT_NONE_SOME]
QED
Finalise typed_memory_step_unread_frame

Theorem typed_memory_unread_path_frame:
  !path tv a off mem mem' k ptv.
    value_has_type tv a /\ well_formed_type_value tv /\
    val_in_memory tv a off mem /\ mem_path_offset tv path = SOME (k,ptv) /\
    (!v. evaluate_subscripts tv a path <> INL v) /\
    (!b n. off <= b /\ b+n <= off+type_memory_size tv /\
      (b+n <= off+k \/ off+k+type_memory_size ptv <= b) ==>
      mem_bytes_at b n mem' = mem_bytes_at b n mem) ==>
    val_in_memory tv a off mem'
Proof
  Induct >> simp[mem_path_offset_def, evaluate_subscripts_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >>
  `mem_path_offset tv [h] = SOME (k',etv)` by simp[mem_path_offset_def] >>
  drule mem_path_offset_sound >> strip_tac >>
  `subscript_type tv h = SOME etv` by
    gvs[subscripts_type_def, AllCaseEqs()] >>
  drule evaluate_subscripts_cons_typed >> strip_tac >>
  Cases_on `evaluate_subscripts tv a [h]`
  >- suspend "live" >> suspend "dead"
QED
Resume typed_memory_unread_path_frame[live]:
  drule_all typed_memory_step_read >> strip_tac >>
  qpat_assum `mem_path_offset etv path = _`
    (mp_then Any strip_assume_tac mem_path_offset_sound) >>
  `val_in_memory etv x (off+k') mem'` by
    (first_x_assum irule >> simp[] >>
     conj_tac
     >- (qpat_x_assum `!rest a. _` (qspecl_then [`path`, `a`] mp_tac) >>
         simp[] >> metis_tac[]) >>
     qexists_tac `mem` >>
     reverse conj_tac >- metis_tac[ADD_COMM] >>
     rpt strip_tac >>
     qpat_x_assum `!b n. _` (qspecl_then [`b`, `n`] mp_tac) >>
     (impl_tac >- decide_tac) >> simp[]) >>
  irule typed_memory_step_restore >>
  simp[] >> qexistsl_tac [`x`, `etv`, `k'`, `mem`, `h`] >>
  simp[] >> reverse conj_tac >- metis_tac[ADD_COMM] >>
  rpt strip_tac >>
  qpat_x_assum `!b n. _ ==> mem_bytes_at _ _ _ = _`
    (qspecl_then [`b`, `n`] mp_tac) >>
  (impl_tac >- decide_tac) >> simp[]
QED
Resume typed_memory_unread_path_frame[dead]:
  irule typed_memory_step_unread_frame >>
  simp[] >> qexistsl_tac [`etv`, `k'`, `mem`, `h`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!b n. _ ==> mem_bytes_at _ _ _ = _`
    (qspecl_then [`b`, `n`] mp_tac) >>
  (impl_tac >- decide_tac) >> simp[]
QED
Finalise typed_memory_unread_path_frame
