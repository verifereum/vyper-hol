(* Current-value layout boundaries, ported from the S1 places proof.
   These say nothing about snapshots or history-only popped paths. *)
Theory bodyPtrSubscriptCurrentMemory
Ancestors
  exprSimAggregateEncoding tupleMemoryLayout exprSimAttributeFields
  exprSimProps vyperPlaceStatePreservation
  vyperPlaceResultTyping vyperTypeInvariants vyperPlaceTyping
  valueEncoding valueEncodingDefs valueEncodingProofs valueEncodingProps loweringPosts
  vyperState vyperTyping vyperTypeSystem vyperValue vyperValueOperation list rich_list pair arithmetic
Libs
  pairLib

Theorem fields_in_memory_mem_field_offset:
  !vals fs off mem id fv k ftv.
    struct_has_type fs vals /\ fields_in_memory vals fs off mem /\
    ALOOKUP vals id = SOME fv /\ mem_field_offset fs id = SOME (k,ftv) ==>
    val_in_memory ftv fv (off + k) mem
Proof
  Induct >> Cases_on `fs` >> simp[value_has_type_def] >>
  PairCases_on `h` >> Cases >>
  rename1 `struct_has_type ((fname,fty)::fts) ((vname,vval)::vrest)` >>
  simp[value_has_type_def, val_in_memory_def, mem_field_offset_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `fname = id` >> gvs[AllCaseEqs()] >>
  rename1 `mem_field_offset fts id = SOME child_offset` >>
  PairCases_on `child_offset` >> gvs[] >>
  first_x_assum drule_all >> simp[AC ADD_ASSOC ADD_COMM]
QED

Theorem array_index_in_memory:
  !tv av off mem i v k etv.
    value_has_type tv (ArrayV av) /\
    val_in_memory tv (ArrayV av) off mem /\
    array_index tv av i = SOME v /\
    mem_step_offset tv (ValueSubscript (IntV i)) = SOME (k,etv) ==>
    val_in_memory etv v (off + k) mem
Proof
  rpt gen_tac >> Cases_on `tv` >> Cases_on `av` >>
  gvs[value_has_type_def] >>
  TRY (rename1 `ArrayTV _ bd` >> Cases_on `bd` >> gvs[value_has_type_def]) >>
  simp[val_in_memory_def, array_index_def, mem_step_offset_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[oEL_THM, AllCaseEqs()]
  >- (drule values_have_types_length >> strip_tac >>
      drule_all tuple_in_memory_element >> simp[GSYM type_memory_size_list_sum])
  >- (drule_all elems_in_memory_EL >> simp[AC ADD_ASSOC ADD_COMM]) >>
  drule_all kvs_in_memory_lookup >> simp[]
QED

Theorem mem_step_offset_current_value:
  !tv a sb v off mem k etv.
    value_has_type tv a /\ val_in_memory tv a off mem /\
    evaluate_subscripts tv a [sb] = INL v /\
    mem_step_offset tv sb = SOME (k,etv) ==>
    val_in_memory etv v (off + k) mem
Proof
  rpt gen_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
      simp[evaluate_subscripts_def] >>
      Cases_on `a` >> simp[evaluate_subscripts_def, AllCaseEqs()] >>
      rpt strip_tac >> drule_all array_index_in_memory >> simp[]) >>
  Cases_on `tv` >> Cases_on `a` >>
  simp[evaluate_subscripts_def, mem_step_offset_def, value_has_type_def,
       val_in_memory_def, AllCaseEqs()] >>
  rpt strip_tac >> drule_all fields_in_memory_mem_field_offset >> simp[]
QED

Theorem mem_path_offset_current_value:
  !path tv a v off mem k ptv.
    value_has_type tv a /\ well_formed_type_value tv /\
    val_in_memory tv a off mem /\
    evaluate_subscripts tv a path = INL v /\
    mem_path_offset tv path = SOME (k,ptv) ==>
    val_in_memory ptv v (off + k) mem
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_path_offset_def, evaluate_subscripts_def] >>
  gvs[mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  rename1 `mem_step_offset tv sb = SOME (delta,etv)` >>
  `mem_path_offset tv [sb] = SOME (delta,etv)` by
    simp[mem_path_offset_def] >>
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
  drule_all mem_step_offset_current_value >> strip_tac >>
  first_x_assum drule_all >> simp[NoAsms, AC ADD_ASSOC ADD_COMM]
QED
