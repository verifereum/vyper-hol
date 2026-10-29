(* Typing boundary for the scoped-assignment ABI arena write. *)
Theory vyperAbiWriteTyping
Ancestors
  list rich_list alist pair option integer arithmetic
  vyperAST vyperValue vyperValueOperation vyperState vyperTyping
  vyperAssignPreservesType vyperAbiMemoryProps

Theorem array_set_index_result_array:
  array_set_index tv av i v = INL new ==>
  ?av'. new = ArrayV av'
Proof
  Cases_on `av` >>
  simp[array_set_index_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  rpt (CASE_TAC >> gvs[AllCaseEqs()])
QED

(* Kept below the interpreter dependency boundary of vyperArray. *)
Theorem abi_ALOOKUP_insert_sarray_same[local]:
  !k v al. ALOOKUP (insert_sarray k v al) k = SOME v
Proof
  ho_match_mp_tac insert_sarray_ind >> rw[insert_sarray_def]
QED

Theorem abi_array_index_after_set_same[local]:
  !tv av av' i v.
    array_set_index tv av i v = INL (ArrayV av') ==>
    array_index tv av' i = SOME v
Proof
  gen_tac >> Cases >> simp[array_set_index_def, AllCaseEqs()] >>
  rw[] >> simp[array_index_def, oEL_THM, EL_APPEND_EQN, LENGTH_TAKE_EQ,
               abi_ALOOKUP_insert_sarray_same, ALOOKUP_ADELKEY] >>
  qmatch_goalsub_rename_tac `default_value elem` >>
  Cases_on `v = default_value elem` >>
  gvs[ALOOKUP_ADELKEY, abi_ALOOKUP_insert_sarray_same]
QED

Theorem assign_subscripts_result_path:
  !subs tv old op new.
    assign_subscripts tv old subs op = INL new ==>
    ?child. evaluate_subscripts tv new subs = INL child
Proof
  Induct >> simp[evaluate_subscripts_def] >>
  Cases_on `h` >> rpt gen_tac
  >- (rename1 `ValueSubscript index_value` >>
      Cases_on `index_value` >> Cases_on `old` >>
      simp[Once assign_subscripts_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      drule array_set_index_result_array >> strip_tac >> gvs[] >>
      drule abi_array_index_after_set_same >> strip_tac >>
      simp[evaluate_subscripts_def] >>
      first_x_assum drule >> strip_tac >> gvs[]) >>
  Cases_on `old` >> simp[Once assign_subscripts_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[evaluate_subscripts_def, AFUPDKEY_ALOOKUP] >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem abi_field_offset_ALOOKUP:
  !fields id tv.
    ALOOKUP fields id = SOME tv ==>
    ?off. abi_field_offset id fields = SOME (off,tv)
Proof
  Induct >> simp[abi_field_offset_def] >>
  Cases_on `h` >> rw[abi_field_offset_def] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem typed_array_index_capacity:
  value_has_type (ArrayTV elem bd) (ArrayV av) /\
  array_index (ArrayTV elem bd) av i = SOME v ==>
  0 <= i /\ Num i < bound_length bd
Proof
  Cases_on `av` >> Cases_on `bd` >>
  simp[value_has_type_def, array_index_def, bound_length_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac listTheory.oEL_EQ_EL >> decide_tac
QED

Theorem evaluate_subscripts_abi_path:
  !subs tv a child.
    value_has_type tv a /\ well_formed_type_value tv /\
    leaf_type tv subs <> NoneTV /\
    evaluate_subscripts tv a subs = INL child ==>
    ?off. abi_path_offset tv subs = SOME (off,leaf_type tv subs)
Proof
  Induct >> simp[abi_path_offset_def, leaf_type_def] >>
  Cases_on `h` >> rpt gen_tac
  >- (rename1 `ValueSubscript index_value` >>
      Cases_on `index_value` >> Cases_on `tv` >>
      simp[leaf_type_def] >> rpt strip_tac >>
      Cases_on `a` >> gvs[evaluate_subscripts_def, AllCaseEqs()] >>
      rename1 `array_index (ArrayTV elem bd) av index = SOME elem_value` >>
      drule_all typed_array_index_capacity >> strip_tac >>
      fs[well_formed_type_value_def] >>
      `value_has_type elem elem_value` by
        (qspecl_then [`ArrayTV elem bd`, `elem`, `bd`, `av`, `index`, `elem_value`]
           mp_tac array_index_has_type >> simp[]) >>
      first_x_assum drule_all >> strip_tac >>
      simp[abi_path_offset_def, abi_subscript_offset_def]) >>
  Cases_on `tv` >> simp[leaf_type_def, AllCaseEqs()] >>
  rpt strip_tac >> Cases_on `a` >>
  gvs[evaluate_subscripts_def, AllCaseEqs()] >>
  rename1 `value_has_type (StructTV fields) (StructV vals)` >>
  rename1 `ALOOKUP vals field_name = SOME field_value` >>
  fs[value_has_type_def] >>
  drule_all struct_field_has_type >> strip_tac >> gvs[] >>
  rename1 `ALOOKUP fields field_name = SOME field_tv` >>
  `well_formed_type_value field_tv` by
    (fs[well_formed_type_value_def, EVERY_MEM] >>
     `MEM (field_name,field_tv) fields` by metis_tac[ALOOKUP_MEM] >>
     qpat_x_assum `!e. MEM e fields ==> _`
       (qspec_then `(field_name,field_tv)` mp_tac) >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  drule abi_field_offset_ALOOKUP >> strip_tac >>
  simp[abi_path_offset_def, abi_subscript_offset_def]
QED

Theorem evaluate_subscripts_leaf_well_typed:
  !subs tv a v.
    evaluate_subscripts tv a subs = INL v /\
    value_has_type tv a /\
    well_formed_type_value tv /\
    leaf_type tv subs <> NoneTV ==>
    value_has_type (leaf_type tv subs) v /\
    well_formed_type_value (leaf_type tv subs)
Proof
  Induct >> simp[evaluate_subscripts_def, leaf_type_def] >>
  gen_tac >> Cases_on `h` >>
  simp[evaluate_subscripts_def, leaf_type_def] >>
  rpt gen_tac >> strip_tac
  >- (
    Cases_on `v` >> gvs[evaluate_subscripts_def, AllCaseEqs()] >>
    Cases_on `tv` >> gvs[leaf_type_def, value_has_type_def, well_formed_type_value_def] >>
    drule array_index_has_type >> simp[] >> strip_tac >>
    first_x_assum drule_all >> simp[]) >>
  Cases_on `a` >> gvs[evaluate_subscripts_def, AllCaseEqs()] >>
  Cases_on `tv` >>
  gvs[evaluate_subscripts_def, leaf_type_def, AllCaseEqs(), value_has_type_def] >>
  rename1 `StructTV ftypes` >>
  Cases_on `ALOOKUP ftypes s` >> gvs[] >>
  rename1 `ALOOKUP ftypes s = SOME ftv` >>
  `value_has_type ftv v'` by
    (drule struct_field_has_type >> disch_then drule >> strip_tac >> gvs[]) >>
  `well_formed_type_value ftv` by
    (gvs[well_formed_type_value_def, EVERY_MEM, MEM_MAP] >>
     drule alistTheory.ALOOKUP_MEM >> strip_tac >>
     first_x_assum (qspec_then `(s, ftv)` mp_tac) >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem abi_operation_writes_typed:
  value_has_type tv child /\
  (!v elem cap. op = AppendOp v /\ tv = ArrayTV elem (Dynamic cap) ==>
     value_has_type elem v) ==>
  IS_SOME (abi_operation_writes tv child op)
Proof
  strip_tac >>
  `IS_SOME (encode_value tv child)` by metis_tac[value_has_type_equiv] >>
  Cases_on `tv` >> simp[abi_operation_writes_def] >>
  rename1 `ArrayTV elem bd` >> Cases_on `bd` >>
  simp[abi_operation_writes_def] >>
  Cases_on `child` >> simp[abi_operation_writes_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  simp[abi_operation_writes_def] >>
  Cases_on `op` >> simp[abi_operation_writes_def] >>
  rename1 `AppendOp appended` >>
  `IS_SOME (encode_value elem appended)` by metis_tac[value_has_type_equiv] >>
  gvs[IS_SOME_EXISTS]
QED

Theorem write_abi_immutables_typed_success:
  assign_subscripts tv old subs op = INL new /\
  value_has_type tv new /\ well_formed_type_value tv /\
  leaf_type tv subs <> NoneTV /\
  (!v elem cap. op = AppendOp v /\ leaf_type tv subs = ArrayTV elem (Dynamic cap) ==>
     value_has_type elem v) ==>
  ?rt. write_abi_immutables cx src id tv new subs op st = (INL (),rt)
Proof
  strip_tac >> drule assign_subscripts_result_path >> strip_tac >>
  drule_all evaluate_subscripts_abi_path >> strip_tac >>
  drule_all evaluate_subscripts_leaf_well_typed >> strip_tac >>
  `IS_SOME (abi_operation_writes (leaf_type tv subs) child op)` by
    (irule abi_operation_writes_typed >> simp[]) >>
  gvs[IS_SOME_EXISTS] >>
  simp[write_abi_immutables_def, return_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem write_abi_memory_typed_success:
  assign_subscripts tv old subs op = INL new /\
  value_has_type tv new /\ well_formed_type_value tv /\
  leaf_type tv subs <> NoneTV /\
  (!v elem cap. op = AppendOp v /\ leaf_type tv subs = ArrayTV elem (Dynamic cap) ==>
     value_has_type elem v) ==>
  ?rt. write_abi_memory cx id tv new subs op st = (INL (),rt)
Proof
  strip_tac >> drule assign_subscripts_result_path >> strip_tac >>
  drule_all evaluate_subscripts_abi_path >> strip_tac >>
  drule_all evaluate_subscripts_leaf_well_typed >> strip_tac >>
  `IS_SOME (abi_operation_writes (leaf_type tv subs) child op)` by
    (irule abi_operation_writes_typed >> simp[]) >>
  gvs[IS_SOME_EXISTS] >>
  simp[write_abi_memory_def, return_def] >>
  IF_CASES_TAC >> simp[]
QED
