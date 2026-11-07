Theory exprSimPopNestedLocalMemory
Ancestors
  compileEnv exprSimPopNestedLocalLayout exprSimPopNestedLocalPath exprSimPop exprSimProps
  valueEncoding valueEncodingProps loweringPosts
  vyperState vyperTyping vyperPlaceWriteSoundness vyperTypeInvariants
  venomState vyperAssignPreservesType arithmetic exprSimAggregateEncoding

Theorem val_in_memory_pop_path:
  !path tv a base k etv n vs updated s.
    mutable_place_path tv path /\ value_has_type tv a /\
    well_formed_type_value tv /\ val_wf tv a /\
    val_in_memory tv a base s.vs_memory /\
    mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
    evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
    assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated ==>
    val_in_memory tv updated base
      (mstore (base + k) (n2w (LENGTH vs - 1)) s).vs_memory
Proof
  Induct_on `path`
  >- (rpt strip_tac >>
      gvs[mem_path_offset_def, evaluate_subscripts_def, assign_subscripts_def,
          val_in_memory_def, val_wf_def] >>
      simp[mstore_mem_word_at_same, rich_listTheory.LENGTH_FRONT] >>
      irule elems_in_memory_FRONT >> simp[] >>
      irule elems_in_memory_mstore_before >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[mem_path_offset_def, AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >>
  rename1 `mem_path_offset etv' path = SOME (restoff,ArrayTV etv (Dynamic n))` >>
  Cases_on `h` >- suspend "array_step" >> suspend "struct_step"
QED

Resume val_in_memory_pop_path[array_step]:
      rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `tv` >>
      gvs[mutable_place_path_def] >>
      qmatch_assum_rename_tac `value_has_type (ArrayTV ct bd) a` >>
      `?arr. a = ArrayV arr` by (Cases_on `a` >> gvs[value_has_type_def]) >>
      pop_assum strip_assume_tac >> gvs[] >>
      gvs[Once evaluate_subscripts_def, Once assign_subscripts_def, AllCaseEqs()] >>
      `etv' = ct` by
        (Cases_on `bd` >> gvs[mem_step_offset_def, AllCaseEqs()]) >> gvs[] >>
      `evaluate_subscripts (ArrayTV ct bd) (ArrayV arr)
         [ValueSubscript (IntV i)] = INL v` by simp[evaluate_subscripts_def] >>
      drule_all array_child_memory >> strip_tac >>
      `well_formed_type_value ct` by gvs[well_formed_type_value_def] >>
      `value_has_type ct v` by
        (irule array_index_has_type >> simp[] >> goal_assum drule >> simp[]) >>
      `val_in_memory ct vj (base' + k')
         (mstore ((base' + k') + restoff) (n2w (LENGTH vs - 1)) s).vs_memory` by
        (first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
         qexists_tac `v` >> simp[]) >>
      qpat_x_assum `!tv a base k etv n vs updated s. _` kall_tac >>
      irule array_child_memory_store >>
      goal_assum (drule_at Any) >>
      qexistsl_tac [`ArrayV arr`, `v`, `vj`, `k'`, `i`] >>
      pure_rewrite_tac[ADD_ASSOC] >>
      simp[Once assign_subscripts_def] >>
      simp[Once assign_subscripts_def] >>
      drule mem_path_offset_sound >>
      simp[type_memory_size_def]
QED

Resume val_in_memory_pop_path[struct_step]:
  rename1 `AttrSubscript id` >> Cases_on `tv` >> gvs[mutable_place_path_def] >>
  qmatch_assum_rename_tac `value_has_type (StructTV fs) a` >>
  `?vals. a = StructV vals` by (Cases_on `a` >> gvs[value_has_type_def]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  gvs[Once evaluate_subscripts_def, Once assign_subscripts_def, AllCaseEqs()] >>
  `ALOOKUP fs id = SOME etv'` by
    (irule (cj 1 mem_field_offset_sound) >> gvs[mem_step_offset_def]) >> gvs[] >>
  `evaluate_subscripts (StructTV fs) (StructV vals) [AttrSubscript id] = INL v` by
    simp[evaluate_subscripts_def] >>
  drule_all struct_child_memory >> strip_tac >>
  `well_formed_type_value etv'` by
    (drule_all well_formed_struct_field_type >> simp[]) >>
  `value_has_type etv' v` by
    (gvs[value_has_type_def] >> drule_all struct_field_has_type >> simp[]) >>
  `val_in_memory etv' v' (base' + k')
     (mstore ((base' + k') + restoff) (n2w (LENGTH vs - 1)) s).vs_memory` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `v` >> simp[]) >>
  qpat_x_assum `!tv a base k etv n vs updated s. _` kall_tac >>
  irule struct_child_memory_store >> goal_assum (drule_at Any) >>
  qexistsl_tac [`StructV vals`, `v`, `v'`, `etv'`, `k'`, `id`] >>
  pure_rewrite_tac[ADD_ASSOC] >>
  simp[Once assign_subscripts_def] >> simp[Once assign_subscripts_def] >>
  drule mem_path_offset_sound >> simp[type_memory_size_def]
QED

Finalise val_in_memory_pop_path

Theorem val_in_memory_mutable_path:
  !path tv a locbase k ct child s.
    mutable_place_path tv path /\ value_has_type tv a /\
    well_formed_type_value tv /\ val_wf tv a /\
    val_in_memory tv a locbase s.vs_memory /\
    mem_path_offset tv path = SOME (k,ct) /\
    evaluate_subscripts tv a path = INL child ==>
    val_wf ct child /\ val_in_memory ct child (locbase + k) s.vs_memory
Proof
  Induct_on `path`
  >- simp[mem_path_offset_def, evaluate_subscripts_def] >>
  rpt gen_tac >> strip_tac >> gvs[mem_path_offset_def, AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >>
  rename1 `mem_path_offset etv path = SOME (restoff,ct)` >>
  Cases_on `h`
  >- suspend "array_step" >>
  suspend "struct_step"
QED

Resume val_in_memory_mutable_path[array_step]:
  rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `tv` >>
  gvs[mutable_place_path_def] >>
  qmatch_assum_rename_tac `value_has_type (ArrayTV et bd) a` >>
  `?arr. a = ArrayV arr` by (Cases_on `a` >> gvs[value_has_type_def]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  gvs[Once evaluate_subscripts_def, AllCaseEqs()] >>
  `etv = et` by (Cases_on `bd` >> gvs[mem_step_offset_def, AllCaseEqs()]) >> gvs[] >>
  `evaluate_subscripts (ArrayTV et bd) (ArrayV arr)
     [ValueSubscript (IntV i)] = INL v` by simp[evaluate_subscripts_def] >>
  drule_all array_child_memory >> strip_tac >>
  `well_formed_type_value et` by gvs[well_formed_type_value_def] >>
  `value_has_type et v` by
    (irule array_index_has_type >> simp[] >> goal_assum drule >> simp[]) >>
  first_x_assum drule_all >> simp[AC ADD_ASSOC ADD_COMM]
QED

Resume val_in_memory_mutable_path[struct_step]:
  rename1 `AttrSubscript id` >> Cases_on `tv` >> gvs[mutable_place_path_def] >>
  qmatch_assum_rename_tac `value_has_type (StructTV fs) a` >>
  `?vals. a = StructV vals` by (Cases_on `a` >> gvs[value_has_type_def]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  gvs[Once evaluate_subscripts_def, AllCaseEqs()] >>
  `ALOOKUP fs id = SOME etv` by
    (irule (cj 1 mem_field_offset_sound) >> gvs[mem_step_offset_def]) >> gvs[] >>
  `evaluate_subscripts (StructTV fs) (StructV vals) [AttrSubscript id] = INL v` by
    simp[evaluate_subscripts_def] >>
  drule_all struct_child_memory >> strip_tac >>
  `well_formed_type_value etv` by
    (drule_all well_formed_struct_field_type >> simp[]) >>
  `value_has_type etv v` by
    (gvs[value_has_type_def] >> drule_all struct_field_has_type >> simp[]) >>
  first_x_assum drule_all >> simp[AC ADD_ASSOC ADD_COMM]
QED

Finalise val_in_memory_mutable_path

Theorem pop_path_elem_in_memory:
  !path tv a locbase k etv n vs s.
    mutable_place_path tv path /\ value_has_type tv a /\
    well_formed_type_value tv /\ val_wf tv a /\
    val_in_memory tv a locbase s.vs_memory /\
    mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
    evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] ==>
    val_in_memory etv (LAST vs)
      (locbase + k + 32 + (LENGTH vs - 1) * type_memory_size etv)
      (mstore (locbase + k) (n2w (LENGTH vs - 1)) s).vs_memory
Proof
  rpt gen_tac >> strip_tac >> drule_all val_in_memory_mutable_path >>
  simp[val_wf_def, val_in_memory_def] >> strip_tac >>
  `elems_in_memory vs (locbase + k + 32) etv
     (mstore (locbase + k) (n2w (LENGTH vs - 1)) s).vs_memory` by
    (irule elems_in_memory_mstore_before >> simp[]) >>
  drule elems_in_memory_EL >>
  disch_then (qspec_then `LENGTH vs - 1` mp_tac) >>
  `0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
  simp[listTheory.LAST_EL, PRE_SUB1]
QED
