(* Typed replacement in a constructor immutable's current root. *)
Theory immutablePathReplace
Ancestors
  exprSimPopImmutableTarget ctorDeployLoweringNoCtor
  placeMemoryPathRebuild vyperState vyperLookup vyperValueOperation
  immutableEncoding vyperTyping vyperValue

Theorem immutable_replace_path_admissible:
  !path tv a ptv v updated.
    mutable_place_path tv path /\ value_has_type tv a /\
    well_formed_type_value tv /\ immutable_value_admissible tv a /\
    subscripts_type tv path = SOME ptv /\ value_has_type ptv v /\
    immutable_value_admissible ptv v /\
    assign_subscripts tv a path (Replace v) = INL updated ==>
    immutable_value_admissible tv updated
Proof
  Induct_on `path`
  >- simp[subscripts_type_def, assign_subscripts_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `h`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `tv` >>
      gvs[vyperPlaceWriteSoundnessTheory.mutable_place_path_def] >>
      rename1 `ArrayTV ct bd` >>
      Cases_on `a` >> gvs[vyperTypingTheory.value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      gvs[vyperTypingTheory.value_has_type_def]
      >- suspend "sparse"
      >> suspend "dynamic") >>
  Cases_on `tv` >>
  gvs[vyperPlaceWriteSoundnessTheory.mutable_place_path_def] >>
  Cases_on `a` >> gvs[vyperTypingTheory.value_has_type_def] >>
  suspend "struct"
QED

Resume immutable_replace_path_admissible[sparse]:
  Cases_on `bd` >>
  gvs[immutable_value_admissible_def, vyperTypingTheory.value_has_type_def,
      vyperTypingTheory.well_formed_type_value_def,
      subscripts_type_def, subscript_type_def, assign_subscripts_def,
      vyperValueOperationTheory.array_index_def, AllCaseEqs()] >>
  `value_has_type ct v'` by
    (gvs[all_have_type_EVERY, listTheory.oEL_THM, AllCaseEqs()] >>
     metis_tac[listTheory.EVERY_EL]) >>
  `immutable_value_admissible ct v'` by
    (gvs[listTheory.oEL_THM, AllCaseEqs()] >>
     metis_tac[listTheory.EVERY_EL]) >>
  `immutable_value_admissible ct vj` by
    (first_x_assum drule_all >> simp[]) >>
  gvs[array_set_index_def, AllCaseEqs()] >>
  simp[immutable_value_admissible_def, listTheory.IMP_EVERY_LUPDATE,
       rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]
QED

Resume immutable_replace_path_admissible[dynamic]:
  Cases_on `bd` >>
  gvs[immutable_value_admissible_def, vyperTypingTheory.value_has_type_def,
      vyperTypingTheory.well_formed_type_value_def,
      subscripts_type_def, subscript_type_def, assign_subscripts_def,
      vyperValueOperationTheory.array_index_def, AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `assign_subscripts ct child path (Replace v) = INL vj` >>
  `value_has_type ct child /\ immutable_value_admissible ct child` by
    (qpat_x_assum `!tv a ptv v updated. _` kall_tac >>
     conj_tac
     >- (simp[Abbr `child`, default_value_well_typed] >>
         drule_all vyperAssignPreservesTypeTheory.ALOOKUP_sparse_has_type >> simp[]) >>
     simp[Abbr `child`, cj 1 no_ctor_default_admissible] >>
     drule alistTheory.ALOOKUP_MEM >>
     gvs[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  `immutable_value_admissible ct vj` by
    (first_x_assum drule_all >> simp[]) >>
  `immutable_value_admissible (ArrayTV ct (Fixed n))
     (ArrayV (SArrayV (ADELKEY (Num i) l)))` by
    (irule immutable_sparse_admissible_delete >>
     simp[immutable_value_admissible_def]) >>
  `immutable_value_admissible (ArrayTV ct (Fixed n))
     (ArrayV (SArrayV (insert_sarray (Num i) vj l)))` by
    (irule immutable_sparse_admissible_insert >>
     simp[immutable_value_admissible_def]) >>
  qpat_x_assum `!tv a ptv v updated. _` kall_tac >>
  gvs[array_set_index_def, AllCaseEqs()] >>
  Cases_on `vj = default_value ct` >>
  gvs[immutable_value_admissible_def]
QED

Resume immutable_replace_path_admissible[struct]:
  gvs[subscripts_type_def, subscript_type_def, assign_subscripts_def,
      AllCaseEqs()] >>
  `value_has_type etv v'` by
    (drule_all vyperAssignPreservesTypeTheory.struct_field_has_type >>
     strip_tac >> gvs[]) >>
  `well_formed_type_value etv` by
    metis_tac[vyperPlaceStatePreservationTheory.subscript_type_well_formed,
              subscript_type_def] >>
  `immutable_fields_admissible l l'` by
    gvs[immutable_value_admissible_def] >>
  `immutable_value_admissible etv v'` by
    (drule_all immutable_fields_admissible_lookup >> simp[]) >>
  `immutable_value_admissible etv v''` by
    (first_x_assum drule_all >> simp[]) >>
  simp[immutable_value_admissible_def] >>
  irule immutable_fields_admissible_update >>
  goal_assum (drule_at Any) >> simp[]
QED

Finalise immutable_replace_path_admissible

Theorem immutable_word_replacement_admissible:
  word_memory_type tv /\ well_formed_type_value tv /\ value_has_type tv v ==>
  immutable_value_admissible tv v
Proof
  strip_tac >> gvs[loweringSliceTheory.word_memory_type_def]
  >- (Cases_on `bt` >> Cases_on `v` >>
      gvs[value_has_type_def, well_formed_type_value_def,
          immutable_value_admissible_def] >>
      Cases_on `b` >>
      gvs[value_has_type_def, well_formed_type_value_def,
          immutable_value_admissible_def]) >>
  Cases_on `v` >>
  gvs[value_has_type_def, immutable_value_admissible_def]
QED
