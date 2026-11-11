Theory targetStorageReadRoot
Ancestors
  stmtLowering targetPlaceSim targetPlaceSimCasesBase allocLimits vyperSubscriptOverlap list
  vyperStoragePlaceProvenance vyperInterpreter vyperState
  vyperStorageLayoutSafety vyperStoragePlaceRegion words

Theorem target_root_state_read:
  !bt ns. target_root bt = TopLevelNameTarget ns ==>
  MEM (ReadAcc (StateRef ns)) (accesses_expr (target_to_expr bt))
Proof
  ho_match_mp_tac base_assignment_target_induct >>
  simp[target_root_def, target_to_expr_def, expr_accesses_def,
       accesses_expr_def] >> metis_tac[]
QED

Theorem nonconstant_state_read_member:
  !accs mods src id.
  MEM (ReadAcc (StateRef (src,id))) accs /\
  (!ts. ALOOKUP mods src = SOME ts ==> ~constant_decl id ts) ==>
  MEM (StateRef (src,id)) (nonconstant_reads mods accs)
Proof
  Induct_on `accs` >> simp[nonconstant_reads_def] >>
  Cases_on `h` >> simp[nonconstant_reads_def] >>
  Cases_on `v` >> simp[nonconstant_reads_def] >>
  PairCases_on `p` >> simp[nonconstant_reads_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP mods p0` >> simp[] >>
  IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Triviality extend_place_named_region:
  (case pv of
     PlaceR (StoragePlace tr slot leaf) =>
       (?keys root tv path delta.
         declared_storage_region cx mid name keys = SOME (tr,root,tv) /\
         storage_subregion tv path delta leaf /\ slot = root + n2w delta)
   | HashMapRef tr slot kt vt =>
       (?prefix. !subs leaf_slot leaf_tv.
         resolve_hashmap_leaf (get_tenv cx) slot (HashMapT kt vt) subs =
           SOME (leaf_slot,leaf_tv) ==>
         declared_storage_region cx mid name (prefix ++ subs) = SOME (tr,leaf_slot,leaf_tv))
   | _ => T) /\
  extend_place cx pv sb st = (INL next,st') ==>
  (case next of
     PlaceR (StoragePlace tr slot leaf) =>
       (?keys root tv path delta.
         declared_storage_region cx mid name keys = SOME (tr,root,tv) /\
         storage_subregion tv path delta leaf /\ slot = root + n2w delta)
   | HashMapRef tr slot kt vt =>
       (?prefix. !subs leaf_slot leaf_tv.
         resolve_hashmap_leaf (get_tenv cx) slot (HashMapT kt vt) subs =
           SOME (leaf_slot,leaf_tv) ==>
         declared_storage_region cx mid name (prefix ++ subs) = SOME (tr,leaf_slot,leaf_tv))
   | _ => T)
Proof
  Cases_on `pv` >> simp[extend_place_def, raise_def]
  >- (Cases_on `p` >> simp[extend_place_def, raise_def]
      >- (simp[bind_def, return_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
          drule extend_storage_place_subregion >> strip_tac >> gvs[] >>
          drule_all storage_subregion_append >> strip_tac >>
          goal_assum (drule_at Any) >>
          qexistsl_tac [`keys`,`root`] >>
          simp[GSYM word_add_n2w, WORD_ADD_ASSOC]) >>
      simp[bind_def, return_def, extend_memory_place_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[bind_def, ignore_bind_def, lift_sum_def, return_def, AllCaseEqs()]) >>
  Cases_on `sb` >>
  simp[extend_place_def, bind_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[value_type_CASE_rator, vyperMiscTheory.option_CASE_rator,
      bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs()]
  >- (qpat_x_assum `!subs leaf_slot leaf_tv. _`
        (qspec_then `[ValueSubscript v']` mp_tac) >>
      simp[resolve_hashmap_leaf_def, subscript_to_value_def] >> strip_tac >>
      qexistsl_tac [`prefix ++ [ValueSubscript v']`,
                    `hashmap_slot c (encode_hashmap_key t v')`,`tv`,`[]`,`0`] >>
      simp[storage_subregion_def, WORD_ADD_0]) >>
  qexists_tac `prefix ++ [ValueSubscript v']` >>
  rpt strip_tac >>
  qpat_x_assum `!subs leaf_slot leaf_tv. _`
    (qspec_then `ValueSubscript v'::subs` mp_tac) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[resolve_hashmap_leaf_def, subscript_to_value_def]
QED

Theorem eval_base_place_named_region:
  !bt cx st pv st' mid name.
  target_root bt = TopLevelNameTarget (mid,name) /\
  eval_base_place cx bt st = (INL pv,st') ==>
  (case pv of
     PlaceR (StoragePlace tr slot leaf) =>
       (?keys root tv path delta.
         declared_storage_region cx mid name keys = SOME (tr,root,tv) /\
         storage_subregion tv path delta leaf /\ slot = root + n2w delta)
   | HashMapRef tr slot kt vt =>
       (?prefix. !subs leaf_slot leaf_tv.
         resolve_hashmap_leaf (get_tenv cx) slot (HashMapT kt vt) subs =
           SOME (leaf_slot,leaf_tv) ==>
         declared_storage_region cx mid name (prefix ++ subs) = SOME (tr,leaf_slot,leaf_tv))
   | _ => T)
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac >>
  simp[target_root_def, Once evaluate_def, bind_def, AllCaseEqs(), get_scopes_def,
       type_check_def, assert_def, ignore_bind_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
   >~ [`eval_base_place cx (TopLevelNameTarget (mid,name)) st = _`]
  >- (gvs[Once evaluate_def] >>
      Cases_on `pv` >> simp[]
      >- (Cases_on `p` >> simp[] >>
          drule lookup_global_storage_region >> strip_tac >>
          qexistsl_tac [`[]`,`c`,`t`,`[]`,`0`] >>
          simp[storage_subregion_def, WORD_ADD_0]) >>
      gvs[lookup_global_def, bind_def, lift_option_type_def,
          return_def, raise_def, AllCaseEqs(),
          vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
          var_decl_info_CASE_rator] >>
      qexists_tac `[]` >> simp[declared_storage_region_def]) >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all extend_place_named_region >> simp[]
QED
