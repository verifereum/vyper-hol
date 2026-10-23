(* TOP-LEVEL: stateless declared-region provenance for resolved target places.
   A mapping prefix describes every possible completed key path; a storage
   place retains its declared root and capacity path across RHS effects. *)
Theory vyperStoragePlaceProvenance
Ancestors
  arithmetic list option pair words finite_map
  vyperAST vyperContext vyperMisc vyperValue vyperState vyperInterpreter
  vyperStorageLayoutSafety vyperStoragePlaceRegion vyperPlaceFrames
Libs
  wordsLib

Definition storage_place_region_def:
  storage_place_region cx (StoragePlace tr slot leaf) =
    (?mid var_name keys root tv path delta.
      declared_storage_region cx mid var_name keys = SOME (tr,root,tv) /\
      storage_subregion tv path delta leaf /\ slot = root + n2w delta) /\
  storage_place_region cx (MemoryPlace id path) = T /\
  storage_place_region cx (ImmutablePlace mid id path) = T
End

Definition storage_mapping_region_def:
  storage_mapping_region cx tr slot vt <=>
    ?mid var_name key_prefix. !subs leaf_slot leaf_tv.
      resolve_hashmap_leaf (get_tenv cx) slot vt subs = SOME (leaf_slot,leaf_tv) ==>
      declared_storage_region cx mid var_name (key_prefix ++ subs) =
        SOME (tr,leaf_slot,leaf_tv)
End

(* Non-map values cannot become target places: extend_target_place rejects
   them and get_place does not convert values to places. This predicate is
   deliberately used for target evaluation, not unrestricted extend_place. *)
Definition storage_result_region_def:
  storage_result_region cx (PlaceR p) = storage_place_region cx p /\
  storage_result_region cx (ValueR (HashMapRef tr slot kt vt)) =
    storage_mapping_region cx tr slot (HashMapT kt vt) /\
  storage_result_region cx (ValueR (Value v)) = T /\
  storage_result_region cx (ValueR (ArrayRef tr slot tv bd)) = T
End

Theorem declared_storage_place_region:
  declared_storage_region cx mid var_name keys = SOME (tr,slot,tv) ==>
  storage_place_region cx (StoragePlace tr slot tv)
Proof
  strip_tac >> simp_tac (srw_ss()) [storage_place_region_def] >>
  qexistsl_tac [`mid`,`var_name`,`keys`,`slot`,`tv`,`[]`,`0`] >>
  simp[storage_subregion_def]
QED

Theorem storage_mapping_region_step:
  storage_mapping_region cx tr slot (HashMapT kt vt) ==>
  storage_mapping_region cx tr (hashmap_slot slot (encode_hashmap_key kt key)) vt
Proof
  rewrite_tac [storage_mapping_region_def] >> strip_tac >>
  qexistsl_tac [`mid`,`var_name`,`key_prefix ++ [ValueSubscript key]`] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!subs leaf_slot leaf_tv. _`
    (qspecl_then [`ValueSubscript key::subs`,`leaf_slot`,`leaf_tv`] mp_tac) >>
  pure_once_rewrite_tac [resolve_hashmap_leaf_def] >>
  asm_simp_tac bool_ss
    [subscript_to_value_def, option_case_def, APPEND, GSYM APPEND_ASSOC]
QED

Theorem storage_mapping_region_leaf:
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv ==>
  storage_place_region cx (StoragePlace tr slot tv)
Proof
  strip_tac >>
  qpat_x_assum `storage_mapping_region _ _ _ _` mp_tac >>
  rewrite_tac [storage_mapping_region_def] >> strip_tac >>
  qpat_x_assum `!subs leaf_slot leaf_tv. _`
    (qspecl_then [`[]`,`slot`,`tv`] mp_tac) >>
  asm_simp_tac bool_ss [resolve_hashmap_leaf_def, option_case_def, APPEND_NIL] >>
  strip_tac >> irule declared_storage_place_region >> goal_assum (drule_at Any)
QED

Theorem lookup_global_place_storage_region:
  lookup_global_place cx mid var_name st =
    (INL (PlaceR (StoragePlace tr slot tv)),st') ==>
  declared_storage_region cx mid var_name [] = SOME (tr,slot,tv)
Proof
  simp[lookup_global_place_def, bind_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
      var_decl_info_CASE_rator, bind_def, lift_option_type_def,
      return_def, raise_def, AllCaseEqs()] >>
  simp[declared_storage_region_def]
QED

Theorem lookup_global_place_mapping_region:
  lookup_global_place cx mid var_name st =
    (INL (ValueR (HashMapRef tr slot kt vt)),st') ==>
  storage_mapping_region cx tr slot (HashMapT kt vt)
Proof
  simp[lookup_global_place_def, bind_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
      var_decl_info_CASE_rator, bind_def, lift_option_type_def,
      return_def, raise_def, AllCaseEqs()] >>
  simp_tac (srw_ss()) [storage_mapping_region_def] >>
  qexistsl_tac [`mid`,`var_name`,`[]`] >> rpt gen_tac >> strip_tac >>
  asm_simp_tac (srw_ss()) [declared_storage_region_def]
QED

Theorem lookup_global_place_region:
  lookup_global_place cx mid var_name st = (INL pv,st') ==>
  storage_result_region cx pv
Proof
  Cases_on `pv`
  >- (rename1 `storage_result_region cx (PlaceR resolved_place)` >>
      Cases_on `resolved_place` >>
      simp[storage_result_region_def, storage_place_region_def] >> rpt strip_tac >>
      drule lookup_global_place_storage_region >> strip_tac >>
      drule (SIMP_RULE (srw_ss()) [storage_place_region_def] declared_storage_place_region) >>
      simp[]) >>
  rename1 `storage_result_region cx (ValueR resolved_value)` >>
  Cases_on `resolved_value` >> simp[storage_result_region_def] >> rpt strip_tac >>
  drule lookup_global_place_mapping_region >> simp[]
QED

Theorem resolve_array_element_empty[local]:
  resolve_array_element cx tr slot tv [] st = (INL (slot,tv,[]),st)
Proof
  Cases_on `tv` >> simp[resolve_array_element_def, return_def]
QED

Theorem extend_storage_place_subregion:
  extend_storage_place cx tr slot tv sb st = (INL p,st') ==>
  ?leaf delta. p = StoragePlace tr (slot + n2w delta) leaf /\
    storage_subregion tv [sb] delta leaf
Proof
  Cases_on `tv` >> Cases_on `sb` >>
  simp[extend_storage_place_def, raise_def] >>
  TRY (rename1 `ValueSubscript key` >> Cases_on `key` >>
       simp[extend_storage_place_def, raise_def]) >>
  TRY (rename1 `ArrayTV elem bd` >> Cases_on `bd`) >>
  simp[resolve_array_element_def, bind_def, ignore_bind_def,
       lift_option_type_def, check_def, assert_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[resolve_array_element_empty, vyperMiscTheory.option_CASE_rator,
      vyperMiscTheory.prod_CASE_rator, return_def, raise_def, AllCaseEqs()] >>
  TRY (pairarg_tac >> gvs[return_def]) >>
  simp[storage_subregion_def]
QED

Theorem extend_storage_place_region:
  storage_place_region cx (StoragePlace tr slot tv) /\
  extend_storage_place cx tr slot tv sb st = (INL p,st') ==>
  storage_place_region cx p
Proof
  strip_tac >> drule extend_storage_place_subregion >> strip_tac >>
  qmatch_assum_rename_tac `storage_subregion tv [sb] step_delta leaf` >>
  gvs[storage_place_region_def] >>
  qmatch_assum_rename_tac
    `declared_storage_region cx source_mid source_name source_keys =
       SOME (tr,declared_root,declared_tv)` >>
  qmatch_assum_rename_tac `storage_subregion declared_tv base_path base_delta tv` >>
  drule_all storage_subregion_append >> strip_tac >>
  qexistsl_tac [`source_mid`,`source_name`,`source_keys`,`declared_root`,`declared_tv`,
               `base_path ++ [sb]`,`base_delta + step_delta`] >>
  asm_simp_tac bool_ss [GSYM word_add_n2w, WORD_ADD_ASSOC]
QED

Theorem extend_mapping_place_region:
  storage_mapping_region cx tr slot (HashMapT kt vt) /\
  extend_target_place cx (ValueR (HashMapRef tr slot kt vt)) sb st = (INL pv,st') ==>
  storage_result_region cx pv
Proof
  Cases_on `sb` >>
  simp[extend_target_place_def, extend_place_def, get_Value_def,
       bind_def, lift_sum_def, return_def, raise_def,
       evaluate_subscript_def, AllCaseEqs(), subscript_result_place_def] >>
  rpt strip_tac >>
  gvs[vyperMiscTheory.sum_CASE_rator, return_def, raise_def, AllCaseEqs(),
      subscript_result_place_def, storage_result_region_def] >>
  drule storage_mapping_region_step >>
  disch_then (qspec_then `v` assume_tac) >>
  FIRST [drule_all storage_mapping_region_leaf >> simp[], simp[]]
QED

Theorem extend_target_place_region:
  storage_result_region cx pv /\
  extend_target_place cx pv sb st = (INL next,st') ==>
  storage_result_region cx next
Proof
  Cases_on `pv`
  >- (rename1 `PlaceR resolved_place` >> Cases_on `resolved_place` >>
      simp[storage_result_region_def] >> strip_tac >>
      gvs[extend_target_place_def, extend_place_def, bind_def,
          ignore_bind_def, return_def, AllCaseEqs()] >>
      FIRST [drule_all extend_storage_place_region >>
               simp[storage_result_region_def],
             simp[storage_result_region_def, storage_place_region_def,
                  extend_memory_place_def]]) >>
  rename1 `ValueR resolved_value` >> Cases_on `resolved_value` >>
  simp[storage_result_region_def, extend_target_place_def, raise_def] >>
  metis_tac[SRULE[extend_target_place_def] extend_mapping_place_region]
QED

Theorem eval_base_place_region:
  !bt cx st pv st'.
    eval_base_place cx bt st = (INL pv,st') ==>
    storage_result_region cx pv
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac >> TRY (PairCases_on `p`) >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), get_scopes_def,
       type_check_def, assert_def, ignore_bind_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  FIRST [simp[storage_result_region_def, storage_place_region_def] >> NO_TAC,
         drule lookup_global_place_region >> simp[] >> NO_TAC,
         qmatch_assum_rename_tac `eval_base_place cx child st = (INL child_pv,child_st)` >>
         qpat_x_assum `!y. _` (qspec_then `child` mp_tac) >>
         simp[expr_size_def] >> strip_tac >> first_x_assum drule >> strip_tac >>
         drule_all extend_target_place_region >> simp[]]
QED

Theorem eval_target_place_region:
  eval_target_place cx bt st = (INL p,st') ==>
  storage_place_region cx p
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule eval_base_place_region >> strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def,
                       storage_result_region_def]
QED
