(* Declaration and layout boundary for aggregate storage Append. *)
Theory bodyAppendAggregateMetadata
Ancestors
  bodyAppendStorageFacts bodySim supportedStmts exprSimHyps exprSimHypsDefs
  bodyStorageMetadata exprOpenCases compileEnv loweringStateRelDefs
  vyperTypeSystem vyperTypeValues vyperTypeEnv vyperStorageLayoutSafety
  placeDynLayout vyperValue valueEncodingProps supportedProgram supportedDecls
  supportedTypes

Theorem storage_element_nonword[local]:
  supported_storage_type tops elem /\ ~supported_full_word_type elem ==>
  ~is_word_type elem
Proof
  Cases_on `elem` >>
  simp[is_word_type_def, supported_storage_type_def,
       Once supported_nested_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def, supported_full_word_type_def,
       supported_storage_type_def, Once supported_nested_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_word_type_def]
QED

Theorem body_append_aggregate_metadata:
  body_inv tops ctx cenv cx /\
  supported_variable_decl tops (src,id) =
    SOME (vis,mut,ArrayT elem (Dynamic dn),SOME declared_slot) /\
  (mut = Storage \/ mut = Transient) /\ ~supported_full_word_type elem /\
  supported_stmt tops bindings (Append (TopLevelNameTarget (src,id)) e) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Append (TopLevelNameTarget (src,id)) e) = SOME env' /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget (src,id)) e) ==>
  src = NONE /\ expr_type e = elem /\ ~is_word_type elem /\
  cenv.ce_module_var_type (src,id) = SOME (ArrayT elem (Dynamic dn)) /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_dynarray_capacity (src,id) = dn /\
  ?tr key slot tv.
    get_module_code cx src = SOME tops /\
    find_var_decl_by_name id tops =
      SOME (StorageVarDecl tr (ArrayT elem (Dynamic dn)),key) /\
    lookup_var_slot_from_layout cx tr src key = SOME slot /\
    evaluate_type (get_tenv cx) elem = SOME tv /\
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (StoragePlace tr (n2w slot) (ArrayTV tv (Dynamic dn))),es) /\
    type_memory_bytes cenv elem = 32 * type_slot_size tv /\
    type_memory_bytes cenv elem < 2 ** 64 /\
    0 < dn /\ dn + 1 < dimword(:256) /\ 0 < type_slot_size tv /\
    type_slot_size (ArrayTV tv (Dynamic dn)) < dimword(:256) /\
    declared_storage_region cx src id [] =
      SOME (tr,n2w slot,ArrayTV tv (Dynamic dn)) /\
    w2n (n2w slot : bytes32) + type_slot_size (ArrayTV tv (Dynamic dn)) <=
      dimword(:256) /\
    (storage_vars_rel cenv cx /\ transient_vars_rel cenv cx ==>
      FLOOKUP cenv.ce_module_vars (src,id) =
        SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot)))
Proof
  strip_tac >>
  `expr_type e = elem` by
    (Cases_on `supported_storage_dynamic_array tops (src,id)`
     >- (drule supported_append_storage_decl >> strip_tac >> gvs[]) >>
     gvs[supported_stmt_def]) >>
  drule_all body_append_root_metadata >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >>
  `supported_program tops` by fs[body_inv_def] >>
  `supported_declaration_header tops
     (VariableDecl vis mut id (ArrayT elem (Dynamic dn)) (SOME declared_slot))` by
    metis_tac[supported_program_def, supported_declaration_headers_def,
              listTheory.EVERY_MEM] >>
  `supported_storage_type tops elem` by
    (Cases_on `vis` >> gvs[supported_declaration_header_def,
                           supported_storage_array_depth]) >>
  `~is_word_type elem` by metis_tac[storage_element_nonword] >>
  gvs[] >>
  drule supported_variable_decl_runtime_lookup >> simp[] >> strip_tac >>
  `get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  drule append_typing_target >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `find_var_decl_by_name id tops <> NONE` by simp[] >>
  drule_all append_typed_storage_target >> strip_tac >>
  drule find_var_decl_storage_mem >> strip_tac >>
  `ALL_DISTINCT
    (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops))`
    by fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  gvs[] >>
  `build_var_type_map tops (NONE,id) = cenv.ce_module_var_type (NONE,id)` by
    gvs[body_inv_def] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  (rpt conj_tac
   >- (irule append_storage_target_eval >> simp[evaluate_type_def])
   >- (drule_all expr_sim_inv_memory_size >> simp[type_memory_size_slots])
   >- (drule body_append_element_alloc_bound >> simp[])
   >- (rename1 `0 < type_slot_size etv` >>
       fs[type_slot_size_def] >>
       `cenv.ce_module_dynarray_capacity (NONE,id) <=
        type_slot_size etv * cenv.ce_module_dynarray_capacity (NONE,id)`
         by simp[] >> decide_tac)
   >- simp[declared_storage_region_def, evaluate_type_def]
   >- (`declared_storage_region cx NONE id [] =
          SOME (tr,n2w slot,ArrayTV tv' (Dynamic (cenv.ce_module_dynarray_capacity (NONE,id))))`
         by simp[declared_storage_region_def, evaluate_type_def] >>
       `storage_layout_safe cx` by fs[expr_sim_inv_def] >>
       drule_all storage_layout_safe_region_nonoverflow >> simp[]) >>
   strip_tac >> drule_all append_storage_compiler_location >> simp[])
QED
