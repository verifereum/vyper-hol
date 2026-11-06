(* Body invariants supply the mixed tuple target boundary. *)
Theory assignTuplePtrMixedReady
Ancestors
  assignTuplePtrBodyReady bodySim bodySimStmtCases bodyExprPreFacts
  tupleTargetStoreProps exprSimHyps exprSimHypsDefs exprSimTopLevelProps
  exprSimFieldLayout exprSimAttributeFields exprSimUnwrap
  accountsRelProps vyperStorageLayoutSafety vyperPlaceResultTyping
  bodyStorageMetadata stmtSimAssignAttr supportedExprForms
  vyperLookupStorage vyperTypeContractStaticMaps supportedTypes supportedDecls supportedStmts
  memoryLocalRhsProps stmtSimDeclStore stmtSimAugAssign exprSimAggregateLayout allocLimits allocLimitsProps
  vyperTypeEnv vyperTypeSystem vyperTyping vyperTypeInvariants
  vyperInterpreter vyperState vyperValue compileEnv exprLoweringProps
  stmtLowering loweringPosts list finite_map words arithmetic

Theorem tuple_find_var_decl_storage_some_ptr:
  !ts vis mut id ty init.
    MEM (VariableDecl vis mut id ty init) ts /\
    (mut = Storage \/ mut = Transient) ==>
    find_var_decl_by_name id ts <> NONE
Proof
  Induct >> simp[] >> Cases >> rw[find_var_decl_by_name_def] >> metis_tac[]
QED

Theorem tuple_env_assignable_find_NONE_ptr:
  env_consistent env cx st /\
  FLOOKUP env.bare_global_assignable (src, id) = SOME ty ==>
  ?ts. get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE
Proof
  rw[env_consistent_def, env_context_consistent_def] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem tuple_supported_scalar_decl_ptr:
  supported_scalar_target tops (src, id) ==>
  src = NONE /\ find_var_decl_by_name id tops <> NONE /\
  ?vis mut ty slot. MEM (VariableDecl vis mut id ty slot) tops /\ is_word_type ty
Proof
  simp[supported_scalar_target_def] >>
  Cases_on `supported_variable_decl tops (src, id)` >> simp[] >>
  rename1 `SOME x` >> PairCases_on `x` >>
  Cases_on `x0` >> Cases_on `x1` >> Cases_on `x3` >> simp[] >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >>
  `find_var_decl_by_name id tops <> NONE` by
    metis_tac[tuple_find_var_decl_storage_some_ptr] >>
  gvs[supported_full_word_type_def] >> first_assum (irule_at Any) >>
  simp[is_word_type_def]
QED

Theorem tuple_supported_field_decl_ptr:
  supported_storage_field_write tops (src, id) fld ==>
  src = NONE /\ find_var_decl_by_name id tops <> NONE /\
  ?mut sid slot. MEM (VariableDecl Private mut id (StructT sid) slot) tops
Proof
  simp[supported_storage_field_write_def, supported_storage_fields_def] >>
  Cases_on `supported_variable_decl tops (src, id)` >> simp[] >>
  rename1 `SOME x` >> PairCases_on `x` >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  Cases_on `x0` >> Cases_on `x1` >> Cases_on `x2` >> Cases_on `x3` >> simp[] >>
  metis_tac[tuple_find_var_decl_storage_some_ptr]
QED

Theorem tuple_target_body_local_aligned_ptr:
  expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty /\
  0 < type_memory_bytes cenv ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) ty tv
Proof
  rpt strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  simp[tuple_target_aligned_local] >> metis_tac[expr_sim_inv_local]
QED

Theorem tuple_target_body_local_layout_ptr:
  expr_sim_inv cenv cx env es /\
  well_typed_atarget env (BaseTarget (NameTarget id)) ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v ==>
  tuple_target_layout es.scopes (BaseTarget (NameTarget id)) ty tv v
Proof
  rpt strip_tac >>
  gvs[well_typed_atarget_def, well_typed_target_def,
      vyperTypeEnvTheory.type_place_target_NameTarget] >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\ entry.assignable` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     metis_tac[]) >>
  `entry.type = tv` by metis_tac[expr_sim_inv_local, optionTheory.SOME_11] >>
  simp[tuple_target_layout_local] >> metis_tac[store_lays_out_typed]
QED

Theorem tuple_target_body_local_room_ptr:
  expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
  FLOOKUP env.var_types id = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  type_memory_size tv + 64 < dimword (:256)
Proof
  rpt strip_tac >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv ty < 2 ** 64` by metis_tac[locals_alloc_ok_def] >>
  metis_tac[allocation_limit_word_room]
QED

Theorem tuple_target_body_toplevel_aligned_ptr:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  supported_scalar_target tops nsid /\
  type_place_target env (TopLevelNameTarget nsid) = SOME (Type ty) /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx (BaseTarget (TopLevelNameTarget nsid)) ty tv
Proof
  Cases_on `nsid` >> rename1 `(src, id)` >> rpt strip_tac >>
  drule tuple_supported_scalar_decl_ptr >> strip_tac >> gvs[] >>
  rename1 `is_word_type declared_ty` >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) = build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all tuple_env_assignable_find_NONE_ptr >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `declared_ty = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  simp[tuple_target_aligned_toplevel] >>
  rpt strip_tac >> irule storage_dead_update_word_region >>
  qexistsl_tac [`NONE`, `id`, `[]`, `tv`] >>
  simp[declared_storage_region_def] >> metis_tac[word_type_slot_size]
QED

Theorem tuple_target_body_field_aligned_ptr:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  supported_storage_field_write tops nsid fld /\
  type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
    SOME (Type ty) /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx
    (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) ty tv
Proof
  Cases_on `nsid` >> rename1 `(src, id)` >> rpt strip_tac >>
  drule tuple_supported_field_decl_ptr >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by fs[body_inv_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[vyperTypeEnvTheory.type_place_target_AttributeTarget,
      vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all tuple_env_assignable_find_NONE_ptr >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ tgt_ty fld = SOME _` >>
  `tgt_ty = StructT sid` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> drule_all build_maps_variable >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  gvs[] >> drule_all attribute_type_struct_field >> strip_tac >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >> gvs[] >>
  drule struct_field_slot_exists >> strip_tac >>
  drule_all struct_field_offset_slots_eq >> strip_tac >>
  simp[tuple_target_aligned_field] >>
  rpt gen_tac >> irule storage_dead_update_struct_word_field >>
  goal_assum (drule_at Any) >> qexistsl_tac [`NONE`, `id`] >>
  simp[declared_storage_region_def] >> metis_tac[word_type_slot_size]
QED

Theorem tuple_target_body_ready_ptr:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  locals_alloc_ok cenv env /\ well_typed_atarget env g ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ((?id lty. g = BaseTarget (NameTarget id) /\
            FLOOKUP env.var_types id = SOME lty /\
            0 < type_memory_bytes cenv lty) \/
   (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
           supported_scalar_target tops nsid) \/
   (?nsid fld fty.
      g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
      supported_storage_field_write tops nsid fld /\
      type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
        SOME (Type fty) /\ is_word_type fty)) ==>
  tuple_target_aligned cenv cx g ty tv /\
  (~is_word_type ty ==> type_memory_size tv + 64 < dimword (:256)) /\
  (!es1 v. expr_sim_inv cenv cx env es1 /\ value_has_type tv v ==>
     tuple_target_layout es1.scopes g ty tv v)
Proof
  rpt strip_tac >> gvs[tuple_target_base_type]
  >- (gvs[vyperTypeEnvTheory.type_place_target_NameTarget] >>
      irule tuple_target_body_local_aligned_ptr >> metis_tac[])
  >- (gvs[vyperTypeEnvTheory.type_place_target_NameTarget] >>
      metis_tac[tuple_target_body_local_room_ptr])
  >- (irule tuple_target_body_local_layout_ptr >>
      simp[well_typed_atarget_def, well_typed_target_def] >> metis_tac[])
  >- (irule tuple_target_body_toplevel_aligned_ptr >> metis_tac[])
  >- (drule_all tuple_target_body_toplevel_aligned_ptr >> Cases_on `nsid` >>
      simp[tuple_target_aligned_toplevel])
  >- simp[tuple_target_layout_def]
  >- (irule tuple_target_body_field_aligned_ptr >> metis_tac[])
  >> simp[tuple_target_layout_def]
QED
