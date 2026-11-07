(* Boundary facts for the supported storage/transient Append case. *)
Theory bodyAppendStorageFacts
Ancestors
  bodySim supportedExprForms supportedTypes vyperValue vyperTypeSystem
  compileVyper compileEnv vyperAST words supportedDecls vyperInterpreter
  vyperState bodyStorageMetadata exprOpenCases vyperTypeEnv
  exprSimHyps finite_map vyperTypeInvariants

Theorem supported_append_storage_decl:
  supported_storage_dynamic_array tops nid ==>
  ?elem n slot mut.
    supported_variable_decl tops nid =
      SOME (Private, mut, ArrayT elem (Dynamic n), SOME slot) /\
    (mut = Storage \/ mut = Transient) /\ supported_full_word_type elem
Proof
  simp[supported_storage_dynamic_array_def] >>
  Cases_on `supported_variable_decl tops nid` >> simp[] >>
  rename1 `SOME x` >> PairCases_on `x` >>
  Cases_on `x0` >> Cases_on `x1` >> Cases_on `x2` >>
  Cases_on `x3` >> simp[] >>
  rename1 `ArrayT elem bd` >> Cases_on `bd` >> simp[] >>
  metis_tac[]
QED

Theorem supported_append_element_layout:
  supported_full_word_type elem ==>
  is_word_type elem /\
  ?tv. evaluate_type tenv elem = SOME tv /\ type_slot_size tv = 1
Proof
  rw[supported_full_word_type_def] >>
  simp[is_word_type_def, evaluate_type_def, type_slot_size_def]
QED

Theorem append_capacity_word_bound:
  supported_full_word_type elem /\
  assignable_type tenv (ArrayT elem (Dynamic n)) ==>
  0 < n /\ n + 1 < dimword(:256)
Proof
  strip_tac >>
  drule supported_append_element_layout >>
  disch_then (qspec_then `tenv` strip_assume_tac) >>
  gvs[assignable_type_def, well_formed_type_def, evaluate_type_def,
      type_slot_size_def, bound_length_def]
QED

Theorem supported_append_capacity_lookup:
  !tops src id vis mut elem n slot.
    supported_variable_decl tops (src,id) =
      SOME (vis,mut,ArrayT elem (Dynamic n),slot) ==>
    src = NONE /\
    build_dynarray_capacity (collect_module_vars tops) (NONE,id) = n
Proof
  Induct >> simp[supported_variable_decl_def] >>
  Cases >>
  simp[supported_variable_decl_def, collect_module_vars_def,
       build_dynarray_capacity_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), dynarray_capacity_of_type_def] >>
  first_x_assum drule >> strip_tac >> simp[] >>
  CASE_TAC >> simp[] >> metis_tac[]
QED

Theorem body_append_capacity_lookup:
  body_inv tops ctx cenv cx /\
  supported_variable_decl tops nid =
    SOME (vis,mut,ArrayT elem (Dynamic n),slot) ==>
  cenv.ce_module_dynarray_capacity nid = n
Proof
  Cases_on `nid` >> strip_tac >>
  drule supported_append_capacity_lookup >> strip_tac >>
  gvs[body_inv_def]
QED

Theorem append_storage_target_eval:
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,key) /\
  lookup_var_slot_from_layout cx tr src key = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  eval_target_place cx (TopLevelNameTarget (src,id)) es =
    (INL (StoragePlace tr (n2w slot) tv), es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tv])
Proof
  strip_tac >>
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def,
       get_place_def, LET_THM, ignore_bind_def, record_storage_event_def]
QED

Theorem body_append_root_metadata:
  body_inv tops ctx cenv cx /\
  supported_variable_decl tops nid =
    SOME (vis,mut,ArrayT elem (Dynamic n),slot) ==>
  cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic n)) /\
  cenv.ce_hashmap_info nid = NONE /\
  cenv.ce_module_dynarray_capacity nid = n
Proof
  Cases_on `nid` >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  `ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops))`
    by fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  drule_all body_append_capacity_lookup >>
  fs[body_inv_def]
QED

Theorem append_typed_storage_target:
  env_consistent env cx es /\
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops <> NONE /\
  type_place_target env (TopLevelNameTarget (src,id)) = SOME (Type ty) ==>
  ?tr key slot tv.
    find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,key) /\
    lookup_var_slot_from_layout cx tr src key = SOME slot /\
    evaluate_type (get_tenv cx) ty = SOME tv
Proof
  simp[type_place_target_TopLevelNameTarget] >> rpt strip_tac
  >- (gvs[env_consistent_def, env_context_consistent_def] >>
      qpat_x_assum `!src id ty. FLOOKUP env.bare_global_assignable _ = SOME _ ==> _`
        drule >> strip_tac >> gvs[]) >>
  drule_all env_consistent_toplevel_storage_static >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

Theorem body_append_runtime_metadata:
  body_inv tops ctx cenv cx /\
  supported_storage_dynamic_array tops (src,id) /\
  env_consistent env cx es /\
  type_place_target env (TopLevelNameTarget (src,id)) = SOME (Type ty) ==>
  ?elem n tr key slot tv.
    ty = ArrayT elem (Dynamic n) /\ supported_full_word_type elem /\
    cenv.ce_module_var_type (src,id) = SOME ty /\
    cenv.ce_module_dynarray_capacity (src,id) = n /\
    find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,key) /\
    lookup_var_slot_from_layout cx tr src key = SOME slot /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (StoragePlace tr (n2w slot) tv), es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tv])
Proof
  strip_tac >>
  drule supported_append_storage_decl >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  drule_all body_append_root_metadata >> strip_tac >>
  drule supported_variable_decl_runtime_lookup >> simp[] >> strip_tac >>
  `get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `find_var_decl_by_name id tops <> NONE` by simp[] >>
  drule_all append_typed_storage_target >> strip_tac >>
  drule find_var_decl_storage_mem >> strip_tac >>
  `ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops))`
    by fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `ty = ArrayT elem (Dynamic n)` by
    (fs[body_inv_def] >> metis_tac[optionTheory.SOME_11]) >>
  gvs[] >> drule_all append_storage_target_eval >>
  metis_tac[]
QED

Theorem append_storage_compiler_location:
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,key) /\
  lookup_var_slot_from_layout cx tr src key = SOME slot ==>
  FLOOKUP cenv.ce_module_vars (src,id) =
    SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))
Proof
  Cases_on `tr` >>
  simp[storage_vars_rel_def, transient_vars_rel_def] >> rpt strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  simp[var_decl_transient_def]
QED

Theorem append_typing_target:
  type_stmt env ret_ty (Append tgt e) = SOME env' ==>
  ?elem n.
    type_place_target env tgt = SOME (Type (ArrayT elem (Dynamic n))) /\
    well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) elem /\
    assignable_type env.type_defs elem
Proof
  simp[Once type_stmt_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem body_append_target_bounds:
  body_inv tops ctx cenv cx /\
  supported_storage_dynamic_array tops (src,id) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Append (TopLevelNameTarget (src,id)) e) = SOME env' ==>
  ?elem n tr key slot tv.
    supported_full_word_type elem /\ 0 < n /\ n + 1 < dimword(:256) /\
    cenv.ce_module_var_type (src,id) = SOME (ArrayT elem (Dynamic n)) /\
    cenv.ce_module_dynarray_capacity (src,id) = n /\
    find_var_decl_by_name id tops =
      SOME (StorageVarDecl tr (ArrayT elem (Dynamic n)),key) /\
    lookup_var_slot_from_layout cx tr src key = SOME slot /\
    evaluate_type (get_tenv cx) (ArrayT elem (Dynamic n)) = SOME tv /\
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (StoragePlace tr (n2w slot) tv), es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tv])
Proof
  strip_tac >> drule append_typing_target >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  drule_all body_append_runtime_metadata >> strip_tac >> gvs[] >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `assignable_type env.type_defs
     (ArrayT elem (Dynamic (cenv.ce_module_dynarray_capacity (src,id))))` by
    simp[assignable_type_def, well_formed_type_def] >>
  drule_all append_capacity_word_bound >> strip_tac >>
  metis_tac[]
QED

(* A word type takes no wider type (type_widens_to). *)
Theorem type_widens_to_word:
  !tenv t u. type_widens_to tenv t u /\ is_word_type u ==> t = u
Proof
  metis_tac[compileEnvTheory.type_widens_to_word]
QED
