(* Visibility-independent storage bindings and declaration-inert builders.
   Public storage/transient variables and hashmaps also synthesize getters;
   their entry and typing proofs live in entryDispatchProps, entryStateRel
   and supportedGetterProps. FlagDecl/ErrorDecl leave compiler storage and
   function classification unchanged. *)

Theory whitelistVisibility
Ancestors
  bodyAppendStorageFacts entryStateRel bodyStorageMetadata exprOpenCases
  supportedDecls compileVyper constSubst compileEnv vyperTypeEnv vyperTypeContract
  vyperContext vyperInterpreter vyperState vyperTypeInvariants exprSimHyps
  exprSimHypsDefs vyperTypeSystem
  bodySim list finite_map pair

(* ===== Storage variables and hashmaps of any visibility ===== *)

Theorem supported_variable_decl_find_var_decl[local]:
  !tops id vis mut ty slot.
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    supported_variable_decl tops (NONE,id) = SOME (vis,mut,ty,slot) /\
    (mut = Storage \/ mut = Transient) ==>
    find_var_decl_by_name id tops =
      SOME (StorageVarDecl (mut = Transient) ty, id)
Proof
  Induct >- simp[supported_variable_decl_def] >>
  Cases >>
  simp[supported_variable_decl_def, find_var_decl_by_name_def,
       toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  drule supported_variable_decl_mem >> strip_tac >>
  gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!y. _`
    (drule_then mp_tac o REWRITE_RULE [GSYM IMP_DISJ_THM]) >>
  simp[toplevel_vtype_keys_toplevel_def]
QED

(* A storage or transient variable, of any visibility, with a slot: the
   module variables bind its slot, and its declared type is the module's
   type for it. *)
Theorem supported_variable_decl_storage_binding:
  !tops src id vis mut ty slot.
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    supported_variable_decl tops (src,id) = SOME (vis,mut,ty,SOME slot) /\
    (mut = Storage \/ mut = Transient) ==>
    src = NONE /\
    FLOOKUP (add_module_var_locations tops FEMPTY) (NONE,id) =
      SOME (if mut = Transient then TransientLoc (n2w slot)
            else StorageLoc (n2w slot)) /\
    find_var_decl_by_name id tops =
      SOME (StorageVarDecl (mut = Transient) ty, id) /\
    build_var_type_map tops (NONE,id) = SOME ty /\
    build_hashmap_info tops (NONE,id) = NONE
Proof
  rpt gen_tac >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >>
  qpat_x_assum `src = NONE` SUBST_ALL_TAC >>
  `find_var_decl_by_name id tops =
     SOME (StorageVarDecl (mut = Transient) ty, id)` by
    metis_tac[supported_variable_decl_find_var_decl] >>
  drule_all build_maps_variable >> strip_tac >>
  drule_then (qspecl_then [`FEMPTY`, `VariableDecl vis mut id ty (SOME slot)`,
                           `id`] mp_tac) add_module_var_locations_mem >>
  simp[toplevel_vtype_keys_toplevel_def] >> disch_then SUBST1_TAC >>
  gvs[add_module_var_locations_def, FLOOKUP_UPDATE]
QED

Theorem supported_hashmap_decl_mem[local]:
  !tops src id vis tr kt vt slot.
    supported_hashmap_decl tops (src,id) = SOME (vis,tr,kt,vt,slot) ==>
    src = NONE /\ MEM (HashMapDecl vis tr id kt vt slot) tops
Proof
  Induct >> simp[supported_hashmap_decl_def] >> Cases >>
  rw[supported_hashmap_decl_def] >> metis_tac[]
QED

Theorem supported_hashmap_decl_find_var_decl[local]:
  !tops id vis tr kt vt slot.
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    supported_hashmap_decl tops (NONE,id) = SOME (vis,tr,kt,vt,slot) ==>
    find_var_decl_by_name id tops = SOME (HashMapVarDecl tr kt vt, id) /\
    build_hashmap_info tops (NONE,id) = SOME (tr,kt,vt)
Proof
  Induct >- simp[supported_hashmap_decl_def] >>
  Cases >>
  simp[supported_hashmap_decl_def, find_var_decl_by_name_def,
       build_hashmap_info_def, toplevel_vtype_keys_toplevel_def,
       ALL_DISTINCT_APPEND] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  drule supported_hashmap_decl_mem >> strip_tac >>
  gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!y. _`
    (drule_then mp_tac o REWRITE_RULE [GSYM IMP_DISJ_THM]) >>
  simp[toplevel_vtype_keys_toplevel_def]
QED

(* A hashmap of any visibility with a slot: the module variables bind its
   slot, and the hashmap table holds its key and value types. *)
Theorem supported_hashmap_decl_storage_binding:
  !tops src id vis tr kt vt slot.
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    supported_hashmap_decl tops (src,id) = SOME (vis,tr,kt,vt,SOME slot) ==>
    src = NONE /\
    FLOOKUP (add_module_var_locations tops FEMPTY) (NONE,id) =
      SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot)) /\
    find_var_decl_by_name id tops = SOME (HashMapVarDecl tr kt vt, id) /\
    build_hashmap_info tops (NONE,id) = SOME (tr,kt,vt)
Proof
  rpt gen_tac >> strip_tac >>
  drule supported_hashmap_decl_mem >> strip_tac >> gvs[] >>
  drule_all supported_hashmap_decl_find_var_decl >> strip_tac >>
  drule_then (qspecl_then [`FEMPTY`, `HashMapDecl vis tr id kt vt (SOME slot)`,
                           `id`] mp_tac) add_module_var_locations_mem >>
  simp[toplevel_vtype_keys_toplevel_def, add_module_var_locations_def,
       FLOOKUP_UPDATE]
QED

(* With distinct names, one declaration per module-variable key. *)
Theorem toplevel_vtype_key_unique[local]:
  !tops a b k.
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    MEM a tops /\ MEM b tops /\
    toplevel_vtype_keys_toplevel (NONE:num option) a = [k] /\
    toplevel_vtype_keys_toplevel (NONE:num option) b = [k] ==>
    a = b
Proof
  Induct >> simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >> metis_tac[MEM]
QED

(* No immutable shares a name with a declared storage variable or hashmap,
   so add_immutable_locations keeps its binding. *)
Theorem add_immutable_locations_keeps_declared[local]:
  !tops sft top id.
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    MEM top tops /\
    toplevel_vtype_keys_toplevel (NONE:num option) top = [(NONE,id)] /\
    (!vis ty slot. top <> VariableDecl vis Immutable id ty slot) ==>
    FLOOKUP (add_immutable_locations sft tops 0
               (add_module_var_locations tops FEMPTY)) (NONE,id) =
    FLOOKUP (add_module_var_locations tops FEMPTY) (NONE,id)
Proof
  rpt strip_tac >> irule add_immutable_locations_lookup_unchanged >>
  rpt strip_tac >> gvs[] >>
  drule_then (qspecl_then [`VariableDecl vis Immutable id ty slot`, `top`,
    `(NONE,id)`] mp_tac) toplevel_vtype_key_unique >>
  simp[toplevel_vtype_keys_toplevel_def] >> metis_tac[]
QED

(* The function compile env of a storage or transient variable of any
   visibility (build_compile_env's ce_module_vars, ce_module_var_type and
   ce_hashmap_info). *)
Theorem build_compile_env_storage_binding:
  !tops src id vis mut ty slot fvis fmut fname args ret body ut.
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    supported_variable_decl tops (src,id) = SOME (vis,mut,ty,SOME slot) /\
    (mut = Storage \/ mut = Transient) ==>
    src = NONE /\
    FLOOKUP (build_compile_env tops fvis fmut fname args ret body
               ut).ce_module_vars (NONE,id) =
      SOME (if mut = Transient then TransientLoc (n2w slot)
            else StorageLoc (n2w slot)) /\
    (build_compile_env tops fvis fmut fname args ret body
       ut).ce_module_var_type (NONE,id) = SOME ty /\
    (build_compile_env tops fvis fmut fname args ret body
       ut).ce_hashmap_info (NONE,id) = NONE
Proof
  rpt gen_tac >> strip_tac >>
  drule supported_variable_decl_storage_binding >> disch_then drule >>
  (impl_tac >- fs[]) >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  simp[build_compile_env_def] >>
  rpt (pairarg_tac >> simp[]) >>
  `FLOOKUP (add_immutable_locations
             (get_struct_fields (make_struct_fields_map tops)) tops 0
             (add_module_var_locations tops FEMPTY)) (NONE,id) =
   FLOOKUP (add_module_var_locations tops FEMPTY) (NONE,id)` by
    (irule add_immutable_locations_keeps_declared >> simp[] >>
     first_assum (irule_at Any) >> simp[toplevel_vtype_keys_toplevel_def]) >>
  simp[]
QED

(* The same for a hashmap of any visibility. *)
Theorem build_compile_env_hashmap_binding:
  !tops src id vis tr kt vt slot fvis fmut fname args ret body ut.
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    supported_hashmap_decl tops (src,id) = SOME (vis,tr,kt,vt,SOME slot) ==>
    src = NONE /\
    FLOOKUP (build_compile_env tops fvis fmut fname args ret body
               ut).ce_module_vars (NONE,id) =
      SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot)) /\
    (build_compile_env tops fvis fmut fname args ret body
       ut).ce_hashmap_info (NONE,id) = SOME (tr,kt,vt)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all supported_hashmap_decl_storage_binding >> strip_tac >>
  drule supported_hashmap_decl_mem >> strip_tac >> gvs[] >>
  simp[build_compile_env_def] >>
  rpt (pairarg_tac >> simp[]) >>
  `FLOOKUP (add_immutable_locations
             (get_struct_fields (make_struct_fields_map tops)) tops 0
             (add_module_var_locations tops FEMPTY)) (NONE,id) =
   FLOOKUP (add_module_var_locations tops FEMPTY) (NONE,id)` by
    (irule add_immutable_locations_keeps_declared >> simp[] >>
     first_assum (irule_at Any) >> simp[toplevel_vtype_keys_toplevel_def]) >>
  simp[]
QED

(* ===== The S1 lemmas whose statements name Private ===== *)

(* bodyAppendStorageFacts' body_append_runtime_metadata, with
   supported_storage_dynamic_array replaced by a lookup of any
   visibility. *)
Theorem body_append_runtime_metadata_vis:
  body_inv tops ctx cenv cx /\
  supported_variable_decl tops (src,id) =
    SOME (vis, mut, ArrayT delem (Dynamic dn), SOME dslot) /\
  (mut = Storage \/ mut = Transient) /\ supported_full_word_type delem /\
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
      (INL (StoragePlace tr (n2w slot) tv),es)
Proof
  strip_tac >>
  `ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  drule supported_variable_decl_storage_binding >> disch_then drule >>
  (impl_tac >- fs[]) >> strip_tac >> gvs[] >>
  drule_all body_append_root_metadata >> strip_tac >>
  `find_var_decl_by_name id tops <> NONE` by simp[] >>
  drule_all append_typed_storage_target >> strip_tac >> gvs[] >>
  drule_all append_storage_target_eval >> strip_tac >>
  simp[]
QED

(* bodyAppendStorageFacts' body_append_target_bounds, likewise. *)
Theorem body_append_target_bounds_vis:
  body_inv tops ctx cenv cx /\
  supported_variable_decl tops (src,id) =
    SOME (vis, mut, ArrayT delem (Dynamic dn), SOME dslot) /\
  (mut = Storage \/ mut = Transient) /\ supported_full_word_type delem /\
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
      (INL (StoragePlace tr (n2w slot) tv),es)
Proof
  REWRITE_TAC [GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule append_typing_target >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  drule_all body_append_runtime_metadata_vis >> strip_tac >> gvs[] >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `assignable_type env.type_defs
     (ArrayT elem (Dynamic (cenv.ce_module_dynarray_capacity (src,id))))` by
    simp[assignable_type_def, well_formed_type_def] >>
  drule_all append_capacity_word_bound >> strip_tac >>
  metis_tac[]
QED

(* bodySimStmtCases' body_assign_copy_target, with the Private lookup
   replaced by a lookup of any visibility. *)
Theorem body_assign_copy_target_vis:
  !tops ctx cenv cx src id vis mut ty ast_slot env es ret_ty e env'.
    body_inv tops ctx cenv cx /\
    supported_variable_decl tops (src,id) = SOME (vis,mut,ty,SOME ast_slot) /\
    (mut = Storage \/ mut = Transient) /\ expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) =
      SOME env' ==>
    src = NONE /\ get_module_code cx NONE = SOME tops /\
    cenv.ce_hashmap_info (NONE,id) = NONE /\
    cenv.ce_module_var_type (NONE,id) = SOME ty /\
    ?tr id_str off tvt.
      find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,id_str) /\
      lookup_var_slot_from_layout cx tr NONE id_str = SOME off /\
      evaluate_type (get_tenv cx) ty = SOME tvt
Proof
  rpt gen_tac >> strip_tac >> (
  `ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   get_module_code cx NONE = SOME tops /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by
    fs[body_inv_def] >>
  drule supported_variable_decl_storage_binding >> disch_then drule >>
  (impl_tac >- fs[]) >> strip_tac >> gvs[] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  Cases_on `type_place_target env (TopLevelNameTarget (NONE,id))` >>
  gvs[type_stmt_def, atarget_accepts_def] >>
  rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (gvs[env_consistent_def, env_context_consistent_def] >>
      first_x_assum drule >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> gvs[] >>
  gvs[optionTheory.IS_SOME_EXISTS])
QED

(* ===== FlagDecl and ErrorDecl entries ===== *)

(* Each builder over tops skips a FlagDecl or ErrorDecl entry, wherever it
   is.  The ones that carry an accumulator hold for every accumulator. *)

Theorem add_module_var_locations_inert_decl:
  !pre suf d vars.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    add_module_var_locations (pre ++ d :: suf) vars =
    add_module_var_locations (pre ++ suf) vars
Proof
  Induct >> rw[add_module_var_locations_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem add_immutable_locations_inert_decl:
  !pre suf d off vars.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    add_immutable_locations sft (pre ++ d :: suf) off vars =
    add_immutable_locations sft (pre ++ suf) off vars
Proof
  Induct >> rw[add_immutable_locations_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem compute_immutables_len_inert_decl:
  !pre suf d.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    compute_immutables_len sft (pre ++ d :: suf) =
    compute_immutables_len sft (pre ++ suf)
Proof
  Induct >> rw[compute_immutables_len_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem extract_layout_inert_decl:
  !pre suf d.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    extract_layout (pre ++ d :: suf) = extract_layout (pre ++ suf)
Proof
  Induct >- (rw[] >> simp[extract_layout_def]) >>
  rw[] >> (
  Cases_on `h`
  >~ [`VariableDecl _ dm _ _ ds`]
  >- (Cases_on `ds` >> Cases_on `dm` >> simp[extract_layout_def])
  >~ [`HashMapDecl _ _ _ _ _ ds`]
  >- (Cases_on `ds` >> simp[extract_layout_def]) >>
  simp[extract_layout_def])
QED

Theorem build_var_type_map_inert_decl:
  !pre suf d.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    build_var_type_map (pre ++ d :: suf) = build_var_type_map (pre ++ suf)
Proof
  Induct >> rw[build_var_type_map_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem build_hashmap_info_inert_decl:
  !pre suf d.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    build_hashmap_info (pre ++ d :: suf) = build_hashmap_info (pre ++ suf)
Proof
  Induct >> rw[build_hashmap_info_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem collect_module_vars_inert_decl:
  !pre suf d.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    collect_module_vars (pre ++ d :: suf) = collect_module_vars (pre ++ suf)
Proof
  Induct >> rw[collect_module_vars_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem build_struct_fields_map_inert_decl:
  !pre suf d sft.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    build_struct_fields_map tenv (pre ++ d :: suf) sft =
    build_struct_fields_map tenv (pre ++ suf) sft
Proof
  Induct >> rw[build_struct_fields_map_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem build_event_info_inert_decl:
  !pre suf d eim.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    build_event_info tenv (pre ++ d :: suf) eim =
    build_event_info tenv (pre ++ suf) eim
Proof
  Induct >> rw[build_event_info_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem build_func_info_inert_decl:
  !pre suf d.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    build_func_info sft (pre ++ d :: suf) = build_func_info sft (pre ++ suf)
Proof
  Induct >> rw[build_func_info_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem build_func_param_types_inert_decl:
  !pre suf d.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    build_func_param_types (pre ++ d :: suf) =
    build_func_param_types (pre ++ suf)
Proof
  Induct >> rw[build_func_param_types_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem build_func_return_type_inert_decl:
  !pre suf d.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    build_func_return_type (pre ++ d :: suf) =
    build_func_return_type (pre ++ suf)
Proof
  Induct >> rw[build_func_return_type_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem build_func_ids_inert_decl:
  !pre suf d n.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    build_func_ids n (pre ++ d :: suf) = build_func_ids n (pre ++ suf)
Proof
  Induct >> rw[build_func_ids_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem build_func_mutability_inert_decl:
  !pre suf d.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    build_func_mutability (pre ++ d :: suf) = build_func_mutability (pre ++ suf)
Proof
  Induct >> rw[build_func_mutability_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem module_consts_env_inert_decl[local]:
  !pre suf acc d.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    module_consts_env (pre ++ d :: suf) acc =
    module_consts_env (pre ++ suf) acc
Proof
  Induct >- (rw[] >> simp[module_consts_env_def]) >>
  rw[] >> Cases_on `h` >> gvs[module_consts_env_def] >>
  rename1 `VariableDecl vis mode name ty slot` >>
  Cases_on `mode` >> gvs[module_consts_env_def] >>
  first_x_assum irule >> simp[]
QED

Theorem public_getters_inert_decl[local]:
  !pre suf d.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    public_getters (pre ++ d :: suf) = public_getters (pre ++ suf)
Proof
  Induct >> rw[] >> gvs[public_getters_def, public_getter_def]
QED

Theorem classify_functions_inert_decl:
  !pre suf d.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    classify_functions (pre ++ d :: suf) = classify_functions (pre ++ suf)
Proof
  rw[] >>
  simp[classify_functions_def, rich_listTheory.FOLDR_APPEND,
       classify_function_def, module_consts_env_inert_decl,
       public_getters_inert_decl]
QED

Theorem find_var_decl_by_name_inert_decl:
  !pre suf d name.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    find_var_decl_by_name name (pre ++ d :: suf) =
    find_var_decl_by_name name (pre ++ suf)
Proof
  Induct >- (rw[] >> simp[find_var_decl_by_name_def]) >>
  rw[] >> (Cases_on `h` >> simp[find_var_decl_by_name_def])
QED

Theorem lookup_function_inert_decl:
  !pre suf d src name vis.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    lookup_function src name vis (pre ++ d :: suf) =
    lookup_function src name vis (pre ++ suf)
Proof
  Induct >- (rw[] >> Cases_on `vis` >> simp[lookup_function_def]) >>
  rw[] >> (
  Cases_on `h`
  >~ [`VariableDecl dv _ _ _ _`]
  >- (Cases_on `dv` >> Cases_on `vis` >> simp[lookup_function_def])
  >~ [`HashMapDecl dv _ _ _ _ _`]
  >- (Cases_on `dv` >> Cases_on `vis` >> simp[lookup_function_def]) >>
  Cases_on `vis` >> simp[lookup_function_def])
QED

Theorem lookup_raw_return_inert_decl:
  !pre suf d src name vis.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    lookup_raw_return src name vis (pre ++ d :: suf) =
    lookup_raw_return src name vis (pre ++ suf)
Proof
  Induct >- (rw[] >> simp[lookup_raw_return_def]) >>
  rw[] >> (Cases_on `h` >> simp[lookup_raw_return_def])
QED

Theorem lookup_callable_function_inert_decl:
  !pre suf d in_deploy name.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    lookup_callable_function in_deploy name (pre ++ d :: suf) =
    lookup_callable_function in_deploy name (pre ++ suf)
Proof
  rw[] >> simp[lookup_callable_function_def, lookup_function_inert_decl]
QED

Theorem is_bare_global_decl_inert_decl:
  !pre suf d id.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    is_bare_global_decl id (pre ++ d :: suf) =
    is_bare_global_decl id (pre ++ suf)
Proof
  Induct >- (rw[] >> simp[is_bare_global_decl_def]) >>
  rw[] >> (
  Cases_on `h`
  >~ [`VariableDecl _ dm _ _ _`]
  >- (Cases_on `dm` >> simp[is_bare_global_decl_def]) >>
  simp[is_bare_global_decl_def])
QED

Theorem supported_decl_other_module[local]:
  !ts m n.
    m <> NONE ==>
    supported_variable_decl ts (m,n) = NONE /\
    supported_hashmap_decl ts (m,n) = NONE
Proof
  Cases >> simp[supported_variable_decl_def, supported_hashmap_decl_def]
QED

Theorem supported_variable_decl_inert_decl:
  !pre suf d nid.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    supported_variable_decl (pre ++ d :: suf) nid =
    supported_variable_decl (pre ++ suf) nid
Proof
  Induct >> rpt gen_tac >> PairCases_on `nid` >>
  rw[supported_variable_decl_def] >> BasicProvers.every_case_tac >>
  gvs[supported_decl_other_module]
QED

Theorem supported_hashmap_decl_inert_decl:
  !pre suf d nid.
    (d = FlagDecl fid ms \/ d = ErrorDecl eid ps) ==>
    supported_hashmap_decl (pre ++ d :: suf) nid =
    supported_hashmap_decl (pre ++ suf) nid
Proof
  Induct >> rpt gen_tac >> PairCases_on `nid` >>
  rw[supported_hashmap_decl_def] >> BasicProvers.every_case_tac >>
  gvs[supported_decl_other_module]
QED

(* An ErrorDecl is not a type, and declares no flag. *)
Theorem type_env_for_module_error_decl:
  !pre suf src.
    type_env_for_module src (pre ++ ErrorDecl eid ps :: suf) =
    type_env_for_module src (pre ++ suf)
Proof
  Induct >> simp[type_env_for_module_def] >>
  Cases >> simp[type_env_for_module_def]
QED

Theorem build_flag_info_error_decl:
  !pre suf fmid fnm.
    build_flag_info (pre ++ ErrorDecl eid ps :: suf) fmid fnm =
    build_flag_info (pre ++ suf) fmid fnm
Proof
  Induct >> rw[build_flag_info_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* The compile env of any function ignores an ErrorDecl entry. *)
Theorem build_compile_env_error_decl:
  !pre suf fvis fmut fname args ret body ut.
    (build_compile_env (pre ++ ErrorDecl eid ps :: suf)
      fvis fmut fname args ret body ut with ce_modules := [(NONE,pre ++ suf)]) =
    build_compile_env (pre ++ suf) fvis fmut fname args ret body ut
Proof
  rpt gen_tac >>
  `!sft tenv.
     make_struct_fields_map (pre ++ ErrorDecl eid ps :: suf) =
       make_struct_fields_map (pre ++ suf) /\
     type_env (pre ++ ErrorDecl eid ps :: suf) = type_env (pre ++ suf)` by
    simp[make_struct_fields_map_def, type_env_def,
         type_env_for_module_error_decl, build_struct_fields_map_inert_decl] >>
  simp[build_compile_env_def, build_flag_info_error_decl,
       extract_layout_inert_decl, build_var_type_map_inert_decl,
       build_hashmap_info_inert_decl, build_event_info_inert_decl,
       add_immutable_locations_inert_decl, add_module_var_locations_inert_decl,
       collect_module_vars_inert_decl, build_func_info_inert_decl,
       build_func_param_types_inert_decl, build_func_return_type_inert_decl,
       build_func_ids_inert_decl, build_func_mutability_inert_decl] >>
  rpt (pairarg_tac >> simp[])
QED

(* A FlagDecl entry: the compile env's module-variable bindings and
   function tables are those of the program without it, except that the
   struct field sizes (and the immutable offsets and function info sized
   by them) are taken in the type environment that has the flag. *)
Theorem build_compile_env_flag_decl:
  !pre suf fvis fmut fname args ret body ut.
    (build_compile_env (pre ++ FlagDecl fid ms :: suf)
       fvis fmut fname args ret body ut).ce_module_vars =
      add_immutable_locations
        (get_struct_fields
           (make_struct_fields_map (pre ++ FlagDecl fid ms :: suf)))
        (pre ++ suf) 0 (add_module_var_locations (pre ++ suf) FEMPTY) /\
    (build_compile_env (pre ++ FlagDecl fid ms :: suf)
       fvis fmut fname args ret body ut).ce_storage_layout =
      extract_layout (pre ++ suf) /\
    (build_compile_env (pre ++ FlagDecl fid ms :: suf)
       fvis fmut fname args ret body ut).ce_module_var_type =
      build_var_type_map (pre ++ suf) /\
    (build_compile_env (pre ++ FlagDecl fid ms :: suf)
       fvis fmut fname args ret body ut).ce_hashmap_info =
      build_hashmap_info (pre ++ suf) /\
    (build_compile_env (pre ++ FlagDecl fid ms :: suf)
       fvis fmut fname args ret body ut).ce_module_dynarray_capacity =
      build_dynarray_capacity (collect_module_vars (pre ++ suf)) /\
    (build_compile_env (pre ++ FlagDecl fid ms :: suf)
       fvis fmut fname args ret body ut).ce_func_info =
      build_func_info
        (get_struct_fields
           (make_struct_fields_map (pre ++ FlagDecl fid ms :: suf)))
        (pre ++ suf) /\
    (build_compile_env (pre ++ FlagDecl fid ms :: suf)
       fvis fmut fname args ret body ut).ce_func_param_types =
      build_func_param_types (pre ++ suf) /\
    (build_compile_env (pre ++ FlagDecl fid ms :: suf)
       fvis fmut fname args ret body ut).ce_func_return_type =
      build_func_return_type (pre ++ suf) /\
    (build_compile_env (pre ++ FlagDecl fid ms :: suf)
       fvis fmut fname args ret body ut).ce_func_ids =
      build_func_ids 0 (pre ++ suf)
Proof
  rpt gen_tac >> simp[build_compile_env_def] >>
  rpt (pairarg_tac >> simp[]) >>
  simp[extract_layout_inert_decl, build_var_type_map_inert_decl,
       build_hashmap_info_inert_decl, add_immutable_locations_inert_decl,
       add_module_var_locations_inert_decl, collect_module_vars_inert_decl,
       build_func_info_inert_decl, build_func_param_types_inert_decl,
       build_func_return_type_inert_decl, build_func_ids_inert_decl, build_func_mutability_inert_decl]
QED
