(* Compiler storage maps projected at a source-qualified variable key. *)
Theory linkedStorageMetadataProps
Ancestors
  bodyInvSplit bodyStorageMetadata moduleVariableKeyProps compileUnit compileVyper
  supportedDecls supportedStmts vyperTypeContract list pair alist

Theorem storage_metadata_other_source[local]:
  !tops src key id vmap hmap tail.
    src <> key ==>
    build_var_type_map_src src tops vmap (key,id) = vmap (key,id) /\
    build_hashmap_info_src src tops hmap (key,id) = hmap (key,id) /\
    build_dynarray_capacity (collect_module_vars_src src tops ++ tail) (key,id) =
      build_dynarray_capacity tail (key,id)
Proof
  Induct >> simp[build_var_type_map_src_def, build_hashmap_info_src_def,
                 collect_module_vars_src_def] >>
  Cases >> simp[build_var_type_map_src_def, build_hashmap_info_src_def,
                collect_module_vars_src_def, build_dynarray_capacity_def] >>
  rw[] >> Cases_on `dynarray_capacity_of_type t` >> simp[]
QED

Theorem storage_metadata_absent_source[local]:
  !mods src id.
    ALOOKUP mods src = NONE ==>
    build_hashmap_info_mods mods (src,id) = NONE /\
    build_dynarray_capacity (collect_module_vars_mods mods) (src,id) = 0
Proof
  Induct >> simp[build_hashmap_info_mods_def, collect_module_vars_mods_def,
                 build_dynarray_capacity_def] >>
  PairCases >> rw[build_hashmap_info_mods_def, collect_module_vars_mods_def] >>
  drule_then (fn th => simp[th]) storage_metadata_other_source
QED

Theorem storage_metadata_source_lookup[local]:
  !tops src id vm hm.
    build_var_type_map_src src tops vm (src,id) =
      (case build_var_type_map tops (NONE,id) of
         NONE => vm (src,id) | SOME ty => SOME ty) /\
    build_hashmap_info_src src tops hm (src,id) =
      (case build_hashmap_info tops (NONE,id) of
         NONE => hm (src,id) | SOME info => SOME info)
Proof
  Induct >> simp[build_var_type_map_src_def, build_var_type_map_def,
                 build_hashmap_info_src_def, build_hashmap_info_def] >>
  Cases >> simp[build_var_type_map_src_def, build_var_type_map_def,
                build_hashmap_info_src_def, build_hashmap_info_def] >>
  rw[]
QED

Theorem storage_capacity_source_lookup[local]:
  !tops src id vis mut elem n slot tail.
    supported_variable_decl tops (NONE,id) =
      SOME (vis,mut,ArrayT elem (Dynamic n),slot) ==>
    build_dynarray_capacity (collect_module_vars_src src tops ++ tail) (src,id) = n
Proof
  Induct >> simp[supported_variable_decl_def] >>
  Cases >>
  simp[supported_variable_decl_def, collect_module_vars_src_def,
       build_dynarray_capacity_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), dynarray_capacity_of_type_def] >>
  first_x_assum drule >> simp[] >>
  CASE_TAC >> simp[] >> metis_tac[]
QED

Theorem storage_metadata_unit_lookup[local]:
  !mods src tops id ty.
    ALL_DISTINCT (MAP FST mods) /\ ALOOKUP mods src = SOME tops /\
    build_var_type_map tops (NONE,id) = SOME ty /\
    build_hashmap_info tops (NONE,id) = NONE ==>
    build_var_type_map_mods mods (src,id) = SOME ty /\
    build_hashmap_info_mods mods (src,id) = NONE
Proof
  Induct >> simp[] >> PairCases >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h0 = src` >>
  gvs[build_var_type_map_mods_def, build_hashmap_info_mods_def]
  >- (simp[storage_metadata_source_lookup] >>
      irule (cj 1 storage_metadata_absent_source) >> simp[ALOOKUP_NONE]) >>
  drule_then (fn th => simp[th]) storage_metadata_other_source >>
  metis_tac[]
QED

Theorem storage_capacity_unit_lookup[local]:
  !mods src tops id vis mut elem n slot.
    ALOOKUP mods src = SOME tops /\
    supported_variable_decl tops (NONE,id) =
      SOME (vis,mut,ArrayT elem (Dynamic n),slot) ==>
    build_dynarray_capacity (collect_module_vars_mods mods) (src,id) = n
Proof
  Induct >> simp[] >> PairCases >>
  rw[collect_module_vars_mods_def] >>
  metis_tac[storage_capacity_source_lookup, storage_metadata_other_source]
QED

Theorem contract_inv_storage_metadata[local]:
  contract_inv mods exps ctx cenv cx ==>
  ALL_DISTINCT (MAP FST mods) /\
  (!src tops. ALOOKUP mods src = SOME tops ==>
     ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops))) /\
  cenv.ce_module_var_type = build_var_type_map_mods mods /\
  cenv.ce_hashmap_info = build_hashmap_info_mods mods /\
  cenv.ce_module_dynarray_capacity =
    build_dynarray_capacity (collect_module_vars_mods mods)
Proof
  simp[contract_inv_def, cenv_module_pins_mods_def] >> metis_tac[]
QED

Theorem contract_inv_variable_metadata:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
  MEM (VariableDecl vis mut id ty slot) tops ==>
  cenv.ce_module_var_type (src,id) = SOME ty /\ cenv.ce_hashmap_info (src,id) = NONE
Proof
  REWRITE_TAC [GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_then strip_assume_tac contract_inv_storage_metadata >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[contract_inv_unqualified_variable_keys] >>
  drule_all_then strip_assume_tac build_maps_variable >>
  drule_all_then strip_assume_tac storage_metadata_unit_lookup >> simp[]
QED

Theorem body_append_capacity_lookup_mods:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
  supported_variable_decl tops (NONE,id) =
    SOME (vis,mut,ArrayT elem (Dynamic n),slot) ==>
  cenv.ce_module_dynarray_capacity (src,id) = n
Proof
  REWRITE_TAC [GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_then strip_assume_tac contract_inv_storage_metadata >>
  metis_tac[storage_capacity_unit_lookup]
QED

Theorem supported_scalar_target_decl:
  src = NONE /\ supported_scalar_target tops (src,id) ==>
  src = NONE /\
  ?vis mut ty slot.
    MEM (VariableDecl vis mut id ty (SOME slot)) tops /\
    (mut = Storage \/ mut = Transient)
Proof
  Cases_on `src` >> simp[supported_scalar_target_def] >>
  Cases_on `supported_variable_decl tops (NONE,id)` >> simp[] >>
  PairCases_on `x` >> Cases_on `x1` >> Cases_on `x3` >>
  simp[] >> metis_tac[supported_variable_decl_mem]
QED

Theorem body_inv_storage_var_types_mods:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr typ,id_str) ==>
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME typ
Proof
  strip_tac >> drule_then strip_assume_tac find_var_decl_storage_mem >>
  metis_tac[contract_inv_variable_metadata]
QED
