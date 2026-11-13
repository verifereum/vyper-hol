(* Shared module declaration and compiler-map metadata. *)
Theory bodyStorageMetadata
Ancestors
  compileVyper supportedDecls vyperState vyperTypeContract
  vyperTypeContractStaticMaps list

Theorem find_var_decl_storage_mem:
  !ts id tr typ id_str.
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) ==>
    id_str = id /\ ?vis mut init. MEM (VariableDecl vis mut id typ init) ts
Proof
  Induct >> simp[find_var_decl_by_name_def] >> Cases >>
  rw[find_var_decl_by_name_def] >> metis_tac[]
QED

Theorem supported_variable_decl_mem:
  !tops src id vis mut ty slot.
    supported_variable_decl tops (src, id) = SOME (vis, mut, ty, slot) ==>
    src = NONE /\ MEM (VariableDecl vis mut id ty slot) tops
Proof
  Induct >> simp[supported_variable_decl_def] >> Cases >>
  rw[supported_variable_decl_def] >> metis_tac[]
QED

Theorem find_var_decl_absent[local]:
  !tops id.
    ~MEM (NONE, id)
       (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) ==>
    find_var_decl_by_name id tops = NONE
Proof
  Induct >> simp[find_var_decl_by_name_def] >> Cases >>
  simp[find_var_decl_by_name_def, toplevel_vtype_keys_toplevel_def]
QED

Theorem find_var_decl_immutable_NONE[local]:
  !tops vis id ty init.
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
    MEM (VariableDecl vis Immutable id ty init) tops ==>
    find_var_decl_by_name id tops = NONE
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac
  >- gvs[toplevel_vtype_keys_toplevel_def, find_var_decl_by_name_def,
         find_var_decl_absent] >>
  Cases_on `h` >>
  gvs[toplevel_vtype_keys_toplevel_def, find_var_decl_by_name_def,
      ALL_DISTINCT_APPEND] >>
  rw[] >> gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> res_tac >>
  gvs[toplevel_vtype_keys_toplevel_def] >>
  qpat_x_assum `!y. ~MEM y tops \/ _`
    (qspec_then `VariableDecl vis Immutable id ty init` mp_tac) >>
  simp[toplevel_vtype_keys_toplevel_def]
QED

(* A supported immutable is a main-module variable with no storage or
   hashmap declaration of its name. *)
Theorem supported_immutable_type_find_NONE:
  !tops src id ty.
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
    supported_immutable_type tops (src,id) = SOME ty ==>
    src = NONE /\ find_var_decl_by_name id tops = NONE
Proof
  rpt gen_tac >> simp[supported_immutable_type_def, AllCaseEqs()] >>
  strip_tac >> drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  metis_tac[find_var_decl_immutable_NONE]
QED

Theorem build_hashmap_info_absent[local]:
  !tops id.
    ~MEM (NONE, id)
       (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) ==>
    build_hashmap_info tops (NONE, id) = NONE
Proof
  Induct >> simp[build_hashmap_info_def] >> Cases >>
  simp[build_hashmap_info_def, toplevel_vtype_keys_toplevel_def]
QED

Theorem build_maps_variable:
  !tops vis mut id ty init.
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
    MEM (VariableDecl vis mut id ty init) tops ==>
    build_hashmap_info tops (NONE, id) = NONE /\
    build_var_type_map tops (NONE, id) = SOME ty
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> Cases_on `h` >>
  gvs[build_hashmap_info_def, build_var_type_map_def,
      toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  metis_tac[build_hashmap_info_absent, module_toplevel_vtype_key_MEM_Variable]
QED
