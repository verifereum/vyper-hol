Theory whitelistLinkedBodyData
Ancestors
  whitelistLinkedBodyEnv vyperTypeContractStaticMaps vyperTypeContractContext
  vyperTypeEventLookup e2eDefs whitelistCheckerDecls whitelistCheckerExprs
  supportedNameRoot supportedGetterProps placeTypingBuildProps
  alist finite_map list rich_list pair vyperAST vyperTypeContract vyperTypeSystem
  supportedTypes supportedDecls supportedExprForms compileVyper
  whitelistLinkedExprFormProps whitelistAllocatedHeaderProps whitelistCheckedBareGlobalProps

Triviality checked_vtype_declaration:
  check_contract mode layouts addr mods = SOME art /\
  FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME vt ==>
  (?ts vis mut ty slot. ALOOKUP mods src = SOME ts /\
     MEM (VariableDecl vis mut id ty slot) ts /\ vt = Type ty) \/
  (?ts vis tr kt v slot. ALOOKUP mods src = SOME ts /\
     MEM (HashMapDecl vis tr id kt v slot) ts /\ vt = HashMapT kt v)
Proof
  strip_tac >> drule check_contract_runtime_namespaces >> strip_tac >>
  drule check_contract_nonsig_maps >> strip_tac >>
  gvs[FLOOKUP_DRESTRICT_SOME] >>
  drule_all build_contract_type_artifact_toplevel_vtypes_sound >> simp[]
QED

Triviality checked_vtype_type:
  check_contract mode layouts addr mods = SOME art /\
  FLOOKUP art.cta_toplevel_vtypes k = SOME vt ==>
  check_value_type (type_env_all_modules mods) vt
Proof
  PairCases_on `k` >> strip_tac >> drule_all checked_vtype_declaration >>
  strip_tac >> gvs[] >> drule_all check_contract_toplevel_decl_MEM_checked >>
  simp[check_value_type_def, check_toplevel_decl_def] >>
  Cases_on `mut` >> simp[]
QED

Triviality main_vtype_keys:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME tops ==>
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))
Proof
  strip_tac >> drule check_contract_runtime_namespaces >> strip_tac >>
  irule contract_namespaces_ok_module_toplevel_vtype_keys >>
  metis_tac[ALOOKUP_MEM]
QED

Triviality checked_main_slot:
  check_contract mode am.layouts tx.target mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\ layouts_agree tops am tx /\ MEM tl tops ==>
  case tl of
    VariableDecl _ Storage _ _ slot => IS_SOME slot
  | VariableDecl _ Transient _ _ slot => IS_SOME slot
  | HashMapDecl _ _ _ _ _ slot => IS_SOME slot
  | _ => T
Proof
  strip_tac >> irule layouts_agree_allocated_header >>
  qexistsl [`am`, `tops`, `tx`] >> simp[] >>
  drule_all check_contract_main_module_allocated >>
  simp[module_allocated_def, EVERY_MEM] >> metis_tac[]
QED

Triviality checked_main_variable:
  check_contract mode am.layouts tx.target mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\ layouts_agree tops am tx /\
  (!ty. assignable_type (type_env_all_modules mods) ty ==> supported_place_type tops ty) /\
  MEM (VariableDecl vis mut id ty slot) tops ==>
  supported_place_root tops (NONE,id) /\ build_hashmap_info tops (NONE,id) = NONE /\
  ((mut = Storage \/ mut = Transient) ==> supported_storage_value tops (NONE,id) ty) /\
  (mut = Immutable ==> supported_immutable_type tops (NONE,id) = SOME ty) /\
  (!e. mut = Constant e ==> supported_constant_type tops (NONE,id) = SOME ty)
Proof
  strip_tac >> drule_all main_vtype_keys >> strip_tac >>
  drule_all supported_variable_decl_distinct_mem >> strip_tac >>
  drule_all build_hashmap_info_variable >> strip_tac >>
  drule_all checked_main_slot >> strip_tac >>
  drule_all check_contract_toplevel_decl_MEM_checked >>
  Cases_on `mut` >> Cases_on `slot` >>
  gvs[check_toplevel_decl_def, supported_place_root_def, supported_storage_value_def,
      supported_value_type_def, supported_storage_type_def, GSYM supported_place_type_def,
      supported_immutable_type_def, supported_constant_type_def]
QED

Triviality checked_main_hashmap:
  check_contract mode am.layouts tx.target mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\ layouts_agree tops am tx /\
  (!ty. assignable_type (type_env_all_modules mods) ty ==> supported_place_type tops ty) /\
  MEM (HashMapDecl vis tr id kt vt slot) tops ==>
  supported_place_root tops (NONE,id) /\
  build_hashmap_info tops (NONE,id) = SOME (tr,kt,vt)
Proof
  strip_tac >> drule_all main_vtype_keys >> strip_tac >>
  drule_all getter_hashmap_member_lookup >> strip_tac >>
  drule_all getter_hashmap_excludes_variable >> strip_tac >>
  drule_all build_hashmap_info_hashmap >> strip_tac >>
  drule_all checked_main_slot >> strip_tac >>
  drule_all check_contract_toplevel_decl_MEM_checked >>
  Cases_on `slot` >> gvs[check_toplevel_decl_def, supported_place_root_def] >>
  metis_tac[checker_hashmap_key_supported, checked_value_type_supported_hashmap]
QED

Triviality checked_main_vtype:
  check_contract mode am.layouts tx.target mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\ layouts_agree tops am tx /\
  (!ty. assignable_type (type_env_all_modules mods) ty ==> supported_place_type tops ty) /\
  FLOOKUP art.cta_toplevel_vtypes (NONE,id) = SOME vt ==>
  supported_place_root tops (NONE,id) /\
  case vt of
    Type ty => build_hashmap_info tops (NONE,id) = NONE /\
      (supported_storage_value tops (NONE,id) ty \/
       supported_immutable_type tops (NONE,id) = SOME ty \/
       supported_constant_type tops (NONE,id) = SOME ty)
  | HashMapT kt v => ?tr. build_hashmap_info tops (NONE,id) = SOME (tr,kt,v)
Proof
  strip_tac >> drule_all checked_vtype_declaration >> strip_tac >> gvs[]
  >- (drule_all checked_main_variable >> Cases_on `mut` >> simp[]) >>
  drule_all checked_main_hashmap >> metis_tac[]
QED

Triviality checked_main_assignable:
  check_contract mode am.layouts tx.target mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\ layouts_agree tops am tx /\
  (!ty. assignable_type (type_env_all_modules mods) ty ==> supported_place_type tops ty) /\
  FLOOKUP art.cta_bare_global_assignable (NONE,id) = SOME ty ==>
  supported_place_root tops (NONE,id) /\ supported_immutable_type tops (NONE,id) = SOME ty
Proof
  strip_tac >> drule check_contract_artifact_fields >> strip_tac >> gvs[] >>
  drule_all build_contract_type_artifact_bare_global_assignable_sound >>
  strip_tac >> gvs[] >> drule_all checked_main_variable >> simp[]
QED

Triviality checked_main_storage_value:
  check_contract mode am.layouts tx.target mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\ layouts_agree tops am tx /\
  (!ty. assignable_type (type_env_all_modules mods) ty ==> supported_place_type tops ty) /\
  FLOOKUP art.cta_bare_globals (NONE,id) = NONE /\
  FLOOKUP art.cta_toplevel_vtypes (NONE,id) = SOME (Type ty) ==>
  supported_storage_value tops (NONE,id) ty
Proof
  strip_tac >> drule_all checked_vtype_declaration >> strip_tac >> gvs[] >>
  drule_all checked_main_variable >> strip_tac >>
  drule check_contract_runtime_namespaces >> strip_tac >>
  drule check_contract_nonsig_maps >> strip_tac >>
  Cases_on `mut` >> gvs[] >>
  `FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals (NONE,id) = SOME ty`
    by (irule build_contract_type_artifact_bare_globals_complete >> metis_tac[]) >>
  gvs[]
QED

Triviality checked_main_event:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\
  FLOOKUP art.cta_event_fields (NONE,id) = SOME fields ==>
  supported_event_fields tops (NONE,id) = SOME fields
Proof
  strip_tac >> drule check_contract_artifact_fields >> strip_tac >>
  `FLOOKUP (build_contract_type_artifact mode mods).cta_event_fields (NONE,id) = SOME fields`
    by (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >> rw[check_contract_def] >> gvs[]) >>
  drule_then strip_assume_tac build_contract_event_fields_sound >>
  `ALOOKUP mods NONE = SOME tls` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >> fs[contract_namespaces_ok_def]) >>
  gvs[] >> irule supported_event_fields_event_keys >> simp[] >>
  irule contract_keys_module_distinct >>
  qexists_tac `mods` >> gvs[contract_namespaces_ok_def]
QED

Theorem linked_checked_data_env:
  check_contract mode am.layouts tx.target mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  (src = NONE ==> layouts_agree tops am tx) /\
  (src = NONE ==> !ty. assignable_type (type_env_all_modules mods) ty ==>
                       supported_place_type tops ty) /\
  env.type_defs = type_env_all_modules mods /\
  env.toplevel_vtypes = art.cta_toplevel_vtypes /\
  env.bare_globals = art.cta_bare_globals /\
  env.event_fields = art.cta_event_fields /\
  (!k ty. FLOOKUP env.bare_global_assignable k = SOME ty ==>
           FLOOKUP art.cta_bare_global_assignable k = SOME ty) ==>
  linked_body_data_env tops src env
Proof
  strip_tac >> simp[linked_body_data_env_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- metis_tac[checked_bare_global_vtype]
  >- metis_tac[checked_vtype_type]
  >- (PairCases_on `k` >> gvs[] >> irule checked_main_vtype >> metis_tac[])
  >- (PairCases_on `k` >> gvs[] >> irule checked_main_assignable >> metis_tac[])
  >- (PairCases_on `k` >> gvs[] >> irule checked_main_storage_value >> metis_tac[]) >>
  PairCases_on `k` >> gvs[] >> drule_all checked_main_event >> simp[]
QED
