Theory linkedStructFields
Ancestors
  linkedNsidProps structFieldsProps compileUnit compileEnv vyperTypeContract
  vyperContext vyperAST finite_map list pair

Triviality linked_type_key_member:
  MEM (src,tops) mods /\ MEM (StructDecl name args) tops ==>
  MEM (src,name) (contract_keys type_def_keys_toplevel mods)
Proof
  simp[contract_keys_def, MEM_FLAT, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
  metis_tac[struct_decl_type_key_member]
QED

Triviality linked_struct_name_no_dot:
  contract_namespaces_ok dep mods /\ MEM (src,tops) mods /\
  MEM (StructDecl name args) tops ==>
  ~MEM #"." name
Proof
  simp[contract_namespaces_ok_def, EVERY_MEM, FORALL_PROD] >>
  metis_tac[]
QED

Triviality type_env_for_module_key_src:
  !tops src key v.
    FLOOKUP (type_env_for_module src tops) key = SOME v ==> FST key = src
Proof
  Induct >> simp[type_env_for_module_def] >>
  Cases >> rw[type_env_for_module_def, FLOOKUP_UPDATE] >> gvs[] >>
  metis_tac[]
QED

Triviality type_env_for_module_struct_lookup_src:
  !tops src name args.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel src) tops)) /\
    MEM (StructDecl name args) tops ==>
    FLOOKUP (type_env_for_module src tops) (src,name) = SOME (StructArgs args)
Proof
  Induct >> simp[] >> Cases >>
  simp[type_env_for_module_def, type_def_keys_toplevel_def, FLOOKUP_UPDATE,
       ALL_DISTINCT_APPEND] >>
  rw[] >> gvs[] >> metis_tac[struct_decl_type_key_member]
QED

Triviality linked_struct_type_origin:
  !mods src name args.
    FLOOKUP (type_env_all_modules mods) (src,name) = SOME (StructArgs args) ==>
    ?tops. MEM (src,tops) mods /\ MEM (StructDecl name args) tops
Proof
  Induct >> simp[type_env_all_modules_def] >>
  PairCases_on `h` >> simp[type_env_all_modules_def, FLOOKUP_FUNION] >>
  rpt gen_tac >> Cases_on `FLOOKUP (type_env_for_module h0 h1) (src,name)` >>
  simp[] >> metis_tac[type_env_for_module_struct_mem]
QED

Triviality linked_struct_type_lookup:
  !mods src tops name args.
    ALL_DISTINCT (MAP FST mods) /\
    ALL_DISTINCT (contract_keys type_def_keys_toplevel mods) /\
    MEM (src,tops) mods /\ MEM (StructDecl name args) tops ==>
    FLOOKUP (type_env_all_modules mods) (src,name) = SOME (StructArgs args)
Proof
  Induct >> simp[] >>
  PairCases_on `h` >>
  simp[type_env_all_modules_def, FLOOKUP_FUNION, contract_keys_def,
       ALL_DISTINCT_APPEND] >>
  rpt strip_tac >> gvs[]
  >- (drule_all type_env_for_module_struct_lookup_src >> simp[]) >>
  Cases_on `FLOOKUP (type_env_for_module h0 h1) (src,name)` >> simp[]
  >- metis_tac[contract_keys_def] >>
  imp_res_tac type_env_for_module_key_src >> gvs[MEM_MAP] >> metis_tac[]
QED

Triviality struct_fields_map_src_origin:
  !tops tenv src sf key fields.
    FLOOKUP (build_struct_fields_map_src tenv src tops sf) key = SOME fields ==>
    FLOOKUP sf key = SOME fields \/
    ?name args. MEM (StructDecl name args) tops /\
      key = nsid_to_string (src,name) /\
      fields = build_struct_fields_one tenv args
Proof
  Induct >> simp[build_struct_fields_map_src_def] >> Cases >>
  rw[build_struct_fields_map_src_def] >> res_tac >>
  gvs[FLOOKUP_UPDATE] >> metis_tac[]
QED

Triviality struct_fields_map_mods_origin:
  !mods tenv sf key fields.
    FLOOKUP (build_struct_fields_map_mods tenv mods sf) key = SOME fields ==>
    FLOOKUP sf key = SOME fields \/
    ?src tops name args. MEM (src,tops) mods /\ MEM (StructDecl name args) tops /\
      key = nsid_to_string (src,name) /\ fields = build_struct_fields_one tenv args
Proof
  Induct >> simp[build_struct_fields_map_mods_def] >> PairCases_on `h` >>
  rw[build_struct_fields_map_mods_def] >> res_tac >>
  metis_tac[struct_fields_map_src_origin]
QED

Triviality struct_fields_map_src_absent:
  !tops tenv src sf key.
    (!name args. MEM (StructDecl name args) tops ==>
       nsid_to_string (src,name) <> key) ==>
    FLOOKUP (build_struct_fields_map_src tenv src tops sf) key = FLOOKUP sf key
Proof
  Induct >> simp[build_struct_fields_map_src_def] >> Cases >>
  rw[build_struct_fields_map_src_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  first_x_assum (mp_tac o SPECL [``tenv : nsid |-> type_args``, ``src : num option``]) >>
  simp[FLOOKUP_UPDATE]
QED

Triviality struct_fields_map_mods_absent:
  !mods tenv sf key.
    (!src tops name args. MEM (src,tops) mods /\ MEM (StructDecl name args) tops ==>
       nsid_to_string (src,name) <> key) ==>
    FLOOKUP (build_struct_fields_map_mods tenv mods sf) key = FLOOKUP sf key
Proof
  Induct >> simp[build_struct_fields_map_mods_def] >> PairCases_on `h` >>
  rw[build_struct_fields_map_mods_def] >>
  first_x_assum (fn th => DEP_REWRITE_TAC [th]) >>
  simp[struct_fields_map_src_absent] >> metis_tac[]
QED

Triviality struct_fields_map_src_lookup:
  !tops tenv src sf name args.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel src) tops)) /\
    MEM (StructDecl name args) tops ==>
    FLOOKUP (build_struct_fields_map_src tenv src tops sf)
      (nsid_to_string (src,name)) = SOME (build_struct_fields_one tenv args)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `MEM (StructDecl name args) tops`
  >- (Cases_on `h` >> gvs[ALL_DISTINCT_APPEND, build_struct_fields_map_src_def] >>
      first_x_assum irule >> simp[]) >>
  `h = StructDecl name args` by fs[] >>
  gvs[type_def_keys_toplevel_def, build_struct_fields_map_src_def] >>
  DEP_REWRITE_TAC [struct_fields_map_src_absent] >> simp[FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `src` >>
  gvs[nsid_to_string_def, APPEND_11] >>
  metis_tac[struct_decl_type_key_member]
QED

Triviality struct_fields_map_mods_lookup:
  !mods tenv sf src tops name args.
    ALL_DISTINCT (MAP FST mods) /\
    ALL_DISTINCT (contract_keys type_def_keys_toplevel mods) /\
    (!s ts n a. MEM (s,ts) mods /\ MEM (StructDecl n a) ts ==> ~MEM #"." n) /\
    MEM (src,tops) mods /\ MEM (StructDecl name args) tops ==>
    FLOOKUP (build_struct_fields_map_mods tenv mods sf) (nsid_to_string (src,name)) =
      SOME (build_struct_fields_one tenv args)
Proof
  Induct >> simp[] >> PairCases_on `h` >>
  rw[build_struct_fields_map_mods_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
  gvs[]
  >- (DEP_REWRITE_TAC [struct_fields_map_mods_absent] >>
      simp[struct_fields_map_src_lookup] >>
      rpt strip_tac >>
      `(src',name') = (h0,name)` suffices_by
        (rw[] >> fs[MEM_MAP] >> metis_tac[]) >>
      irule nsid_to_string_dot_free_injective >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[contract_keys_def] >> metis_tac[]
QED

Theorem make_struct_fields_map_mods_consistent:
  contract_namespaces_ok dep mods ==>
  sfields_tenv_consistent (make_struct_fields_map_mods mods) (type_env_all_modules mods)
Proof
  strip_tac >>
  `!s ts n a. MEM (s,ts) mods /\ MEM (StructDecl n a) ts ==> ~MEM #"." n`
    by metis_tac[linked_struct_name_no_dot] >>
  fs[contract_namespaces_ok_def] >>
  rw[sfields_tenv_consistent_def, make_struct_fields_map_mods_def]
  >- (PairCases_on `nsid` >>
      drule_then strip_assume_tac linked_struct_type_origin >>
      qexists_tac `build_struct_fields_one (type_env_all_modules mods) args` >>
      simp[built_struct_fields_names, built_struct_fields_types] >>
      metis_tac[struct_fields_map_mods_lookup]) >>
  drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) struct_fields_map_mods_origin >>
  qexistsl [`(src,name')`, `args`] >>
  simp[built_struct_fields_names, built_struct_fields_types] >>
  metis_tac[linked_struct_type_lookup]
QED
