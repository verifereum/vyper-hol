Theory linkedStructFields
Ancestors
  linkedNsidProps structFieldsProps compileUnit compileEnv vyperTypeContract
  vyperContext vyperAST loweringStateRelDefs typedCopyMetadata finite_map list pair

Triviality linked_struct_name_no_dot:
  contract_namespaces_ok dep mods /\ MEM (src,tops) mods /\
  MEM (StructDecl name args) tops ==>
  ~MEM #"." name
Proof
  simp[contract_namespaces_ok_def] >> strip_tac >>
  qpat_x_assum `EVERY (\(s,ts). EVERY _ ts) mods` mp_tac >>
  simp[Once EVERY_MEM] >>
  disch_then (qspec_then `(src,tops)` mp_tac) >> simp[] >>
  simp[Once EVERY_MEM] >>
  disch_then (qspec_then `StructDecl name args` mp_tac) >> simp[]
QED

Triviality type_env_for_module_key_src:
  !tops src key v.
    FLOOKUP (type_env_for_module src tops) key = SOME v ==> FST key = src
Proof
  Induct >> simp[type_env_for_module_def] >>
  Cases >> rw[type_env_for_module_def, FLOOKUP_UPDATE] >> gvs[] >>
  metis_tac[]
QED

Triviality linked_struct_type_origin:
  !mods src name args.
    FLOOKUP (type_env_all_modules mods) (src,name) = SOME (StructArgs args) ==>
    ?tops. MEM (src,tops) mods /\ MEM (StructDecl name args) tops
Proof
  Induct >> simp[type_env_all_modules_def] >>
  gen_tac >> PairCases_on `h` >> simp[type_env_all_modules_def, FLOOKUP_FUNION] >>
  rpt gen_tac >> Cases_on `FLOOKUP (type_env_for_module h0 h1) (src,name)` >>
  simp[] >> strip_tac
  >- (first_x_assum drule >> disch_then (qx_choose_then `tops` strip_assume_tac) >>
      qexists_tac `tops` >> simp[]) >>
  gvs[] >> drule type_env_for_module_struct_mem >> simp[] >> strip_tac >>
  qexists_tac `h1` >> gvs[]
QED

Triviality linked_struct_type_lookup:
  !mods src tops name args.
    ALL_DISTINCT (MAP FST mods) /\
    ALL_DISTINCT (contract_keys type_def_keys_toplevel mods) /\
    MEM (src,tops) mods /\ MEM (StructDecl name args) tops ==>
    FLOOKUP (type_env_all_modules mods) (src,name) = SOME (StructArgs args)
Proof
  Induct >> simp[] >>
  gen_tac >> PairCases_on `h` >>
  simp[type_env_all_modules_def, FLOOKUP_FUNION, contract_keys_def,
       ALL_DISTINCT_APPEND] >>
  rpt strip_tac >> gvs[]
  >- (drule_all type_env_for_module_struct_lookup >> simp[]) >>
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
  rw[build_struct_fields_map_src_def] >> first_x_assum drule >> strip_tac >>
  gvs[FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]
QED

Triviality struct_fields_map_mods_origin:
  !mods tenv sf key fields.
    FLOOKUP (build_struct_fields_map_mods tenv mods sf) key = SOME fields ==>
    FLOOKUP sf key = SOME fields \/
    ?src tops name args. MEM (src,tops) mods /\ MEM (StructDecl name args) tops /\
      key = nsid_to_string (src,name) /\ fields = build_struct_fields_one tenv args
Proof
  Induct >> simp[build_struct_fields_map_mods_def] >> gen_tac >> PairCases_on `h` >>
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
  first_x_assum drule >>
  disch_then (fn th => simp[th, FLOOKUP_UPDATE])
QED

Triviality struct_fields_map_mods_absent:
  !mods tenv sf key.
    (!src tops name args. MEM (src,tops) mods /\ MEM (StructDecl name args) tops ==>
       nsid_to_string (src,name) <> key) ==>
    FLOOKUP (build_struct_fields_map_mods tenv mods sf) key = FLOOKUP sf key
Proof
  Induct >> simp[build_struct_fields_map_mods_def] >> gen_tac >> PairCases_on `h` >>
  rw[build_struct_fields_map_mods_def] >>
  `!src tops name args. MEM (src,tops) mods /\ MEM (StructDecl name args) tops ==>
       nsid_to_string (src,name) <> key` by metis_tac[] >>
  first_x_assum drule >> disch_then (fn th => simp[th]) >>
  irule struct_fields_map_src_absent >> metis_tac[]
QED

Triviality struct_fields_map_src_lookup:
  !tops tenv src sf name args.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel src) tops)) /\
    MEM (StructDecl name args) tops ==>
    FLOOKUP (build_struct_fields_map_src tenv src tops sf)
      (nsid_to_string (src,name)) = SOME (build_struct_fields_one tenv args)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  reverse (disch_then (DISJ_CASES_THEN assume_tac))
  >- (Cases_on `h` >>
      gvs[ALL_DISTINCT_APPEND, type_def_keys_toplevel_def, build_struct_fields_map_src_def] >>
      first_x_assum irule >> simp[]) >>
  gvs[type_def_keys_toplevel_def, build_struct_fields_map_src_def] >>
  `!n a. MEM (StructDecl n a) tops ==>
      nsid_to_string (src,n) <> nsid_to_string (src,name)` by
    (rpt strip_tac >>
     `n = name` by (Cases_on `src` >> fs[nsid_to_string_def, APPEND_11]) >>
     gvs[] >> metis_tac[typedCopyProducerTheory.struct_decl_type_key_member]) >>
  drule struct_fields_map_src_absent >> simp[FLOOKUP_UPDATE]
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
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  rw[build_struct_fields_map_mods_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
  gvs[]
  >- (`!s ts n a. MEM (s,ts) mods /\ MEM (StructDecl n a) ts ==>
          nsid_to_string (s,n) <> nsid_to_string (h0,name)` by
        (rpt strip_tac >>
         `(s,n) = (h0,name)` by
           (irule nsid_to_string_dot_free_injective >> simp[] >> metis_tac[]) >>
         gvs[MEM_MAP] >> metis_tac[]) >>
      drule struct_fields_map_mods_absent >> simp[struct_fields_map_src_lookup]) >>
  first_x_assum irule >> simp[contract_keys_def] >> metis_tac[]
QED

Theorem make_struct_fields_map_mods_consistent:
  contract_namespaces_ok dep mods ==>
  sfields_tenv_consistent (make_struct_fields_map_mods mods) (type_env_all_modules mods)
Proof
  strip_tac >>
  `!s ts n a. MEM (s,ts) mods /\ MEM (StructDecl n a) ts ==> ~MEM #"." n`
    by metis_tac[linked_struct_name_no_dot] >>
  `ALL_DISTINCT (MAP FST mods) /\
   ALL_DISTINCT (contract_keys type_def_keys_toplevel mods)`
    by fs[contract_namespaces_ok_def] >>
  qpat_x_assum `contract_namespaces_ok _ _` kall_tac >>
  simp[sfields_tenv_consistent_def, make_struct_fields_map_mods_def] >>
  conj_tac
  >- (rpt strip_tac >> PairCases_on `nsid` >>
      drule_then (qx_choose_then `tops` strip_assume_tac) linked_struct_type_origin >>
      qexists_tac `build_struct_fields_one (type_env_all_modules mods) args` >>
      simp[built_struct_fields_names, built_struct_fields_types] >>
      irule struct_fields_map_mods_lookup >> simp[] >> conj_tac
      >- first_assum ACCEPT_TAC >>
      qexists_tac `tops` >> simp[]) >>
  rpt strip_tac >> drule struct_fields_map_mods_origin >> simp[] >>
  disch_then (qx_choose_then `src` (qx_choose_then `tops`
    (qx_choose_then `sname` (qx_choose_then `args` strip_assume_tac)))) >>
  qexistsl [`(src,sname)`, `args`] >>
  gvs[built_struct_fields_names, built_struct_fields_types] >>
  irule linked_struct_type_lookup >> simp[] >> qexists_tac `tops` >> simp[]
QED
