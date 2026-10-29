Theory placeTypingBuildProps
Ancestors
  placeTypingProps vyperTypeContract vyperTypeContractStaticMaps
  compileVyper compileEnv list finite_map

(* A single-module checker does not reject dots in declaration identifiers.
   A fabricated imported namespace can therefore alias a main-module key. *)
Theorem map_namespace_collision_probe:
  let tops = [HashMapDecl Private F "0.m" (BaseT (UintT 256))
                (Type (BaseT (UintT 256))) (SOME 0)] in
  let mods = [(NONE,tops)] in
  let layouts = [(0w, ([( (NONE,"0.m"), 0)], []))] in
  IS_SOME (check_contract F layouts 0w mods) /\
  OPTION_MAP (\(tr,kt,vt). (kt,vt))
    (build_hashmap_info tops (module_var_key (SOME 0,"m"))) =
      SOME (BaseT (UintT 256), Type (BaseT (UintT 256))) /\
  FLOOKUP (build_contract_type_artifact F mods).cta_toplevel_vtypes
    (SOME 0,"m") = NONE
Proof
  EVAL_TAC
QED

Theorem add_toplevel_vtypes_deploy:
  (add_toplevel_static_maps d src tl art).cta_toplevel_vtypes =
  (add_toplevel_static_maps F src tl art).cta_toplevel_vtypes
Proof
  Cases_on `tl` >> simp[add_toplevel_static_maps_def] >>
  TRY (Cases_on `v0` >> simp[add_toplevel_static_maps_def]) >>
  rw[]
QED

Theorem add_module_vtypes_cong:
  !tls a b.
  a.cta_toplevel_vtypes = b.cta_toplevel_vtypes ==>
  (add_module_static_maps d src tls a).cta_toplevel_vtypes =
  (add_module_static_maps F src tls b).cta_toplevel_vtypes
Proof
  Induct >> simp[add_module_static_maps_def] >> rpt strip_tac >>
  simp[GSYM add_module_static_maps_def] >>
  first_x_assum irule >>
  once_rewrite_tac[add_toplevel_vtypes_deploy] >>
  Cases_on `h` >> simp[add_toplevel_static_maps_def] >>
  TRY (Cases_on `v0` >> simp[add_toplevel_static_maps_def]) >>
  rw[]
QED

Theorem single_module_vtypes_deploy:
  (build_contract_type_artifact d [(NONE,tops)]).cta_toplevel_vtypes =
  (build_contract_type_artifact F [(NONE,tops)]).cta_toplevel_vtypes
Proof
  simp[build_contract_type_artifact_def] >>
  irule add_module_vtypes_cong >> simp[]
QED

Theorem module_var_key_NONE_inj[simp]:
  (module_var_key (NONE,a) = module_var_key (NONE,b)) <=> (a = b)
Proof
  simp[module_var_key_def, nsid_to_string_def]
QED

Theorem build_hashmap_info_absent_key:
  !tops id.
  ~MEM (NONE,id) (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) ==>
  build_hashmap_info tops (module_var_key (NONE,id)) = NONE
Proof
  Induct >> simp[build_hashmap_info_def] >>
  Cases_on `h` >> simp[build_hashmap_info_def,
    toplevel_vtype_keys_toplevel_def]
QED

Theorem build_hashmap_info_variable:
  !tops.
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
  MEM (VariableDecl vis mut id ty init) tops ==>
  build_hashmap_info tops (module_var_key (NONE,id)) = NONE
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `h` >>
  gvs[build_hashmap_info_def, toplevel_vtype_keys_toplevel_def,
      ALL_DISTINCT_APPEND] >>
  metis_tac[build_hashmap_info_absent_key,
            module_toplevel_vtype_key_MEM_Variable]
QED

Theorem build_hashmap_info_hashmap:
  !tops.
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
  MEM (HashMapDecl vis tr id kt vt slot) tops ==>
  build_hashmap_info tops (module_var_key (NONE,id)) = SOME (tr,kt,vt)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `h` >>
  gvs[build_hashmap_info_def, toplevel_vtype_keys_toplevel_def,
      ALL_DISTINCT_APPEND] >>
  metis_tac[module_toplevel_vtype_key_MEM]
QED

Theorem single_module_vtypes_sound:
  FLOOKUP (build_contract_type_artifact d [(NONE,tops)]).cta_toplevel_vtypes
    nsid = SOME vt ==>
  (?vis mut id ty init.
     nsid = (NONE,id) /\ MEM (VariableDecl vis mut id ty init) tops /\
     vt = Type ty) \/
  (?vis tr id kt vty slot.
     nsid = (NONE,id) /\ MEM (HashMapDecl vis tr id kt vty slot) tops /\
     vt = HashMapT kt vty)
Proof
  once_rewrite_tac[single_module_vtypes_deploy] >>
  rewrite_tac[build_contract_type_artifact_def] >>
  simp[] >> strip_tac >>
  drule add_module_static_maps_toplevel_vtypes_sound >>
  simp[empty_contract_type_artifact_def] >> metis_tac[]
QED

Theorem single_module_defined_map_agreement:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
  env.toplevel_vtypes =
    (build_contract_type_artifact d [(NONE,tops)]).cta_toplevel_vtypes /\
  cenv.ce_hashmap_info = build_hashmap_info tops ==>
  place_map_tables_agree_on_defined cenv env
Proof
  rw[place_map_tables_agree_on_defined_def] >>
  drule single_module_vtypes_sound >> strip_tac >> gvs[]
  >- (drule_all build_hashmap_info_variable >> simp[]) >>
  drule_all build_hashmap_info_hashmap >> simp[]
QED

Theorem checked_single_module_defined_map_agreement:
  check_contract d layouts addr [(NONE,tops)] = SOME art /\
  env.toplevel_vtypes = art.cta_toplevel_vtypes /\
  cenv.ce_hashmap_info = build_hashmap_info tops ==>
  place_map_tables_agree_on_defined cenv env
Proof
  rw[check_contract_def] >>
  irule single_module_defined_map_agreement >>
  gvs[contract_namespaces_ok_def, contract_keys_def] >> metis_tac[]
QED

Theorem build_compile_env_ce_hashmap_info:
  (build_compile_env tops vis mut fname args ret fbody use_trans).ce_hashmap_info =
  build_hashmap_info tops
Proof
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem build_compile_env_defined_map_agreement:
  check_contract d layouts addr [(NONE,tops)] = SOME art /\
  env.toplevel_vtypes = art.cta_toplevel_vtypes ==>
  place_map_tables_agree_on_defined
    (build_compile_env tops vis mut fname args ret fbody use_trans) env
Proof
  metis_tac[checked_single_module_defined_map_agreement,
            build_compile_env_ce_hashmap_info]
QED

Theorem build_compile_env_artifact_defined_map_agreement:
  check_contract d layouts addr [(NONE,tops)] = SOME art ==>
  place_map_tables_agree_on_defined
    (build_compile_env tops vis mut fname args ret fbody use_trans)
    (artifact_env art [(NONE,tops)] NONE)
Proof
  strip_tac >> irule build_compile_env_defined_map_agreement >>
  simp[artifact_env_def] >> metis_tac[]
QED

val _ = List.app (fn (name,th) =>
  if List.exists (fn s => s <> "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then raise Fail ("oracle dependency: " ^ name) else ())
  (DB.thms "placeTypingBuildProps");
