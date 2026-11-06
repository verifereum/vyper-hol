Theory gasShadowSourceMetadata
Ancestors
  gasShadow compileVyper vyperContext moduleLowering

Theorem gas_shadow_type_env_for_module[simp]:
  !tops src. type_env_for_module src (MAP gas_shadow_toplevel tops) =
    type_env_for_module src tops
Proof
  Induct >> simp[type_env_for_module_def] >>
  Cases_on `h` >> simp[gas_shadow_toplevel_def, type_env_for_module_def]
QED

Theorem gas_shadow_type_env[simp]:
  type_env (MAP gas_shadow_toplevel tops) = type_env tops
Proof
  simp[type_env_def]
QED

Theorem gas_shadow_build_struct_fields_map[simp]:
  !tops tenv acc.
    build_struct_fields_map tenv (MAP gas_shadow_toplevel tops) acc =
    build_struct_fields_map tenv tops acc
Proof
  Induct >> simp[build_struct_fields_map_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, build_struct_fields_map_def]
QED

Theorem gas_shadow_make_struct_fields_map[simp]:
  make_struct_fields_map (MAP gas_shadow_toplevel tops) =
    make_struct_fields_map tops
Proof
  simp[make_struct_fields_map_def]
QED

Theorem gas_shadow_build_flag_info[simp]:
  !tops fmid fnm. build_flag_info (MAP gas_shadow_toplevel tops) fmid fnm =
    build_flag_info tops fmid fnm
Proof
  Induct >> simp[build_flag_info_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, build_flag_info_def]
QED

Theorem gas_shadow_build_var_type_map[simp]:
  !tops. build_var_type_map (MAP gas_shadow_toplevel tops) = build_var_type_map tops
Proof
  Induct >> simp[build_var_type_map_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, build_var_type_map_def]
QED

Theorem gas_shadow_build_hashmap_info[simp]:
  !tops. build_hashmap_info (MAP gas_shadow_toplevel tops) = build_hashmap_info tops
Proof
  Induct >> simp[build_hashmap_info_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, build_hashmap_info_def]
QED

Theorem gas_shadow_build_event_info[simp]:
  !tops tenv acc. build_event_info tenv (MAP gas_shadow_toplevel tops) acc =
    build_event_info tenv tops acc
Proof
  Induct >> simp[build_event_info_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, build_event_info_def]
QED

Theorem gas_shadow_assign_nkeys[simp]:
  !tops n. assign_nkeys (MAP gas_shadow_toplevel tops) n = assign_nkeys tops n
Proof
  Induct >> simp[assign_nkeys_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, assign_nkeys_def]
QED

Theorem gas_shadow_compute_immutables_len[simp]:
  !tops sft. compute_immutables_len sft (MAP gas_shadow_toplevel tops) =
    compute_immutables_len sft tops
Proof
  Induct >> simp[compute_immutables_len_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, compute_immutables_len_def] >>
  rename1 `gas_shadow_mutability mut` >> Cases_on `mut` >> simp[gas_shadow_mutability_def, compute_immutables_len_def]
QED

Theorem gas_shadow_add_module_var_locations[simp]:
  !tops vars. add_module_var_locations (MAP gas_shadow_toplevel tops) vars =
    add_module_var_locations tops vars
Proof
  Induct >> simp[add_module_var_locations_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, add_module_var_locations_def] >>
  rename1 `gas_shadow_mutability mut` >> Cases_on `mut` >> simp[gas_shadow_mutability_def, add_module_var_locations_def]
QED

Theorem gas_shadow_add_immutable_locations[simp]:
  !tops sft off vars.
    add_immutable_locations sft (MAP gas_shadow_toplevel tops) off vars =
    add_immutable_locations sft tops off vars
Proof
  Induct >> simp[add_immutable_locations_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, add_immutable_locations_def] >>
  rename1 `gas_shadow_mutability mut` >> Cases_on `mut` >> simp[gas_shadow_mutability_def, add_immutable_locations_def]
QED

Theorem gas_shadow_extract_layout[simp]:
  !tops. extract_layout (MAP gas_shadow_toplevel tops) = extract_layout tops
Proof
  Induct >> simp[extract_layout_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, extract_layout_def]
  >- (rename1 `VariableDecl vis (gas_shadow_mutability mut) name ty slot` >>
      Cases_on `mut` >> Cases_on `slot` >>
      simp[gas_shadow_mutability_def, extract_layout_def]) >>
  rename1 `HashMapDecl vis tr name kt vt slot` >> Cases_on `slot` >>
  simp[extract_layout_def]
QED

Theorem gas_shadow_collect_module_vars[simp]:
  !tops. collect_module_vars (MAP gas_shadow_toplevel tops) = collect_module_vars tops
Proof
  Induct >> simp[collect_module_vars_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, collect_module_vars_def]
QED

Theorem gas_shadow_build_func_info[simp]:
  !tops sft. build_func_info sft (MAP gas_shadow_toplevel tops) = build_func_info sft tops
Proof
  Induct >> simp[build_func_info_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, build_func_info_def]
QED

Theorem gas_shadow_build_func_param_types[simp]:
  !tops. build_func_param_types (MAP gas_shadow_toplevel tops) = build_func_param_types tops
Proof
  Induct >> simp[build_func_param_types_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, build_func_param_types_def]
QED

Theorem gas_shadow_build_func_return_type[simp]:
  !tops. build_func_return_type (MAP gas_shadow_toplevel tops) = build_func_return_type tops
Proof
  Induct >> simp[build_func_return_type_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, build_func_return_type_def]
QED

Theorem gas_shadow_build_func_mutability[simp]:
  !tops. build_func_mutability (MAP gas_shadow_toplevel tops) = build_func_mutability tops
Proof
  Induct >> simp[build_func_mutability_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, build_func_mutability_def]
QED

Theorem gas_shadow_build_func_ids[simp]:
  !tops n. build_func_ids n (MAP gas_shadow_toplevel tops) = build_func_ids n tops
Proof
  Induct >> simp[build_func_ids_def] >> Cases_on `h` >>
  simp[gas_shadow_toplevel_def, build_func_ids_def]
QED

Theorem gas_shadow_collect_locals[simp]:
  !body. collect_locals (MAP gas_shadow_stmt body) = collect_locals body
Proof
  recInduct collect_locals_ind >>
  simp[gas_shadow_stmt_def, collect_locals_def] >>
  Cases_on `v` >> simp[gas_shadow_stmt_def, collect_locals_def]
QED

Theorem gas_shadow_build_compile_env[simp]:
  !tops vis mut name args ret body trans.
  build_compile_env (MAP gas_shadow_toplevel tops) vis mut name args ret
    (MAP gas_shadow_stmt body) trans =
  build_compile_env tops vis mut name args ret body trans
Proof
  simp[build_compile_env_def]
QED
