(* Return metadata is invariant under parameter registration and local declarations. *)
Theory returnMetadataPtr
Ancestors
  entryStateRel bodySim retAbiPlanProps structFieldsProps compileVyper compileEnv
  supportedPlaceAssignable supportedDecls supportedProgram e2eDefs
  vyperTypeContractStaticMaps vyperTypeContract
  vyperInterpreter vyperTypeSystem
  list option finite_map

val _ = Parse.hide "body";

Theorem register_same_frame_metadata:
  compile_register_positional_args cenv0 args off st = (cenv, sa) /\
  same_frame cenv next ==>
  next with <| ce_vars := cenv0.ce_vars; ce_var_type := cenv0.ce_var_type;
               ce_dynarray_capacity := cenv0.ce_dynarray_capacity |> = cenv0
Proof
  strip_tac >> drule compile_register_positional_args_cenv >> strip_tac >>
  gvs[same_frame_def, compileEnvTheory.compile_env_component_equality]
QED

Theorem external_package_struct_fields:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) ==>
  cenv0.ce_struct_fields = make_struct_fields_map tops
Proof
  simp[package_external_fn_def, set_external_package_target_def] >>
  Cases_on `ret = NoneT` >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       build_compile_env_ce_struct_fields] >> strip_tac >>
  gvs[build_compile_env_ce_struct_fields]
QED

Theorem external_package_ret_abi_plan:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  assignable_type (type_env tops) ret /\ ret <> NoneT ==>
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) cenv0.ce_ret_enc_info /\
  vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) = cenv0.ce_max_return_size
Proof
  strip_tac >>
  gvs[package_external_fn_def, set_external_package_target_def,
      update_cenv_nonreentrant_def] >>
  irule build_compile_env_ret_abi_plan >> simp[]
QED

Theorem external_frame_struct_fields:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next ==>
  next.ce_struct_fields = make_struct_fields_map tops
Proof
  strip_tac >> drule external_package_struct_fields >> strip_tac >>
  drule_all register_same_frame_metadata >>
  simp[compile_env_component_equality]
QED

Theorem external_frame_ret_abi_plan:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  assignable_type (type_env tops) ret /\ ret <> NoneT ==>
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) next.ce_ret_enc_info
Proof
  strip_tac >> drule_all external_package_ret_abi_plan >> strip_tac >>
  drule_all register_same_frame_metadata >>
  simp[compile_env_component_equality] >> metis_tac[]
QED

Theorem external_frame_return_size:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  assignable_type (type_env tops) ret /\ ret <> NoneT ==>
  vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) = next.ce_max_return_size
Proof
  strip_tac >> drule_all external_package_ret_abi_plan >> strip_tac >>
  drule_all register_same_frame_metadata >>
  simp[compile_env_component_equality] >> metis_tac[]
QED

Theorem external_frame_type_memory_bytes:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  type_memory_bytes next ty = type_memory_size tv
Proof
  strip_tac >> drule_all external_frame_struct_fields >> strip_tac >>
  irule make_struct_fields_map_memory_size >> simp[] >>
  metis_tac[typedCopyProducerTheory.distinct_type_keys_struct_args_unique]
QED

Theorem checked_supported_external_return[local]:
  !decls tops mods art src name mut nr args defaults ret fbody.
  EVERY (supported_declaration_header tops) decls /\
  EVERY (check_toplevel_decl mods art src) decls /\
  lookup_function NONE name External decls =
    SOME (mut, nr, args, defaults, ret, fbody) ==>
  well_formed_type (type_env_all_modules mods) ret /\
  supported_function_return tops External ret
Proof
  Induct >> simp[lookup_function_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h` >>
  gvs[supported_declaration_header_def, check_toplevel_decl_def,
      lookup_function_def]
  >~ [`if s = name /\ f = External then _ else _`]
  >- (Cases_on `s = name /\ f = External` >> gvs[]
      >- simp[well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >~ [`if s = name /\ f = External then _ else _`]
  >- (Cases_on `s = name /\ f = External` >> gvs[]
      >- gvs[assignable_type_well_formed] >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >~ [`lookup_function _ _ _ (VariableDecl vis _ _ _ _ :: _)`]
  >- (Cases_on `vis` >> gvs[lookup_function_def] >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >~ [`lookup_function _ _ _ (HashMapDecl vis _ _ _ _ _ :: _)`]
  >- (Cases_on `vis` >> gvs[lookup_function_def] >>
      first_x_assum irule >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem source_external_return_contract:
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, nr, args, defaults, ret, fbody) ==>
  well_formed_type (type_env tops) ret /\
  supported_function_return tops External ret
Proof
  strip_tac >> gvs[source_typing_ok_def, supported_program_def,
                  supported_declaration_headers_def] >>
  `EVERY (check_toplevel_decl [(NONE,tops)] art NONE) tops` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     drule check_contract_toplevel_decl_MEM >>
     disch_then irule >> simp[]) >>
  drule_all checked_supported_external_return >>
  simp[vyperContextTheory.type_env_all_modules_def,
       vyperContextTheory.type_env_def, FUNION_FEMPTY_2]
QED

Theorem source_typing_distinct_type_keys:
  source_typing_ok tops am tx ==>
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))
Proof
  rw[source_typing_ok_def, check_contract_def] >>
  drule contract_namespaces_ok_module_type_def_keys >> simp[]
QED

Theorem source_external_frame_type_memory_bytes:
  source_typing_ok tops am tx /\
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next ==>
  !ty tv. evaluate_type (type_env tops) ty = SOME tv ==>
  type_memory_bytes next ty = type_memory_size tv
Proof
  rpt strip_tac >> drule source_typing_distinct_type_keys >> strip_tac >>
  drule_all external_frame_type_memory_bytes >> simp[]
QED

Theorem source_external_frame_struct_metadata_acyclic:
  supported_program tops /\ source_typing_ok tops am tx /\
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next ==>
  acyclic_struct_metadata next.ce_struct_fields
Proof
  strip_tac >> drule_all external_frame_struct_fields >> strip_tac >>
  gvs[source_typing_ok_def] >>
  drule_all typedCopyProducerTheory.supported_checked_struct_metadata_acyclic >>
  simp[]
QED
