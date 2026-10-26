(* Struct metadata shape supplied by actual checked compiler construction.
   Deleting a visited declaration preserves the correspondence needed by the
   semantic and compiler ABI traversals. Field sizes are handled separately. *)
Theory abiCallerStructMap
Ancestors
  abiCallerStructFields compileVyper compileEnv vyperContext vyperValue
  vyperAST finite_map list pair

Definition abi_caller_struct_map_def:
  abi_caller_struct_map (sf:(string, (string # type # num) list) fmap) env <=>
    !nsid args. FLOOKUP env nsid = SOME (StructArgs args) ==>
    ?name fields. nsid = (NONE,name) /\
      FLOOKUP sf name = SOME fields /\
      MAP (\(field_name,ty,sz). (field_name,ty)) fields = args
End

Theorem abi_caller_struct_map_lookup:
  abi_caller_struct_map sf env /\
  FLOOKUP env nsid = SOME (StructArgs args) ==>
  ?fields. FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
    MAP (\(field_name,ty,sz). (field_name,ty)) fields = args
Proof
  simp[abi_caller_struct_map_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[nsid_to_string_def]
QED

Theorem abi_caller_constructed_struct_map:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] ==>
  abi_caller_struct_map
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans).ce_struct_fields (type_env tops)
Proof
  strip_tac >> simp[abi_caller_struct_map_def] >> rpt strip_tac >>
  qpat_assum `FLOOKUP (type_env tops) _ = _`
    (mp_tac o PURE_REWRITE_RULE [type_env_def]) >>
  Cases_on `nsid` >> strip_tac >>
  drule abi_caller_type_env_struct >> strip_tac >> gvs[] >>
  drule_all abi_caller_constructed_struct_fields >> strip_tac >>
  qexists_tac `build_struct_fields_one (type_env tops) args` >>
  simp[abi_caller_struct_fields_types]
QED

Theorem abi_caller_struct_map_delete:
  abi_caller_struct_map sf env ==>
  abi_caller_struct_map (sf \\ name) (env \\ (NONE,name))
Proof
  simp[abi_caller_struct_map_def, DOMSUB_FLOOKUP_THM] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  goal_assum drule >> simp[]
QED
