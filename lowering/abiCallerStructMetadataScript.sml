(* Numeric struct field metadata follows from the actual full-environment
   builder and successful child evaluation. Shape and submap facts are the
   descent invariants supplied by checked construction at the root. *)
Theory abiCallerStructMetadata
Ancestors
  abiCallerStructSize abiCallerStructMap abiCallerTupleLayout abiCallerTypeEnv
  compileVyper compileEnv valueEncoding vyperTypeABI vyperValue vyperContext
  finite_map list pair

Theorem abi_caller_field_memory_size:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  FLOOKUP (type_env tops) (NONE,struct_name) = SOME (StructArgs args) /\
  FLOOKUP
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans).ce_struct_fields struct_name = SOME fields /\
  MEM (field_name,ty,sz) fields /\ evaluate_type (type_env tops) ty = SOME tv ==>
  sz = type_memory_bytes
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans) ty
Proof
  strip_tac >> drule_all abi_caller_constructed_struct_fields >> strip_tac >>
  gvs[] >> drule_all abi_caller_struct_field_sizes >> strip_tac >>
  drule_all abi_caller_memory_size >> simp[]
QED

Theorem abi_caller_struct_map_fields:
  abi_caller_struct_map sf env /\
  FLOOKUP env (NONE,struct_name) = SOME (StructArgs args) /\
  FLOOKUP sf struct_name = SOME fields ==>
  MAP (\(name,ty,sz). (name,ty)) fields = args
Proof
  simp[abi_caller_struct_map_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem abi_caller_struct_typed_field:
  MAP (\(name,ty,sz). (name,ty)) fields = args /\
  LIST_REL (\ty tv. evaluate_type env ty = SOME tv) (MAP SND args) tvs /\
  MEM (field_name,ty,sz) fields ==>
  ?tv. evaluate_type env ty = SOME tv
Proof
  strip_tac >>
  `MEM (field_name,ty) args` by
    (qpat_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
     simp[MEM_MAP] >> qexists_tac `(field_name,ty,sz)` >> simp[]) >>
  `MEM ty (MAP SND args)` by
    (simp[MEM_MAP] >> qexists_tac `(field_name,ty)` >> simp[]) >>
  drule_all LIST_REL_MEM_IMP >> metis_tac[]
QED

Theorem abi_caller_struct_field_memory:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  env SUBMAP type_env tops /\
  sf SUBMAP (build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans).ce_struct_fields /\
  abi_caller_struct_map sf env /\
  FLOOKUP env (NONE,struct_name) = SOME (StructArgs args) /\
  evaluate_types (env \\ (NONE,struct_name)) (MAP SND args) [] = SOME tvs /\
  FLOOKUP sf struct_name = SOME fields ==>
  EVERY (\(name,ty,sz). sz = type_memory_bytes
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans) ty)
    fields
Proof
  strip_tac >> drule_all abi_caller_struct_map_fields >> strip_tac >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `FLOOKUP (type_env tops) (NONE,struct_name) = SOME (StructArgs args)` by
    (irule FLOOKUP_SUBMAP >> qexists_tac `env` >> simp[]) >>
  `FLOOKUP
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).
      ce_struct_fields struct_name = SOME fields` by
    (irule FLOOKUP_SUBMAP >> qexists_tac `sf` >> simp[]) >>
  `env \\ (NONE,struct_name) SUBMAP type_env tops` by
    (irule SUBMAP_TRANS >> qexists_tac `env` >> simp[]) >>
  simp[EVERY_MEM, FORALL_PROD] >>
  map_every qx_gen_tac [`field_name`, `child_ty`, `sz`] >> strip_tac >>
  drule_all abi_caller_struct_typed_field >> strip_tac >>
  drule_all abi_caller_type_submap >> strip_tac >>
  drule_all abi_caller_field_memory_size >> simp[]
QED
