(* Memory sizes use the linked compiler's qualified struct field map. *)
Theory linkedStructMemorySize
Ancestors
  linkedStructFields structFieldsProps abiCallerTypeEnv compileUnit compileEnv
  vyperContext vyperTypeContract vyperValue valueEncoding vfmConstants finite_map list

Theorem make_struct_fields_map_mods_memory_size:
  contract_namespaces_ok dep mods /\
  ce.ce_struct_fields = make_struct_fields_map_mods mods /\
  env SUBMAP type_env_all_modules mods /\ evaluate_type env ty = SOME tv ==>
  type_memory_bytes ce ty = type_memory_size tv
Proof
  `!ce ty. contract_namespaces_ok dep mods /\
      ce.ce_struct_fields = make_struct_fields_map_mods mods ==>
      !tv. evaluate_type (type_env_all_modules mods) ty = SOME tv ==>
        type_memory_bytes ce ty = type_memory_size tv`
    suffices_by
      (strip_tac >> strip_tac >>
       drule_all abi_caller_type_submap >> metis_tac[]) >>
  ho_match_mp_tac type_memory_bytes_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt strip_tac >>
      gvs[evaluate_type_def, AllCaseEqs(), type_memory_bytes_def,
          type_memory_size_def, evaluate_types_OPT_MMAP] >>
      drule_all make_struct_fields_map_mods_lookup >> strip_tac >>
      simp[get_struct_fields_def] >>
      drule build_struct_fields_one_size >> simp[])
  >~ [`TupleT tys`]
  >- (rpt strip_tac >>
      gvs[evaluate_type_def, AllCaseEqs(), type_memory_bytes_def,
          type_memory_size_def, evaluate_types_OPT_MMAP] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> irule tuple_memory_bytes_size >>
      qexists_tac `type_env_all_modules mods` >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), type_memory_bytes_def,
      type_memory_size_def, word_size_def]
QED
