Theory immutableRegionTypingProps
Ancestors
  bodyInvSplit bodyInvCodeProps exprBodyPreProps exprSimHypsDefs
  structFieldsProps typedMemoryCopy vyperTypeInvariants vyperTypeSystem
  finite_map alist list compileEnv vyperValue vyperContext valueEncoding

Theorem immutable_decl_bare_global_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  ALOOKUP mods src = SOME tops /\
  MEM (VariableDecl vis Immutable id ty slot) tops ==>
  FLOOKUP env.bare_globals (src,id) = SOME ty
Proof
  strip_tac >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then (assume_tac o SPEC_ALL) contract_inv_module_codes >>
  `get_module_code cx src = SOME tops` by metis_tac[] >>
  fs[env_consistent_def, env_context_consistent_def, bare_globals_complete_def] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem immutable_region_mods_type:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  immutable_region_mods mods src id off bytes ==>
  ?ts ty tv. ALOOKUP mods src = SOME ts /\
    FLOOKUP env.bare_globals (src,id) = SOME ty /\
    cenv.ce_module_var_type (src,id) = SOME ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    bytes = type_memory_size tv
Proof
  strip_tac >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac contract_inv_struct_fields >>
  drule_then (assume_tac o SPEC_ALL) contract_inv_module_codes >>
  qpat_assum `immutable_region_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_region_mods_def]) >>
  `get_module_code cx src = SOME tops` by metis_tac[] >>
  `FLOOKUP env.bare_globals (src,id) = SOME ty` by
    (irule immutable_decl_bare_global_mods >>
     qexistsl_tac [`cenv`, `ctx`, `cx`, `es`, `exps`, `mods`, `slot`, `tops`, `vis`] >>
     simp[]) >>
  drule_all_then strip_assume_tac env_consistent_bare_global_find_NONE >>
  `well_formed_type (get_tenv cx) ty` by
    (fs[env_consistent_def, env_context_consistent_def] >>
     qpat_x_assum `!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==> _`
       (qspecl_then [`src`, `id`, `Type ty`] mp_tac) >>
     simp[well_formed_vtype_def]) >>
  fs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  rename1 `evaluate_type (get_tenv cx) ty = SOME x` >>
  `type_memory_bytes cenv ty = type_memory_size x` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
     fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  qpat_assum `type_memory_bytes cenv ty = _`
    (assume_tac o REWRITE_RULE [GSYM type_mem_bytes_type_memory_bytes]) >>
  fs[expr_sim_inv_mods_def, bare_globals_layout_def] >>
  metis_tac[]
QED
