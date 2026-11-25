(* The zero-filled linked immutable prefix represents the initialized cells. *)
Theory linkedZeroImmutables
Ancestors
  linkedStructMemorySize ctorDeployLoweringNoCtor immutableEncodingProofs
  structFieldsProps valueEncodingDefs e2eModsDefs e2eDefs bodyInvSplit
  loweringStateRelDefs compileEnv compileUnit vyperTypeConstantCells
  vyperTypeContractStaticMaps vyperTypeInitialState vyperTypeContract vyperInterpreter
  vyperState vyperContext vyperTypeContractContext immutableEncoding immutableValue
  alist finite_map option rich_list list arithmetic

Theorem initial_immutables_value_default:
  initial_immutables tenv mods = SOME imms /\
  FLOOKUP (get_source_immutables src imms) name = SOME (tv,v) ==>
  v = default_value tv
Proof
  map_every qid_spec_tac [`name`,`tv`,`v`,`imms`] >> Induct_on `mods`
  >- simp[initial_immutables_def, empty_immutables_def, get_source_immutables_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[initial_immutables_def] >>
  Cases_on `initial_immutables tenv mods` >> simp[] >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  Cases_on `h0 = src`
  >- (qpat_x_assum `h0 = src` SUBST_ALL_TAC >>
      metis_tac[no_ctor_initial_module_defaults]) >>
  drule_all initial_immutables_module_preserves_other_source >>
  disch_then (fn th => fs[th]) >>
  metis_tac[]
QED

Theorem linked_initialized_zero_immutables:
  check_contract F am.layouts tx.target mods = SOME art /\
  layouts_agree_mods mods exps am tx /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants (deploy_evaluation_context_mods mods am tx)
    (am with <|immutables updated_by CONS (tx.target,imms);
               exports updated_by CONS (tx.target,exps)|>)
    tx.target mods = SOME am_c ==>
  immutables_section_rel_mods mods (account_immutables am_c tx.target)
    (REPLICATE (imm_len_mods mods) 0w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac check_contract_namespaces_ok >>
  simp[immutables_section_rel_mods_def] >>
  qx_genl_tac [`src`,`name`,`off`,`width`] >> strip_tac >>
  `off + width <= imm_len_mods mods` by
    (qpat_assum `layouts_agree_mods _ _ _ _` (mp_tac o REWRITE_RULE [layouts_agree_mods_def]) >>
     strip_tac >>
     qpat_assum `!src name off width. immutable_region_mods _ src name off width ==> _`
       (qspecl_then [`src`,`name`,`off`,`width`] (fn bound =>
         qpat_assum `immutable_region_mods mods src name off width`
           (ACCEPT_TAC o MATCH_MP bound)))) >>
  qpat_x_assum `immutable_region_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_region_mods_def]) >>
  `MEM (VariableDecl vis Immutable name ty slot) tops` by simp[] >>
  `is_immutable_decl name tops` by metis_tac[is_immutable_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops))` by
    metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM] >>
  `find_var_decl_by_name name tops = NONE` by
    (irule find_var_decl_by_name_NONE_Immutable >> metis_tac[]) >>
  drule_all initial_immutables_contains_decl >>
  simp[IS_SOME_EXISTS] >>
  disch_then (qx_choose_then `cell` assume_tac) >>
  PairCases_on `cell` >>
  `evaluate_type (type_env_all_modules mods) ty = SOME cell0` by
    (irule initial_immutables_all_bare_global_type >>
     qexistsl_tac [`name`,`imms`,`mods`,`src`,`tops`,`cell1`] >> simp[] >>
     rpt strip_tac >>
     qpat_assum `tops = _` (fn shape =>
       qpat_assum `ALL_DISTINCT (FLAT (MAP _ tops))`
         (mp_tac o REWRITE_RULE [shape])) >>
     simp[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND,
          toplevel_vtype_keys_toplevel_def] >>
     metis_tac[module_toplevel_vtype_key_MEM_Variable_any]) >>
  drule_all_then SUBST_ALL_TAC initial_immutables_value_default >>
  qexistsl_tac [`cell0`,`default_value cell0`] >>
  conj_tac
  >- (simp[account_immutables_def, empty_immutables_def] >>
      irule evaluate_all_constants_preserves_bare_global_lookup_type >>
      goal_assum (drule_at Any) >>
      qexistsl_tac [
        `am with <|immutables updated_by CONS (tx.target,imms);
                   exports updated_by CONS (tx.target,exps)|>`,
        `FEMPTY |+ ((src,name),ty)`,`deploy_evaluation_context_mods mods am tx`,`ty`] >>
      simp[constants_do_not_clobber_bare_globals_def,FLOOKUP_UPDATE] >>
      rpt gen_tac >> CCONTR_TAC >> gvs[] >>
      `ALOOKUP mods src = SOME ts` by
        (irule ALOOKUP_ALL_DISTINCT_MEM >> fs[contract_namespaces_ok_def]) >>
      gvs[toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
      metis_tac[module_toplevel_vtype_key_MEM_Variable_any]) >>
  conj_tac >- metis_tac[no_ctor_evaluated_default_admissible] >>
  qabbrev_tac `ce = (ARB:compile_env) with ce_struct_fields := make_struct_fields_map_mods mods` >>
  `type_memory_bytes ce ty = type_memory_size cell0` by
    (mp_tac (Q.INST [`dep` |-> `F`, `env` |-> `type_env_all_modules mods`,
                     `tv` |-> `cell0`]
       (SPEC_ALL make_struct_fields_map_mods_memory_size)) >>
     simp[Abbr `ce`]) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map_mods mods)) ty =
    type_memory_size cell0` by
    (qspecl_then [`ce`,`ty`] mp_tac type_mem_bytes_type_memory_bytes >>
     simp[Abbr `ce`] >> disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `width = type_memory_size cell0` by metis_tac[] >>
  `imm_len_mods mods = off + type_memory_size cell0 +
                         (imm_len_mods mods - (off + type_memory_size cell0))` by
    decide_tac >>
  conj_tac >-
    (qpat_assum `type_mem_bytes _ ty = type_memory_size cell0`
       (ACCEPT_TAC o SYM)) >>
  qabbrev_tac `suffix_len = imm_len_mods mods - (off + type_memory_size cell0)` >>
  `REPLICATE (imm_len_mods mods) (0w:word8) =
    REPLICATE off 0w ++ REPLICATE (type_memory_size cell0) 0w ++
    REPLICATE suffix_len 0w` by
    (qpat_assum `imm_len_mods mods = _` (SUBST1_TAC o SYM) >>
     simp[rich_listTheory.REPLICATE_APPEND, Abbr `suffix_len`, ADD_ASSOC]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (qspecl_then [`cell0`,`REPLICATE off (0w:word8)`,`REPLICATE suffix_len (0w:word8)`]
        mp_tac (cj 1 immutable_default_zero_decodes_mutual) >> simp[]) >>
  `type_memory_size cell0 - (suffix_len + type_memory_size cell0) = 0` by
    decide_tac >>
  simp[mem_bytes_at_def, rich_listTheory.DROP_APPEND, rich_listTheory.TAKE_APPEND,
       GSYM no_ctor_default_encoding, listTheory.TAKE_LENGTH_TOO_LONG,
       encode_immutable_value_length, immutable_value_bytes_encoded]
QED
