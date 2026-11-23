Theory linkedEntryStructAcyclic
Ancestors
  checkedCopyAcyclic copyAccessibility copyAcyclicProps typedCopyDomain structSourceProps
  loweringStateRelDefs vyperTypeConstantFold vyperTypeContract vyperTypeContractContext vyperContext vyperAST
  compileEnv finite_map alist list pair relation combin

Theorem checked_struct_metadata_acyclic_mods:
  check_contract dep layouts addr mods = SOME art /\
  sfields_tenv_consistent sf (type_env_all_modules mods) ==>
  acyclic_struct_metadata sf
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac o REWRITE_RULE [sfields_tenv_consistent_def])) >>
  `copy_source_agrees sf (type_env_all_modules mods)` by
    (rw[copy_source_agrees_def] >>
     qpat_assum `!nsid args. FLOOKUP (type_env_all_modules mods) nsid = _ ==> _`
       (drule_then strip_assume_tac) >>
     fs[get_struct_fields_def]) >>
  irule wf_type_copy_child_acyclic >>
  irule copy_fields_accessible_well_founded >>
  gen_tac >> Cases_on `FLOOKUP sf name` >- simp[get_struct_fields_def] >>
  qpat_assum `!name fields. FLOOKUP sf name = SOME fields ==> _`
    (drule_then strip_assume_tac) >>
  PairCases_on `nsid` >>
  `ALL_DISTINCT (MAP FST mods)` by
    (drule check_contract_namespaces_ok >> simp[contract_namespaces_ok_def]) >>
  qpat_x_assum `FLOOKUP (type_env_all_modules mods) _ = SOME (StructArgs args)` mp_tac >>
  simp[FLOOKUP_type_env_all_modules] >>
  Cases_on `ALOOKUP mods nsid0` >> simp[] >> strip_tac >>
  rename1 `ALOOKUP mods nsid0 = SOME tops` >>
  drule_then strip_assume_tac type_env_for_module_struct_origin >>
  `MEM (nsid0,tops) mods` by (irule ALOOKUP_MEM >> asm_rewrite_tac[]) >>
  `EVERY (assignable_type (type_env_all_modules mods) o SND) args` by
    (qspecl_then [`dep`, `layouts`, `addr`, `mods`, `art`, `nsid0`, `tops`, `name'`, `args`]
       mp_tac check_contract_struct_fields_assignable >> asm_rewrite_tac[]) >>
  `EVERY (assignable_type (type_env_all_modules mods)) (MAP SND args)` by
    fs[EVERY_MAP, o_DEF] >>
  `MAP (FST o SND) (get_struct_fields sf name) = MAP SND args` by
    (PURE_REWRITE_TAC [get_struct_fields_def] >>
     qpat_assum `FLOOKUP sf name = SOME x` SUBST1_TAC >>
     simp[NoAsms] >> FIRST_ASSUM ACCEPT_TAC) >>
  qpat_assum `(nsid0,nsid1) = (nsid0,name')` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  qpat_assum `name = nsid_to_string (nsid0,nsid1)` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  qpat_assum `MAP (FST o SND) (get_struct_fields sf name) = _` SUBST1_TAC >>
  irule assignable_list_copy_accessible >>
  qexists_tac `type_env_all_modules mods` >> asm_rewrite_tac[]
QED
