Theory whitelistLinkedStructTypeProps
Ancestors
  list pair alist finite_map vyperAST vyperContext vyperTypeSystem vyperTypeContract
  vyperTypeContractContext vyperTypeContractStaticMaps vyperTypeConstantFold
  structSourceProps supportedPlaceAssignable whitelistCheckerTypes
  whitelistCheckerExprs

Theorem checked_struct_descriptor:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  FLOOKUP (type_env_all_modules mods) k = SOME (StructArgs fs) ==>
  EVERY (assignable_type (type_env_all_modules mods) o SND) fs /\
  (well_formed_type (type_env_all_modules mods) (StructT k) ==>
   assignable_type (type_env_all_modules mods) (StructT k)) /\
  (src = NONE /\ FST k = NONE ==> supported_struct_fields tops k = SOME fs)
Proof
  strip_tac >> Cases_on `k` >> rename1 `(owner,name)` >>
  `ALL_DISTINCT (MAP FST mods)` by
    (drule check_contract_namespaces_ok >> simp[contract_namespaces_ok_def]) >>
  `?decls. ALOOKUP mods owner = SOME decls /\
           FLOOKUP (type_env_for_module owner decls) (owner,name) =
           SOME (StructArgs fs)` by
    (Cases_on `ALOOKUP mods owner` >> fs[FLOOKUP_type_env_all_modules]) >>
  `MEM (StructDecl name fs) decls` by
    (drule type_env_for_module_struct_origin >> simp[]) >>
  `check_toplevel_decl mods art owner (StructDecl name fs)` by
    (irule check_contract_toplevel_decl_MEM_checked >> metis_tac[]) >>
  `fs <> [] /\ EVERY (assignable_type (type_env_all_modules mods) o SND) fs` by
    (qpat_x_assum `check_toplevel_decl _ _ _ _` mp_tac >>
     simp[check_toplevel_decl_def, EVERY_MEM, FORALL_PROD] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  simp[] >> conj_tac
  >- (strip_tac >> drule_all well_formed_struct_fields_deleted >> strip_tac >>
      simp[Once assignable_type_def, EVERY_MEM] >> rpt strip_tac >>
      irule assignable_type_submap >> conj_tac
      >- (qexists_tac `type_env_all_modules mods` >> fs[EVERY_MEM])
      >> fs[EVERY_MEM])
  >> strip_tac >> gvs[] >> irule type_env_struct_fields >> simp[type_env_def]
QED
