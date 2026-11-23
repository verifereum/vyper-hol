Theory linkedCheckedDeclarationNames
Ancestors
  supportedNames supportedProgram vyperAST vyperTypeContract
  vyperTypeContractStaticMaps vyperTypeContractContext list rich_list alist

Theorem check_contract_supported_declaration_names_mods:
  check_contract dep layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  supported_selectors_distinct tops ==>
  supported_declaration_names tops /\
  ALL_DISTINCT (supported_internal_function_names tops)
Proof
  strip_tac >>
  `MEM (src,tops) mods` by (irule ALOOKUP_MEM >> asm_rewrite_tac[]) >>
  `ALL_DISTINCT (contract_keys self_member_keys_toplevel mods) /\
   ALL_DISTINCT (contract_keys event_keys_toplevel mods)` by
    (drule check_contract_namespaces_ok >> simp[contract_namespaces_ok_def]) >>
  `ALL_DISTINCT (FLAT (MAP (self_member_keys_toplevel src) tops)) /\
   ALL_DISTINCT (FLAT (MAP (event_keys_toplevel src) tops))` by
    (conj_tac >> irule vyperTypeContractTheory.contract_keys_module_distinct >>
     qexists_tac `mods` >> asm_rewrite_tac[]) >>
  `sublist (MAP (\name. (src,name)) (supported_function_names tops))
     (FLAT (MAP (self_member_keys_toplevel src) tops))` by
    (qsuff_tac `!ts. sublist (MAP (\name. (src,name)) (supported_function_names ts))
       (FLAT (MAP (self_member_keys_toplevel src) ts))`
     >- (disch_then (qspec_then `tops` ACCEPT_TAC)) >>
     Induct >> simp[supported_function_names_def, sublist_nil] >>
     Cases >> simp[supported_function_names_def, self_member_keys_toplevel_def] >>
     simp[GSYM sublist_cons, sublist_cons_include]) >>
  `ALL_DISTINCT (supported_function_names tops)` by
    (irule (INST_TYPE [beta |-> ``:num option # string``] ALL_DISTINCT_MAP) >>
     qexists_tac `\n. (src,n)` >>
     irule sublist_ALL_DISTINCT >>
     qexists_tac `FLAT (MAP (self_member_keys_toplevel src) tops)` >>
     asm_rewrite_tac[]) >>
  `!ts. sublist (supported_internal_function_names ts) (supported_function_names ts)` by
    (Induct >> simp[supported_internal_function_names_def, supported_function_names_def,
                    sublist_nil] >>
     Cases >> simp[supported_internal_function_names_def, supported_function_names_def] >>
     Cases_on `f` >>
     simp[GSYM sublist_cons, sublist_cons_include]) >>
  conj_tac
  >- (simp[supported_declaration_names_def] >> conj_tac
      >- (`!ts. MAP (\name. (src,name)) (supported_event_names ts) =
               FLAT (MAP (event_keys_toplevel src) ts)` by
            (Induct >> simp[supported_event_names_def] >>
             Cases >> simp[event_keys_toplevel_def]) >>
          irule (INST_TYPE [beta |-> ``:num option # string``] ALL_DISTINCT_MAP) >>
          qexists_tac `\n. (src,n)` >> simp[]) >>
      simp[EVERY_MEM] >> Cases >> simp[supported_function_header_names_def] >>
      strip_tac >> drule_all check_contract_toplevel_decl_MEM_checked >>
      simp[check_toplevel_decl_def, params_ok_def, supported_function_bindings_def]) >>
  irule sublist_ALL_DISTINCT >> qexists_tac `supported_function_names tops` >> simp[]
QED
