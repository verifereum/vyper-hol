Theory whitelistLinkedHeaderProps
Ancestors
  alist list rich_list pair combin bodyCallSupport e2eDefs supportedDecls
  supportedTypes vyperTypeContract vyperTypeContractContext
  vyperTypeContractStaticMaps vyperImportRefs vyperImportRefsProps
  whitelistCheckerExprs whitelistLinkedTypeSupport whitelistAllocatedHeaderProps
  whitelistEventTypeProps

Triviality linked_module_header:
  ALL_DISTINCT (MAP FST mods) /\ ALOOKUP mods src = SOME tops /\
  check_toplevel_decl mods art src tl /\
  (src <> NONE ==> imported_toplevel_refs_ok tl) ==>
  supported_module_declaration_header tops tl
Proof
  Cases_on `tl` >>
  simp[check_toplevel_decl_def, imported_toplevel_refs_ok_def,
       supported_module_declaration_header_def, supported_declaration_header_def]
  >~ [`supported_function_return tops vis ret`]
  >- (Cases_on `vis` >>
      simp[function_header_ok_def, supported_function_return_def,
           supported_return_type_def] >>
      metis_tac[linked_assignable_type_supported_place])
  >- (rename1 `case mut of Storage => _ | Transient => _ | Immutable => _ | Constant e => _` >>
      Cases_on `mut` >>
      simp[check_toplevel_decl_def, supported_declaration_header_def,
           supported_storage_type_def, GSYM supported_place_type_def,
           supported_value_type_def] >>
      metis_tac[linked_assignable_type_supported_place])
  >~ [`supported_hashmap_value tops vt`]
  >- (strip_tac >> conj_tac
      >- metis_tac[checker_hashmap_key_supported] >>
      metis_tac[linked_check_value_type_supported_hashmap_value])
  >~ [`EVERY (supported_place_type tops o SND) fields`]
  >- (simp[NULL_EQ, EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
      metis_tac[linked_assignable_type_supported_place])
  >> simp[FILTER_MAP, I_o_ID, EVERY_MEM, FORALL_PROD]
  >> rpt strip_tac
  >> rename1 `MEM ((name,ty),indexed) fields`
  >> `assignable_type (type_env_all_modules mods) ty /\
      (indexed ==> event_indexable_type ty)` by metis_tac[]
  >> `supported_nested_type supported_event_leaf_type (LENGTH tops) tops ty` by
       (irule linked_assignable_type_supported_nested >>
        simp[supported_event_leaf_type_def] >> metis_tac[])
  >> Cases_on `indexed` >> gvs[] >> metis_tac[checker_indexed_event_type_supported]
QED

Triviality main_allocated_headers:
  module_allocated am.layouts tx.target NONE tops /\ layouts_agree tops am tx /\
  EVERY (supported_module_declaration_header tops) tops ==>
  supported_declaration_headers tops
Proof
  simp[module_allocated_def, supported_declaration_headers_def, EVERY_MEM] >>
  strip_tac >> qx_gen_tac `tl` >> strip_tac >>
  qpat_x_assum `!e. MEM e tops ==> supported_module_declaration_header tops e`
    (drule_then assume_tac) >>
  qpat_x_assum `!e. MEM e tops ==> toplevel_allocated _ _ _ e`
    (drule_then assume_tac) >>
  drule_all_then mp_tac layouts_agree_allocated_header >>
  Cases_on `tl` >> fs[supported_module_declaration_header_def]
  >~ [`supported_declaration_header _ (VariableDecl _ _ _ _ _)`]
  >- (rename1 `supported_declaration_header _ (VariableDecl _ mut _ _ slot)` >>
      Cases_on `mut` >> Cases_on `slot` >> gvs[supported_declaration_header_def]) >>
  simp[supported_hashmap_header_contract]
QED

Theorem check_contract_linked_supported_declaration_headers:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  (src = NONE ==> layouts_agree tops am tx) ==>
  EVERY (supported_module_declaration_header tops) tops /\
  (src = NONE ==> supported_declaration_headers tops)
Proof
  strip_tac >> conj_asm1_tac
  >- (simp[EVERY_MEM] >> qx_gen_tac `tl` >> strip_tac >>
      `ALL_DISTINCT (MAP FST mods)` by
        (drule check_contract_namespaces_ok >> simp[contract_namespaces_ok_def]) >>
      `check_toplevel_decl mods art src tl` by
        (drule_all check_contract_toplevel_decl_MEM_checked >> simp[]) >>
      `src <> NONE ==> imported_toplevel_refs_ok tl` by
        (Cases_on `src` >> gvs[] >> drule ALOOKUP_MEM >> strip_tac >>
         drule_all check_contract_imported_toplevel_refs_ok >> simp[EVERY_MEM]) >>
      metis_tac[linked_module_header]) >>
  strip_tac >> gvs[] >> irule main_allocated_headers >>
  drule_all check_contract_main_module_allocated >> strip_tac >> metis_tac[]
QED
