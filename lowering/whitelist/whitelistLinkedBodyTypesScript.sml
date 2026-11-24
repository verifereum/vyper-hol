Theory whitelistLinkedBodyTypes
Ancestors
  whitelistLinkedBodyEnv whitelistLinkedTypeSupport whitelistCheckerTypes
  vyperTypeContractContext vyperTypeContractStaticMaps vyperTypeConstantFold
  whitelistLinkedStructTypeProps vyperTypeContract finite_map list pair

Theorem linked_checked_body_type_facts:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tops ==>
  linked_body_type_facts tops src (type_env_all_modules mods)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP FST mods)` by
    (drule check_contract_namespaces_ok >> simp[contract_namespaces_ok_def]) >>
  simp[linked_body_type_facts_def] >> conj_tac
  >- (rpt strip_tac >> irule linked_assignable_type_supported_place >>
      qexistsl [`mods`, `src`] >> simp[]) >>
  conj_tac >> rpt strip_tac >> drule_all checked_struct_descriptor >> simp[]
QED
