Theory whitelistCheckedBareGlobalProps
Ancestors
  alist finite_map pair vyperAST vyperContext vyperTypeContract
  vyperTypeContractStaticMaps

Theorem checked_bare_global_vtype:
  check_contract mode layouts addr mods = SOME art /\
  FLOOKUP art.cta_bare_globals k = SOME ty ==>
  FLOOKUP art.cta_toplevel_vtypes k = SOME (Type ty)
Proof
  strip_tac >> PairCases_on `k` >>
  `ALOOKUP [((tx:call_txn).target, mods)] tx.target = SOME mods` by simp[] >>
  drule_all check_contract_bare_globals_consistent_checked >>
  disch_then (qspec_then `ARB` strip_assume_tac)
QED
