Theory entryReachBodyListInverse
Ancestors
  vyperABIRoundtrip vyperABI list option

Theorem entry_list_conversion_inverse:
  !tys vs avs.
    LIST_REL (\ty v. !av. vyper_to_abi env ty v = SOME av ==>
      abi_to_vyper env ty av = SOME v) tys vs /\
    vyper_to_abi_list env tys vs = SOME avs ==>
    abi_to_vyper_list env tys avs = SOME vs
Proof
  Induct_on `tys`
  >- (Cases_on `vs` >> simp[vyper_to_abi_def, abi_to_vyper_def]) >>
  Cases_on `vs` >>
  simp[Once vyper_to_abi_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >>
  `abi_to_vyper_list env tys avs' = SOME t` by metis_tac[] >>
  simp[Once abi_to_vyper_def]
QED

Theorem entry_same_conversion_inverse:
  !vs avs.
    EVERY (\v. !av. vyper_to_abi env ty v = SOME av ==>
      abi_to_vyper env ty av = SOME v) vs /\
    vyper_to_abi_same env ty vs = SOME avs ==>
    abi_to_vyper_list env (REPLICATE (LENGTH avs) ty) avs = SOME vs
Proof
  Induct_on `vs` >>
  simp[Once vyper_to_abi_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> simp[Once abi_to_vyper_def] >> metis_tac[]
QED

Theorem entry_same_conversion_length:
  !vs avs. vyper_to_abi_same env ty vs = SOME avs ==>
    LENGTH avs = LENGTH vs
Proof
  Induct_on `vs` >> simp[Once vyper_to_abi_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
