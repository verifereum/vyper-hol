Theory entryReachBodyAggregateConversion
Ancestors
  entryReachBodyConversionSupport vyperTyping vyperABI contractABI list

Theorem entry_list_conversion_typed:
  !tys tvs vs avs.
    LIST_REL (\ty tv. !v av.
      value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
      has_type (vyper_to_abi_type env ty) av) tys tvs /\
    values_have_types tvs vs /\
    vyper_to_abi_list env tys vs = SOME avs ==>
    has_types (vyper_to_abi_types env tys) avs
Proof
  Induct_on `tys`
  >- (Cases_on `vs` >> simp[vyper_to_abi_def, vyper_to_abi_type_def,
                           has_type_def]) >>
  Cases_on `tvs` >> Cases_on `vs` >>
  simp[value_has_type_def, vyper_to_abi_def, vyper_to_abi_type_def,
       has_type_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[has_type_def] >> metis_tac[]
QED

Theorem entry_same_conversion_typed:
  (!v av. value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
          has_type (vyper_to_abi_type env ty) av) /\
  EVERY (value_has_type tv) vs /\
  vyper_to_abi_same env ty vs = SOME avs ==>
  have_type (vyper_to_abi_type env ty) avs
Proof
  qid_spec_tac `avs` >> Induct_on `vs` >>
  simp[Once vyper_to_abi_def, has_type_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[has_type_def] >> metis_tac[]
QED
