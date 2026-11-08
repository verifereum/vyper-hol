Theory entryAbiSourceSparseTyping
Ancestors
  entryAbiSparseTyping vyperABI vyperABIRoundtrip vyperTypeDefaults
  vyperTypeABI vyperTyping contractABI list rich_list

Theorem source_default_abi_typed[local]:
  evaluate_type env ty = SOME tv /\
  (!v av. value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
    has_type (vyper_to_abi_type env ty) av) ==>
  has_type (vyper_to_abi_type env ty) (default_to_abi tv)
Proof
  strip_tac >> drule default_value_has_type_thm >> strip_tac >>
  drule (cj 1 vyper_to_abi_default_value) >> strip_tac >> metis_tac[]
QED

Theorem source_sparse_conversion_abi_typed:
  evaluate_type env ty = SOME tv /\
  (!v av. value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
    has_type (vyper_to_abi_type env ty) av) /\
  (!i v. i < n /\ ALOOKUP sparse i = SOME v ==> value_has_type tv v) /\
  vyper_to_abi_sparse env ty tv n sparse = SOME avs ==>
  EVERY (has_type (vyper_to_abi_type env ty)) avs
Proof
  strip_tac >> drule_all source_default_abi_typed >> strip_tac >>
  irule sparse_conversion_abi_typed >> simp[] >> metis_tac[]
QED
