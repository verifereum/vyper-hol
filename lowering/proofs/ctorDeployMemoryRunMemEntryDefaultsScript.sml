Theory ctorDeployMemoryRunMemEntryDefaults
Ancestors
  ctorDeployMemoryRunMemEntrySupported supportedTypes vyperValue vyperABI
  contractABI vyperTyping words
Libs
  wordsLib

Theorem ctor_supported_scalar_default_strict_type:
  supported_scalar_type ty /\ evaluate_type env ty = SOME tv ==>
  has_type (vyper_to_abi_type env ty) (default_to_abi tv)
Proof
  Cases_on `ty` >>
  gvs[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def] >> Cases_on `b` >>
  gvs[supported_word_type_def, supported_string_type_def,
      supported_int_width_def, evaluate_type_def, default_to_abi_def,
      vyper_to_abi_type_def, has_type_def, valid_int_bound_def] >>
  rpt strip_tac >> gvs[default_to_abi_def, has_type_def, valid_int_bound_def] >>
  simp[int_bits_bound_def] >>
  Cases_on `b'` >>
  gvs[supported_word_type_def, supported_string_type_def,
      evaluate_type_def, default_to_abi_def, vyper_base_to_abi_type_def,
      has_type_def, AllCaseEqs(), wordsTheory.dimword_def]
QED

Theorem ctor_supported_scalar_default_inverse:
  supported_scalar_type ty /\ evaluate_type env ty = SOME tv ==>
  abi_to_vyper env ty (default_to_abi tv) = SOME (default_value tv)
Proof
  Cases_on `ty` >>
  gvs[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def] >> Cases_on `b` >>
  gvs[supported_word_type_def, supported_string_type_def,
      supported_int_width_def, evaluate_type_def, default_to_abi_def,
      default_value_def, abi_to_vyper_def, check_IntV_def,
      within_int_bound_def] >> rpt strip_tac >>
  gvs[default_to_abi_def, default_value_def, abi_to_vyper_def,
      check_IntV_def, within_int_bound_def] >>
  Cases_on `b'` >>
  gvs[supported_word_type_def, supported_string_type_def,
      evaluate_type_def, default_to_abi_def, default_value_def,
      abi_to_vyper_def, compatible_bound_def, AllCaseEqs()]
QED
