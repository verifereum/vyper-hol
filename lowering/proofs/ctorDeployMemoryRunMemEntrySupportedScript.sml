Theory ctorDeployMemoryRunMemEntrySupported
Ancestors
  supportedTypes vyperValue vyperABI contractABI vyperTyping valueEncoding words
Libs
  wordsLib

Theorem ctor_supported_scalar_strict_type:
  supported_scalar_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  vyper_to_abi env ty v = SOME av ==>
  has_type (vyper_to_abi_type env ty) av
Proof
  Cases_on `ty` >>
  gvs[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def] >>
  Cases_on `b` >>
  gvs[supported_word_type_def, supported_string_type_def,
      evaluate_type_def] >>
  Cases_on `v` >> rpt strip_tac >>
  gvs[value_has_type_def, vyper_to_abi_def, vyper_to_abi_base_def,
      has_type_def, supported_int_width_def] >>
  simp[valid_int_bound_def] >>
  gvs[within_int_bound_def, int_bits_bound_def]
  >- (Cases_on `i < 0` >> gvs[arithmeticTheory.PRE_SUB1]
      >> intLib.ARITH_TAC)
  >- (Cases_on `b` >> simp[])
  >- (Cases_on `i < 0` >> gvs[]
      >> intLib.ARITH_TAC)
  >- (Cases_on `b'` >>
      gvs[supported_word_type_def, evaluate_type_def,
          value_has_type_def, has_type_def, AllCaseEqs(), wordsTheory.dimword_def])
  >- (Cases_on `b'` >>
      gvs[supported_string_type_def, evaluate_type_def,
          value_has_type_def, has_type_def, AllCaseEqs(), wordsTheory.dimword_def])
  >> qspec_then `word_of_bytes_be l : address` mp_tac wordsTheory.w2n_lt
  >> simp[]
QED

Theorem ctor_supported_scalar_inverse:
  supported_scalar_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  vyper_to_abi env ty v = SOME av ==>
  abi_to_vyper env ty av = SOME v
Proof
  Cases_on `ty` >>
  gvs[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def] >>
  Cases_on `b` >>
  gvs[supported_word_type_def, supported_string_type_def,
      evaluate_type_def] >>
  Cases_on `v` >> rpt strip_tac >>
  gvs[value_has_type_def, vyper_to_abi_def, vyper_to_abi_base_def,
      abi_to_vyper_def, check_IntV_def, supported_int_width_def,
      within_int_bound_def]
  >- (Cases_on `b` >> simp[])
  >- (POP_ASSUM_LIST (K ALL_TAC) >> Induct_on `s` >>
      simp[vyperMiscTheory.n2w_o_ORD_def, wordsTheory.w2n_n2w,
           stringTheory.ORD_BOUND, stringTheory.CHR_ORD])
  >- (Cases_on `b'` >>
      gvs[supported_word_type_def, evaluate_type_def,
          value_has_type_def, compatible_bound_def, AllCaseEqs()])
  >- (Cases_on `b'` >>
      gvs[supported_string_type_def, evaluate_type_def,
          value_has_type_def, compatible_bound_def, AllCaseEqs()])
  >> conj_tac
  >- (qspec_then `word_of_bytes_be l : address` mp_tac wordsTheory.w2n_lt >> simp[])
  >> simp[listTheory.LIST_EQ_REWRITE, byteTheory.word_of_bytes_be_def,
          byteTheory.LENGTH_word_to_bytes, byteTheory.word_to_bytes_def,
          byteTheory.EL_word_to_bytes_aux, byteTheory.get_byte_word_of_bytes_be,
          byteTheory.first_byte_at_0w]
QED
