Theory entryReachBodyScalarConversion
Ancestors
  entryReachBodyConversionSupport supportedTypes vyperTyping vyperABI vyperABIRoundtrip contractABI
  list integer vyperValue vyperArith vyperMisc byte words string combin
  venomMemProps divides

Theorem scalar_forward_inverse[local]:
  supported_scalar_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
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
      abi_to_vyper_def, check_IntV_def, within_int_bound_def,
      compatible_bound_def]
  >~ [`(if b then 1 else 0) <= 1 /\ _`]
  >- (Cases_on `b` >> simp[])
  >~ [`MAP (CHR o w2n) (MAP n2w_o_ORD s) = s`]
  >- (simp[n2w_o_ORD_def, MAP_MAP_o, o_DEF, dimword_8, ORD_BOUND])
  >~ [`compatible_bound b' (LENGTH l)`]
  >- (Cases_on `b'` >>
      gvs[supported_word_type_def, supported_string_type_def,
          value_has_type_def, AllCaseEqs(), compatible_bound_def])
  >~ [`compatible_bound b' (LENGTH l)`]
  >- (Cases_on `b'` >>
      gvs[supported_word_type_def, supported_string_type_def,
          value_has_type_def, AllCaseEqs(), compatible_bound_def]) >>
  conj_tac
  >- (mp_tac (Q.ISPEC `word_of_bytes_be l : 160 word` w2n_lt) >>
      simp[dimword_def] >> CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]) >>
  simp[word_of_bytes_be_def] >> irule word_bytes_roundtrip >>
  simp[divides_def] >> CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem scalar_conversion_typed[local]:
  supported_scalar_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
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
      vyper_base_to_abi_type_def, has_type_def,
      supported_int_width_def, within_int_bound_def,
      valid_int_bound_def, int_bits_bound_def]
  >~ [`Num (if i < 0 then i + 1 else i) < _`]
  >- (Cases_on `i < 0` >> gvs[] >>
      `?k. i = -&k` by (irule NUM_NEGINT_EXISTS >> intLib.ARITH_TAC) >>
      gvs[] >> Cases_on `k` >> gvs[arithmeticTheory.ADD1] >>
      rename1 `k + 1 <= _` >>
      `-&(k + 1) + 1 = (-&k : int)` by (simp[GSYM INT_ADD, INT_NEG_ADD] >> intLib.ARITH_TAC) >>
      gvs[arithmeticTheory.PRE_SUB1])
  >~ [`(if b then 1 else 0) < 2`]
  >- (Cases_on `b` >> simp[])
  >~ [`Num (if i < 0 then i + 1 else i) < _`]
  >- (Cases_on `i < 0` >> gvs[] >>
      `?k. i = -&k` by (irule NUM_NEGINT_EXISTS >> intLib.ARITH_TAC) >>
      gvs[] >> Cases_on `k` >> gvs[arithmeticTheory.ADD1] >>
      rename1 `k + 1 <= _` >>
      `-&(k + 1) + 1 = (-&k : int)` by
        (simp[GSYM INT_ADD, INT_NEG_ADD] >> intLib.ARITH_TAC) >> gvs[])
  >~ [`supported_word_type (BaseT (BytesT b'))`]
  >- (Cases_on `b'` >>
      gvs[supported_word_type_def, evaluate_type_def, value_has_type_def,
          vyper_base_to_abi_type_def, has_type_def, compatible_bound_def,
          dimword_def] >>
      CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[])
  >~ [`supported_string_type (BaseT (BytesT b'))`]
  >- (Cases_on `b'` >>
      gvs[supported_string_type_def, evaluate_type_def, value_has_type_def,
          vyper_base_to_abi_type_def, has_type_def, compatible_bound_def,
          dimword_def] >>
      CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]) >>
  mp_tac (Q.ISPEC `word_of_bytes_be l : 160 word` w2n_lt) >>
  simp[dimword_def] >> CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem entry_scalar_forward_inverse:
  entry_abi_leaf ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
  abi_to_vyper env ty av = SOME v
Proof
  rewrite_tac[entry_abi_leaf_def] >> strip_tac
  >- metis_tac[scalar_forward_inverse] >>
  gvs[evaluate_type_def, AllCaseEqs()] >> Cases_on `v` >>
  gvs[value_has_type_def, vyper_to_abi_def, vyper_to_abi_base_def,
      abi_to_vyper_def, compatible_bound_def]
QED

(* bytes0 has no ABI type: valid_bytes_bound (SOME 0) fails. *)
Theorem entry_scalar_conversion_typed:
  entry_abi_leaf ty /\ ty <> BaseT (BytesT (Fixed 0)) /\
  evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
  has_type (vyper_to_abi_type env ty) av
Proof
  rewrite_tac[entry_abi_leaf_def] >> strip_tac
  >- metis_tac[scalar_conversion_typed] >>
  gvs[evaluate_type_def, AllCaseEqs()] >> Cases_on `v` >>
  gvs[value_has_type_def, vyper_to_abi_def, vyper_to_abi_base_def,
      vyper_base_to_abi_type_def, has_type_def, valid_int_bound_def,
      compatible_bound_def]
  >- (`n < 2 ** 256` suffices_by simp[] >>
      irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** m` >>
      conj_tac >- simp[] >>
      irule arithmeticTheory.EXP_BASE_LEQ_MONO_IMP >> simp[]) >>
  Cases_on `l` >> fs[wordsTheory.dimword_def]
QED
