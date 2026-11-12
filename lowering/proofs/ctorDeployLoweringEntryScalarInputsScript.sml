Theory ctorDeployLoweringEntryScalarInputs
Ancestors
  supportedTypes vyperTypeABI vyperABIRoundtrip compileEnv abiDecoderCoherence
  words integer list vyperABI vyperValue vyperTyping vyperTypeValues contractABI
  valueEncoding vyperArith venomMemProofs

Theorem deploy_supported_scalar_abi_valid:
 !ty env tv v av.
 supported_scalar_type ty /\ evaluate_type env ty = SOME tv /\
 value_has_type tv v /\ val_wf tv v /\
 vyper_to_abi env ty v = SOME av ==>
 has_type (vyper_to_abi_type env ty) av
Proof
 Cases_on `ty` >>
 simp[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def] >>
 Cases_on `b` >>
 simp[supported_word_type_def, supported_string_type_def] >>
 rpt strip_tac >>
 Cases_on `v` >>
 gvs[evaluate_type_def, value_has_type_def, vyper_to_abi_base_def,
     supported_int_width_def, has_type_def, valid_int_bound_def,
     int_bits_bound_def, within_int_bound_def] >>
 all_tac
 >~ [`(if b then 1 else 0) < 2`] >- (Cases_on `b` >> simp[])
 >~ [`Num (if i < 0 then i + 1 else i) < 2 ** PRE n`]
 >- (Cases_on `i < 0` >> gvs[arithmeticTheory.PRE_SUB1] >>
     intLib.COOPER_TAC)
 >~ [`Num (if i < 0 then i + 1 else i) < k`]
 >- (Cases_on `i < 0` >> gvs[] >> intLib.COOPER_TAC)
 >~ [`supported_word_type (BaseT (BytesT bd))`]
 >- (Cases_on `bd` >>
     gvs[supported_word_type_def, evaluate_type_def, value_has_type_def,
         vyper_base_to_abi_type_def, has_type_def, valid_bytes_bound_def,
         dimword_def])
 >~ [`supported_string_type (BaseT (BytesT bd))`]
 >- (Cases_on `bd` >>
     gvs[supported_string_type_def, evaluate_type_def, value_has_type_def,
         vyper_base_to_abi_type_def, has_type_def, valid_bytes_bound_def,
         dimword_def])
 >> mp_tac (Q.ISPEC `word_of_bytes_be l : 160 word` w2n_lt)
 >> CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> simp[]
QED

Theorem deploy_supported_scalar_abi_reverse:
 !ty env tv v av.
 supported_scalar_type ty /\ evaluate_type env ty = SOME tv /\
 value_has_type tv v /\ val_wf tv v /\
 vyper_to_abi env ty v = SOME av ==>
 abi_to_vyper env ty av = SOME v
Proof
 Cases_on `ty` >>
 simp[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def] >>
 Cases_on `b` >>
 simp[supported_word_type_def, supported_string_type_def] >>
 rpt strip_tac >> Cases_on `v` >>
 gvs[evaluate_type_def, value_has_type_def, vyper_to_abi_base_def,
     abi_to_vyper_def, check_IntV_def, within_int_bound_def] 
 >~ [`(if b then 1 else 0) <= 1`] >- (Cases_on `b` >> simp[])
 >~ [`compatible_bound bd (LENGTH bs)`]
 >- (Cases_on `bd` >>
     gvs[supported_word_type_def, supported_string_type_def,
         evaluate_type_def, value_has_type_def, compatible_bound_def])
 >~ [`compatible_bound bd (LENGTH bs)`]
 >- (Cases_on `bd` >>
     gvs[supported_word_type_def, supported_string_type_def,
         evaluate_type_def, value_has_type_def, compatible_bound_def])
 >~ [`MAP (CHR o w2n) (MAP n2w_o_ORD s) = s`]
 >- (simp[MAP_MAP_o, combinTheory.o_DEF, vyperMiscTheory.n2w_o_ORD_def,
        stringTheory.CHR_ORD, stringTheory.ORD_BOUND, dimword_def])
 >> conj_tac
 >- (mp_tac (Q.ISPEC `word_of_bytes_be l : 160 word` w2n_lt) >>
     CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> simp[])
 >> rewrite_tac[byteTheory.word_of_bytes_be_def]
 >> irule word_bytes_roundtrip_proof
 >> CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV)
 >> simp[dividesTheory.divides_def]
QED
