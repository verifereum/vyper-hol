Theory bodyPtrBopInEncoding
Ancestors exprSimCompare valueEncoding vyperTyping arithmeticProps words
  compileEnv vyperValue arithmetic vyperArith
  integer_word

Theorem membership_typed_word_encoding_reflects:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ value_has_type tv w /\
  (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
       m <= 256) /\
  (!m. tv = BaseTV (IntT m) ==> 0 < m) /\
  (!m. tv = BaseTV (BytesT (Fixed m)) ==> m <= 32) ==>
  (typed_val_to_w256 tv v = typed_val_to_w256 tv w <=> v = w)
Proof
  strip_tac >> Cases_on `ty` >> gvs[is_word_type_def]
  >~ [`evaluate_type tenv (FlagT _) = SOME tv`]
  >- (gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `v` >> Cases_on `w` >> gvs[value_has_type_def] >>
      `2 ** m <= 2 ** 256` by simp[] >>
      `n < 2 ** 256 /\ n' < 2 ** 256` by decide_tac >>
      gvs[typed_val_to_w256_def, val_to_w256_def, n2w_11,
          dimword_def, LESS_MOD]) >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_word_type_def]
  >~ [`BaseT (BytesT bd)`]
  >- (Cases_on `bd` >> gvs[is_word_type_def, evaluate_type_def] >>
      Cases_on `v` >> Cases_on `w` >> gvs[value_has_type_def] >>
      irule typed_val_to_w256_bytes_11 >> simp[value_has_type_def]) >>
  gvs[evaluate_type_def] >>
  Cases_on `v` >> Cases_on `w` >> gvs[value_has_type_def]
  >~ [`BaseTV AddressT`]
  >- (irule typed_val_to_w256_bytes_11 >> simp[value_has_type_def])
  >~ [`BaseTV BoolT`]
  >- (Cases_on `b` >> Cases_on `b'` >>
      simp[typed_val_to_w256_def, val_to_w256_def])
  >~ [`BaseTV (UintT n)`] >- suspend "uint"
  >~ [`BaseTV (IntT n)`] >- suspend "sint"
  >> suspend "decimal"
QED

Resume membership_typed_word_encoding_reflects[uint]:
  `2 ** n <= 2 ** 256` by simp[] >>
  `Num i < 2 ** 256 /\ Num i' < 2 ** 256` by decide_tac >>
  `~(i < 0) /\ ~(i' < 0)` by intLib.ARITH_TAC >>
  gvs[typed_val_to_w256_def, val_to_w256_def, i2w_def, n2w_11,
      dimword_def, LESS_MOD] >> intLib.ARITH_TAC
QED

Resume membership_typed_word_encoding_reflects[sint]:
  `w2i (i2w i : bytes32) = i` by
    (irule w2i_i2w_within_signed >> qexists_tac `n` >> simp[]) >>
  `w2i (i2w i' : bytes32) = i'` by
    (irule w2i_i2w_within_signed >> qexists_tac `n` >> simp[]) >>
  simp[typed_val_to_w256_def, val_to_w256_def] >> metis_tac[]
QED

Resume membership_typed_word_encoding_reflects[decimal]:
  `w2i (i2w i : bytes32) = i` by
    (irule w2i_i2w_within_signed >> qexists_tac `168` >> simp[]) >>
  `w2i (i2w i' : bytes32) = i'` by
    (irule w2i_i2w_within_signed >> qexists_tac `168` >> simp[]) >>
  simp[typed_val_to_w256_def, val_to_w256_def] >> metis_tac[]
QED

Finalise membership_typed_word_encoding_reflects
