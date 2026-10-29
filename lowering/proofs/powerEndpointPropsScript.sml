(* The literal negative minimum is a legal base, including at raw widths. *)
Theory powerEndpointProps
Ancestors
  powerSignedRunProps powerBoundProps powerRunProps exprLowering compileEnv
  venomExecSemantics venomState emitHelperProps words integer_word integer
  vyperValueOperation vyperValue arithmetic
Libs
  wordsLib

Theorem power_endpoint_search:
  limit <= m /\ 1 < m ==>
  largest_pow_exponent_search fuel m limit 1 = 1
Proof
  strip_tac >> Cases_on `fuel` >> simp[Once largest_pow_exponent_search_def] >>
  `m <= m ** 2` by simp[X_LE_X_EXP] >>
  `~(m ** 2 < limit)` by decide_tac >> simp[]
QED

Theorem power_endpoint_exponent:
  1 < bits ==> largest_pow_exponent (2 ** (bits - 1)) bits T = 1
Proof
  strip_tac >> simp[largest_pow_exponent_def] >>
  irule power_endpoint_search >> simp[]
QED

Theorem power_endpoint_in_bound:
  1 < bits ==>
  (within_int_bound (Signed bits) ((-&(2 ** (bits - 1))) ** n) <=> n <= 1)
Proof
  strip_tac >>
  `1 < 2 ** (bits - 1)` by simp[] >>
  mp_tac (Q.SPECL [`2 ** (bits - 1)`, `bits`, `T`, `n`] signed_power_in_bound) >>
  simp[] >> strip_tac >>
  Cases_on `n = 0` >- simp[] >> Cases_on `n = 1` >- simp[] >>
  `1 < n` by decide_tac >>
  `(2 ** (bits - 1)) ** 1 < (2 ** (bits - 1)) ** n` by simp[] >>
  fs[] >> decide_tac
QED

Theorem compile_safe_pow_endpoint_run:
  compile_safe_pow x y (BaseT (IntT bits)) (SOME (-&(2 ** (bits - 1)))) el
    st = (op,st') /\ 1 < bits /\ bits <= 256 /\ n < dimword (:256) /\
  eval_operand x ss = SOME (i2w (-&(2 ** (bits - 1)))) /\
  eval_operand y ss = SOME (n2w n) /\ fresh_vars_wrt st ss ==>
  (within_int_bound (Signed bits) ((-&(2 ** (bits - 1))) ** n) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
         eval_operand op ss' = SOME (i2w ((-&(2 ** (bits - 1))) ** n))) /\
  (~within_int_bound (Signed bits) ((-&(2 ** (bits - 1))) ** n) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >>
  `1 < 2 ** (bits - 1)` by simp[] >>
  qpat_x_assum `compile_safe_pow _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_safe_pow_def, type_bits_def, is_signed_type_def,
       power_endpoint_exponent] >> strip_tac >>
  drule_all power_upper_checked_run >>
  simp[power_endpoint_in_bound, word_exp_i2w, w2n_n2w,
       dimword_def, EVAL ``dimindex (:256)``] >> metis_tac[]
QED
