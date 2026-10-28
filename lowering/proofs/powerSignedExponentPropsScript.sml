(* Exact signed literal-exponent bounds, including the asymmetric endpoint. *)
Theory powerSignedExponentProps
Ancestors
  powerGuardProps powerBoundProps powerRunProps exprLowering compileEnv
  emitHelperProps venomExecSemantics venomState words integer_word integer
  vyperValueOperation vyperValue vyperArith valueEncoding arithmetic
Libs
  wordsLib

Theorem power_signed_interval:
  0 < n /\ 0 < bits ==>
  let upper = largest_pow_base n bits T;
      lower = if ODD n /\ (upper + 1) ** n = 2 ** (bits - 1)
              then -&(upper + 1) else -&upper in
  (within_int_bound (Signed bits) (a ** n) <=> lower <= a /\ a <= &upper)
Proof
  strip_tac >> simp[] >>
  STRUCT_CASES_TAC (Q.SPEC `a` INT_NUM_CASES) >| [
    rename1 `m <> 0` >>
    mp_tac (Q.SPECL [`n`, `bits`, `F`, `m`] largest_signed_pow_base_in_bound) >>
    simp[within_int_bound_def, INT_EXP] >> IF_CASES_TAC >> simp[],
    rename1 `m <> 0` >>
    mp_tac (Q.SPECL [`n`, `bits`, `T`, `m`] largest_signed_pow_base_in_bound) >>
    simp[] >> IF_CASES_TAC >> simp[],
    simp[within_int_bound_def, INT_EXP, ZERO_EXP] >> IF_CASES_TAC >> simp[]]

QED

Theorem power_signed_interval_bounds:
  0 < n /\ 0 < bits ==>
  let upper = largest_pow_base n bits T;
      lower = if ODD n /\ (upper + 1) ** n = 2 ** (bits - 1)
              then -&(upper + 1) else -&upper in
  within_int_bound (Signed bits) lower /\ within_int_bound (Signed bits) (&upper)
Proof
  strip_tac >>
  `largest_pow_base n bits T < 2 ** (bits - 1)` by
    (mp_tac (Q.SPECL [`n`, `bits`, `T`] largest_pow_base_lt_limit) >> simp[]) >>
  Cases_on `ODD n /\ (largest_pow_base n bits T + 1) ** n = 2 ** (bits - 1)` >>
  simp[within_int_bound_def] >> decide_tac
QED

Theorem power_signed_word_comparisons:
  within_int_bound (Signed bits) a /\ within_int_bound (Signed bits) lo /\
  within_int_bound (Signed bits) hi /\ bits <= 256 ==>
  (((i2w a : bytes32) < i2w lo) <=> a < lo) /\
  (((i2w a : bytes32) > i2w hi) <=> a > hi)
Proof
  strip_tac >>
  `w2i (i2w a : bytes32) = a /\ w2i (i2w lo : bytes32) = lo /\
   w2i (i2w hi : bytes32) = hi` by
    (rpt conj_tac >> irule w2i_i2w_within_signed >> metis_tac[]) >>
  simp[WORD_LTi, WORD_GTi]
QED

Theorem compile_safe_pow_signed_exponent_run:
  compile_safe_pow x y (BaseT (IntT bits)) NONE (SOME (&n)) st = (op,st') /\
  1 < bits /\ bits <= 256 /\ 2 <= n /\ n < dimword (:256) /\
  within_int_bound (Signed bits) a /\
  eval_operand x ss = SOME (i2w a) /\ eval_operand y ss = SOME (n2w n) /\
  fresh_vars_wrt st ss ==>
  (within_int_bound (Signed bits) (a ** n) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
         eval_operand op ss' = SOME (i2w (a ** n))) /\
  (~within_int_bound (Signed bits) (a ** n) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >>
  qabbrev_tac `upper = largest_pow_base n bits T` >>
  qabbrev_tac `lower : int = if ODD n /\ (upper + 1) ** n = 2 ** (bits - 1)
                      then -&(upper + 1) else -&upper` >>
  `within_int_bound (Signed bits) lower /\ within_int_bound (Signed bits) (&upper)`
    by (mp_tac (Q.INST [`n` |-> `n`, `bits` |-> `bits`] power_signed_interval_bounds) >>
        simp[Abbr `lower`, Abbr `upper`]) >>
  `within_int_bound (Signed bits) (a ** n) <=> lower <= a /\ a <= &upper`
    by (mp_tac (Q.INST [`n` |-> `n`, `bits` |-> `bits`, `a` |-> `a`]
          power_signed_interval) >> simp[Abbr `lower`, Abbr `upper`]) >>
  mp_tac (Q.INST [`a` |-> `a`, `lo` |-> `lower`, `hi` |-> `&upper`,
                   `bits` |-> `bits`] power_signed_word_comparisons) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qunabbrev_tac `lower` >> qunabbrev_tac `upper` >>
  qpat_x_assum `compile_safe_pow _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_safe_pow_def, type_bits_def, is_signed_type_def, GSYM i2w_pos] >>
  strip_tac >> drule_all power_signed_range_run >>
  simp[word_exp_i2w, INT_NOT_LE, INT_NOT_LT, INT_GT] >> metis_tac[]
QED
