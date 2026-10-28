(* Run interface for typed integer powers; literal/value correspondence is
   internal here and is derived from checked AST evaluation by the caller. *)
Theory powerTypedRunProps
Ancestors
  powerEndpointProps powerSignedExponentProps powerSmallProps
  powerSignedRunProps powerBoundProps powerRunProps
  exprLowering compileEnv emitHelperProps venomExecSemantics venomState
  words integer_word integer arithmetic vyperArith vyperValue vyperValueOperation
Libs
  wordsLib

Theorem power_nonnegative_word_bound:
  within_int_bound (if signed then Signed bits else Unsigned bits) e /\
  bits <= 256 /\ 0 <= e ==>
  Num e < dimword (:256) /\ i2w e = (n2w (Num e) : bytes32)
Proof
  strip_tac >>
  `e = &Num e` by (ONCE_REWRITE_TAC[EQ_SYM_EQ] >> simp[]) >>
  pop_assum SUBST_ALL_TAC >> simp[i2w_pos] >>
  `Num e < 2 ** bits` by
    (Cases_on `signed` >> fs[within_int_bound_def] >>
     Cases_on `0 < bits` >> gvs[] >>
     `2 ** (bits - 1) <= 2 ** bits` by simp[] >> decide_tac) >>
  irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** bits` >>
  simp[dimword_def, EVAL ``dimindex (:256)``]
QED

Theorem power_signed_256_bound:
  within_int_bound (Signed bits) e /\ bits <= 256 ==>
  within_int_bound (Signed 256) e
Proof
  strip_tac >> fs[within_int_bound_def] >>
  IF_CASES_TAC >> fs[] >> Cases_on `0 < bits` >> gvs[] >>
  FIRST [irule LESS_EQ_TRANS, irule LESS_LESS_EQ_TRANS] >>
  qexists_tac `2 ** (bits - 1)` >> simp[]
QED

Theorem compile_safe_pow_signed_magnitude_run:
  compile_safe_pow x y (BaseT (IntT bits))
    (SOME (if negative then -&m else &m)) el st = (op,st') /\
  2 <= m /\ 1 < bits /\ bits <= 256 /\ n < dimword (:256) /\
  within_int_bound (Signed bits) (if negative then -&m else &m) /\
  eval_operand x ss = SOME (i2w (if negative then -&m else &m)) /\
  eval_operand y ss = SOME (n2w n) /\ fresh_vars_wrt st ss ==>
  (within_int_bound (Signed bits) ((if negative then -&m else &m) ** n) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
         eval_operand op ss' = SOME (i2w ((if negative then -&m else &m) ** n))) /\
  (~within_int_bound (Signed bits) ((if negative then -&m else &m) ** n) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >> Cases_on `m < 2 ** (bits - 1)`
  >- (irule compile_safe_pow_signed_base_run >> metis_tac[]) >>
  `negative /\ m = 2 ** (bits - 1)` by
    (Cases_on `negative` >> gvs[within_int_bound_def] >> decide_tac) >>
  gvs[] >> irule compile_safe_pow_endpoint_run >>
  simp[dimword_def, EVAL ``dimindex (:256)``] >> metis_tac[]
QED

Theorem compile_safe_pow_negative_run:
  compile_safe_pow x y (BaseT (IntT bits)) (SOME a) el st = (op,st') /\
  1 < bits /\ bits <= 256 /\ within_int_bound (Signed bits) a /\
  within_int_bound (Signed bits) e /\ e < 0 /\
  eval_operand x ss = SOME (i2w a) /\ eval_operand y ss = SOME (i2w e) /\
  fresh_vars_wrt st ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  strip_tac >>
  `within_int_bound (Signed 256) e` by (irule power_signed_256_bound >> metis_tac[]) >>
  `Num e < dimword (:256)` by
    (`Num e <= 2 ** 255` by gvs[within_int_bound_def, Num_neg] >>
     irule LESS_EQ_LESS_TRANS >> qexists_tac `2 ** 255` >>
     simp[dimword_def, EVAL ``dimindex (:256)``]) >>
  Cases_on `a = -1 \/ a = 0 \/ a = 1`
  >- (mp_tac (Q.INST [`ty` |-> `BaseT (IntT bits)`]
        compile_safe_pow_small_base_run) >>
      simp[type_bits_def, is_signed_type_def] >>
      disch_then drule_all >> simp[]) >>
  qabbrev_tac `m = Num (ABS a)` >>
  `2 <= m` by
    (simp[Abbr `m`] >>
     qspecl_then [`a`] strip_assume_tac INT_NUM_CASES >> gvs[] >> decide_tac) >>
  qabbrev_tac `upper0 = largest_pow_exponent m bits T` >>
  qabbrev_tac `upper = if a < 0 /\ ODD (upper0 + 1) /\
    m ** (upper0 + 1) = 2 ** (bits - 1) then upper0 + 1 else upper0` >>
  `m <= 2 ** (bits - 1)` by
    (simp[Abbr `m`] >> fs[within_int_bound_def] >>
     Cases_on `a < 0` >> fs[INT_ABS]) >>
  `upper0 <= bits - 1` by
    (Cases_on `m = 2 ** (bits - 1)`
     >- simp[Abbr `upper0`, power_endpoint_exponent] >>
     mp_tac (Q.SPECL [`m`,`bits`,`T`] largest_pow_exponent_lt_bits) >>
     simp[Abbr `upper0`]) >>
  `upper < words$INT_MIN (:256) /\ upper < dimword (:256)` by
    (simp[Abbr `upper`, wordsTheory.INT_MIN_def, dimword_def,
          EVAL ``dimindex (:256)``] >> IF_CASES_TAC >> simp[] >> decide_tac) >>
  `integer_word$INT_MIN (:256) <= e` by
    (gvs[within_int_bound_def, integer_wordTheory.INT_MIN_def,
        wordsTheory.INT_MIN_def, EVAL ``dimindex (:256)``] >>
     `e = -&Num (-e)` by (simp[] >> intLib.COOPER_TAC) >>
     pop_assum SUBST_ALL_TAC >> gvs[]) >>
  `upper < w2n (i2w e : bytes32)` by
    (irule power_negative_exponent_above >> simp[]) >>
  qunabbrev_tac `upper` >> qunabbrev_tac `upper0` >> qunabbrev_tac `m` >>
  qpat_x_assum `compile_safe_pow _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_safe_pow_def, type_bits_def, is_signed_type_def] >> strip_tac >>
  drule_all power_upper_checked_run >>
  fs[w2n_n2w] >> simp[]
QED
