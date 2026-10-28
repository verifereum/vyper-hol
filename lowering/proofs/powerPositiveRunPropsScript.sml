(* All nonnegative integer exponents, for the two literal branches. *)
Theory powerPositiveRunProps
Ancestors
  powerTypedRunProps powerEndpointProps powerSignedExponentProps powerSmallProps
  powerSignedRunProps powerBoundProps powerRunProps
  exprLowering compileEnv emitHelperProps venomExecSemantics venomState
  words integer_word integer arithmetic vyperArith vyperValue vyperValueOperation
Libs
  wordsLib

Theorem compile_safe_pow_typed_exponent_run:
  compile_safe_pow x y (if signed then BaseT (IntT bits) else BaseT (UintT bits))
    NONE (SOME (&n)) st = (op,st') /\
  (if signed then 1 < bits else 0 < bits) /\ bits <= 256 /\
  within_int_bound (if signed then Signed bits else Unsigned bits) a /\
  n < dimword (:256) /\ eval_operand x ss = SOME (i2w a) /\
  eval_operand y ss = SOME (n2w n) /\ fresh_vars_wrt st ss ==>
  (within_int_bound (if signed then Signed bits else Unsigned bits) (a ** n) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
         eval_operand op ss' = SOME (i2w (a ** n))) /\
  (~within_int_bound (if signed then Signed bits else Unsigned bits) (a ** n) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >> Cases_on `n = 0 \/ n = 1`
  >- (`within_int_bound (if signed then Signed bits else Unsigned bits) (a ** n)` by
        (mp_tac (Q.INST [`n` |-> `n`, `a` |-> `a`, `bits` |-> `bits`,
                        `signed` |-> `signed`]
          powerTypedCounterexampleTheory.power_primitive_exponent_source_result) >>
         simp[evaluate_binop_def, bounded_int_op_def] >>
         Cases_on `n = 0` >> gvs[]) >>
      mp_tac (Q.INST [`ty` |-> `if signed then BaseT (IntT bits) else BaseT (UintT bits)`]
        compile_safe_pow_primitive_exponent_run) >>
      simp[type_bits_def, is_signed_type_def] >>
      (impl_tac >- (Cases_on `signed` >> gvs[type_bits_def, is_signed_type_def])) >> simp[]) >>
  `2 <= n` by decide_tac >> Cases_on `signed` >> gvs[]
  >- (irule compile_safe_pow_signed_exponent_run >>
      simp[dimword_def, EVAL ``dimindex (:256)``] >> metis_tac[]) >>
  `0 <= a` by fs[within_int_bound_def] >>
  `Num a < dimword (:256) /\ i2w a = (n2w (Num a) : bytes32)` by
    (mp_tac (Q.INST [`signed` |-> `F`, `e` |-> `a`] power_nonnegative_word_bound) >>
     simp[]) >>
  `?k. a = &k` by (irule NUM_POSINT_EXISTS >> simp[]) >> gvs[] >>
  mp_tac (Q.INST [`ty` |-> `BaseT (UintT bits)`, `a` |-> `k`]
    compile_safe_pow_unsigned_exponent_run) >>
  simp[type_bits_def, is_signed_type_def, within_int_bound_def, INT_EXP, i2w_pos,
       dimword_def, EVAL ``dimindex (:256)``] >>
  (impl_tac >- gvs[within_int_bound_def, i2w_pos, dimword_def,
                   EVAL ``dimindex (:256)``]) >> simp[]
QED

Theorem compile_safe_pow_typed_base_run:
  compile_safe_pow x y (if signed then BaseT (IntT bits) else BaseT (UintT bits))
    (SOME a) el st = (op,st') /\
  (if signed then 1 < bits else 0 < bits) /\ bits <= 256 /\
  within_int_bound (if signed then Signed bits else Unsigned bits) a /\
  within_int_bound (if signed then Signed bits else Unsigned bits) (&n) /\
  n < dimword (:256) /\ eval_operand x ss = SOME (i2w a) /\
  eval_operand y ss = SOME (n2w n) /\ fresh_vars_wrt st ss ==>
  (within_int_bound (if signed then Signed bits else Unsigned bits) (a ** n) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
         eval_operand op ss' = SOME (i2w (a ** n))) /\
  (~within_int_bound (if signed then Signed bits else Unsigned bits) (a ** n) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >> Cases_on `a = -1 \/ a = 0 \/ a = 1`
  >- (`within_int_bound (if signed then Signed bits else Unsigned bits) (a ** n)` by
        (irule power_small_in_bound >> metis_tac[]) >>
      `eval_operand y ss = SOME (i2w (&n))` by simp[i2w_pos] >>
      mp_tac (Q.INST [`ty` |-> `if signed then BaseT (IntT bits) else BaseT (UintT bits)`,
                     `e` |-> `&n`] compile_safe_pow_small_base_run) >>
      simp[type_bits_def, is_signed_type_def] >>
      impl_tac >- (Cases_on `signed` >> gvs[type_bits_def, is_signed_type_def] >>
                   irule power_signed_256_bound >> metis_tac[]) >> simp[]) >>
  Cases_on `signed` >> gvs[]
  >- (qspecl_then [`a`] strip_assume_tac INT_NUM_CASES >> gvs[] >>
      rename1 `m <> 0` >>
      FIRST [
        irule (SIMP_RULE (srw_ss()) []
          (Q.INST [`negative` |-> `T`] compile_safe_pow_signed_magnitude_run)),
        irule (SIMP_RULE (srw_ss()) []
          (Q.INST [`negative` |-> `F`] compile_safe_pow_signed_magnitude_run))] >>
      simp[dimword_def, EVAL ``dimindex (:256)``] >> metis_tac[]) >>
  `0 <= a` by fs[within_int_bound_def] >>
  `?k. a = &k` by (irule NUM_POSINT_EXISTS >> simp[]) >> gvs[] >>
  mp_tac (Q.INST [`ty` |-> `BaseT (UintT bits)`, `a` |-> `k`]
    compile_safe_pow_unsigned_base_run) >>
  simp[type_bits_def, is_signed_type_def, within_int_bound_def, INT_EXP, i2w_pos,
       dimword_def, EVAL ``dimindex (:256)``] >>
  impl_tac >- (fs[within_int_bound_def, i2w_pos] >>
              qexistsl_tac [`k`, `el`, `x`, `y`] >> simp[] >> decide_tac) >> simp[]
QED
