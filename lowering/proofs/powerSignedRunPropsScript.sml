(* Signed literal-base powers of magnitude >= 2 and below the endpoint:
   exact overflow bound, emitted execution, and actual compile_binop blocks.
   Includes the word-order fact for negative runtime exponent rejection. *)
Theory powerSignedRunProps
Ancestors
  powerBoundProps powerRunProps powerBlockProps exprLowering exprLoweringProps compileEnv
  emitHelper emitHelperProps venomExecSemantics venomState venomInst
  words integer_word integer arithmetic vyperValueOperation vyperValue list
Libs
  wordsLib

Theorem compile_safe_pow_signed_base_run:
  compile_safe_pow x y (BaseT (IntT bits))
    (SOME (if negative then -&m else &m)) el st = (op, st') /\
  2 <= m /\ m < 2 ** (bits - 1) /\ 1 < bits /\ bits <= 256 /\
  n < dimword (:256) /\
  eval_operand x ss = SOME (i2w (if negative then -&m else &m)) /\
  eval_operand y ss = SOME (n2w n) /\ fresh_vars_wrt st ss ==>
  (within_int_bound (Signed bits) ((if negative then -&m else &m) ** n) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
         eval_operand op ss' = SOME (i2w ((if negative then -&m else &m) ** n))) /\
  (~within_int_bound (Signed bits) ((if negative then -&m else &m) ** n) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >>
  qabbrev_tac `upper0 = largest_pow_exponent m bits T` >>
  qabbrev_tac `upper = if negative /\ ODD (upper0 + 1) /\
    m ** (upper0 + 1) = 2 ** (bits - 1) then upper0 + 1 else upper0` >>
  `upper0 < bits - 1` by
    (mp_tac (Q.SPECL [`m`, `bits`, `T`] largest_pow_exponent_lt_bits) >>
     simp[Abbr `upper0`]) >>
  `upper < dimword (:256)` by
    (simp[Abbr `upper`, dimword_def, EVAL ``dimindex (:256)``] >>
     IF_CASES_TAC >> simp[] >> decide_tac) >>
  `within_int_bound (Signed bits) ((if negative then -&m else &m) ** n) <=>
   n <= upper` by
    (mp_tac (Q.SPECL [`m`, `bits`, `negative`, `n`]
      largest_signed_pow_exponent_in_bound) >>
     simp[Abbr `upper`, Abbr `upper0`]) >>
  `word_exp (i2w (if negative then -&m else &m) : bytes32) (n2w n) =
     i2w ((if negative then -&m else &m) ** n)` by simp[word_exp_i2w] >>
  qpat_x_assum `compile_safe_pow _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `negative` >>
  simp[compile_safe_pow_def, type_bits_def, is_signed_type_def,
       Abbr `upper`, Abbr `upper0`] >> strip_tac >>
  drule_all power_upper_checked_run >>
  fs[w2n_n2w, dimword_def, EVAL ``dimindex (:256)``] >>
  simp[GSYM NOT_LESS_EQUAL]
QED

Theorem compile_safe_pow_signed_base_correct:
  compile_safe_pow x y (BaseT (IntT bits))
    (SOME (if negative then -&m else &m)) el st = (op, st') /\
  2 <= m /\ m < 2 ** (bits - 1) /\ 1 < bits /\ bits <= 256 /\
  n < dimword (:256) /\
  eval_operand x ss = SOME (i2w (if negative then -&m else &m)) /\
  eval_operand y ss = SOME (n2w n) /\ fresh_vars_wrt st ss ==>
  (?r ss'. evaluate_binop (Signed bits) tv Exp
              (IntV (if negative then -&m else &m)) (IntV (&n)) = INL (IntV r) /\
            run_inst_seq (emitted_insts st st') ss = OK ss' /\
            eval_operand op ss' = SOME (i2w r)) \/
  (?msg ss'. evaluate_binop (Signed bits) tv Exp
              (IntV (if negative then -&m else &m)) (IntV (&n)) =
                INR (RuntimeError msg) /\
            run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >> drule_all compile_safe_pow_signed_base_run >> strip_tac >>
  Cases_on `within_int_bound (Signed bits) ((if negative then -&m else &m) ** n)` >>
  fs[evaluate_binop_def, bounded_int_op_def] >> metis_tac[]
QED

(* Signed negative values occupy the upper half of the unsigned word space,
   so the unsigned GT guard rejects them as well as positive overflow. *)
Theorem power_negative_exponent_above:
  INT_MIN (:256) <= e /\ e < 0 /\ upper < INT_MIN (:256) ==>
  upper < w2n (i2w e : bytes32)
Proof
  strip_tac >>
  `e <= INT_MAX (:256)` by (simp[INT_MAX_def] >> intLib.COOPER_TAC) >>
  `word_msb (i2w e : bytes32)` by simp[word_msb_i2w_lt_0] >>
  `w2n (i2w e : bytes32) < 2 ** 256` by
    (mp_tac (Q.ISPEC `i2w e : bytes32` w2n_lt) >>
     simp[dimword_def, EVAL ``dimindex (:256)``]) >>
  mp_tac (Q.INST [`n` |-> `w2n (i2w e : bytes32)`]
    (INST_TYPE [alpha |-> ``:256``] word_msb_n2w_numeric)) >>
  simp[] >> fs[wordsTheory.INT_MIN_def, EVAL ``dimindex (:256)``] >> decide_tac
QED

Theorem compile_safe_pow_signed_base_instructions:
  compile_safe_pow x y (BaseT (IntT bits))
    (SOME (if negative then -&m else &m)) el st = (op, st') /\ 2 <= m ==>
  st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> PHI) (emitted_insts st st')
Proof
  strip_tac >> Cases_on `negative` >>
  gvs[compile_safe_pow_def, type_bits_def, is_signed_type_def] >>
  drule power_upper_checked_instructions >> simp[]
QED

Theorem compile_binop_signed_base_block:
  compile_binop Exp x y (BaseT (IntT bits))
    (SOME (if negative then -&m else &m)) el st = (op, st') /\
  2 <= m /\ m < 2 ** (bits - 1) /\ 1 < bits /\ bits <= 256 /\
  n < dimword (:256) /\
  eval_operand x ss = SOME (i2w (if negative then -&m else &m)) /\
  eval_operand y ss = SOME (n2w n) /\ fresh_vars_wrt st ss /\ ~ss.vs_halted /\
  st.cs_current_insts = [] /\
  bb.bb_instructions = st'.cs_current_insts ++ [mk_inst id JMP [Label target] []] ==>
  evaluate_binop (Signed bits) tv Exp
    (IntV (if negative then -&m else &m)) (IntV (&n)) =
      (if within_int_bound (Signed bits) ((if negative then -&m else &m) ** n)
       then INL (IntV ((if negative then -&m else &m) ** n))
       else INR (RuntimeError "bounded_int_op bound")) /\
  (within_int_bound (Signed bits) ((if negative then -&m else &m) ** n) ==>
   ?ss'. run_block fuel ctx bb ss = OK ss' /\
         eval_operand op ss' = SOME (i2w ((if negative then -&m else &m) ** n))) /\
  (~within_int_bound (Signed bits) ((if negative then -&m else &m) ** n) ==>
   ?ss'. run_block fuel ctx bb ss = Abort Revert_abort ss')
Proof
  strip_tac >>
  `compile_safe_pow x y (BaseT (IntT bits))
    (SOME (if negative then -&m else &m)) el st = (op, st')`
    by fs[compile_binop_def] >>
  drule_all compile_safe_pow_signed_base_instructions >> strip_tac >>
  drule_all compile_safe_pow_signed_base_run >> strip_tac >>
  `bb.bb_instructions = emitted_insts st st' ++ [mk_inst id JMP [Label target] []]`
    by gvs[] >>
  simp[evaluate_binop_def, bounded_int_op_def] >> conj_tac >> strip_tac
  >- (first_x_assum drule >>
      disch_then (qx_choose_then `sout` strip_assume_tac) >>
      drule_all power_block_result >> simp[]) >>
  first_x_assum drule >>
  disch_then (qx_choose_then `sout` strip_assume_tac) >>
  drule_all power_run_block_abort >> metis_tac[]
QED

Theorem compile_binop_signed_base_negative_block:
  compile_binop Exp x y (BaseT (IntT bits))
    (SOME (if negative then -&m else &m)) el st = (op, st') /\
  2 <= m /\ m < 2 ** (bits - 1) /\ 1 < bits /\ bits <= 256 /\
  integer_word$INT_MIN (:256) <= e /\ e < 0 /\
  eval_operand x ss = SOME (i2w (if negative then -&m else &m)) /\
  eval_operand y ss = SOME (i2w e) /\ fresh_vars_wrt st ss /\ ~ss.vs_halted /\
  st.cs_current_insts = [] /\
  bb.bb_instructions = st'.cs_current_insts ++ [mk_inst id JMP [Label target] []] ==>
  evaluate_binop (Signed bits) tv Exp
    (IntV (if negative then -&m else &m)) (IntV e) = INR (RuntimeError "Exp~") /\
  ?ss'. run_block fuel ctx bb ss = Abort Revert_abort ss'
Proof
  strip_tac >> simp[evaluate_binop_def] >>
  qabbrev_tac `upper0 = largest_pow_exponent m bits T` >>
  qabbrev_tac `upper = if negative /\ ODD (upper0 + 1) /\
    m ** (upper0 + 1) = 2 ** (bits - 1) then upper0 + 1 else upper0` >>
  `upper0 < bits - 1` by
    (mp_tac (Q.SPECL [`m`, `bits`, `T`] largest_pow_exponent_lt_bits) >>
     simp[Abbr `upper0`]) >>
  `upper < words$INT_MIN (:256) /\ upper < dimword (:256)` by
    (simp[Abbr `upper`, wordsTheory.INT_MIN_def, dimword_def,
          EVAL ``dimindex (:256)``] >> IF_CASES_TAC >> simp[] >> decide_tac) >>
  `upper < w2n (i2w e : bytes32)` by
    (irule power_negative_exponent_above >> simp[]) >>
  qpat_x_assum `compile_binop _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `negative` >>
  simp[compile_binop_def, compile_safe_pow_def, type_bits_def, is_signed_type_def,
       Abbr `upper`, Abbr `upper0`] >> strip_tac >>
  drule_all power_upper_checked_block >>
  fs[w2n_n2w, dimword_def, EVAL ``dimindex (:256)``] >> metis_tac[]
QED
