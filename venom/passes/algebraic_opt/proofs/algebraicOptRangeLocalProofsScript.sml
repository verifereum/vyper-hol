Theory algebraicOptRangeLocalProofs
Ancestors
  algebraicOptDefs venomExecSemantics intBits vyperValueOperation
  passSimulationDefs dfgAnalysisProps

Theorem ao_range_comparison_bounds:
  !r w signed. ao_range_valid_for_cmp r signed /\ in_range r w ==>
    vr_lo r <= ao_wrap_lit w signed /\ ao_wrap_lit w signed <= vr_hi r
Proof
  Cases_on `r` >> Cases_on `signed` >>
  simp[ao_range_valid_for_cmp_def, valueRangeDefsTheory.in_range_def,
       valueRangeDefsTheory.vr_is_top_def, valueRangeDefsTheory.vr_lo_def,
       valueRangeDefsTheory.vr_hi_def, ao_wrap_lit_def] >>
  rpt strip_tac >>
  `0 <= w2i w` by Cooper.COOPER_TAC >>
  `~word_msb w` by
    (metis_tac[integer_wordTheory.w2i_lt_0, wordsTheory.word_msb_neg,
               integerTheory.INT_NOT_LT]) >>
  gvs[integer_wordTheory.w2i_def]
QED

Theorem ao_opt_cmp_range_value:
  !ra lbl idx inst gt signed op a b x y s.
    inst.inst_operands = [a;b] /\
    eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
    (~is_lit_op a ==> in_range (range_get_range ra lbl idx a) x) /\
    (~is_lit_op b ==> in_range (range_get_range ra lbl idx b) y) /\
    ao_opt_cmp_range ra lbl idx inst gt signed = SOME op ==>
    eval_operand op s = SOME
      (if (if gt then ao_wrap_lit x signed > ao_wrap_lit y signed
           else ao_wrap_lit x signed < ao_wrap_lit y signed)
       then 1w else 0w)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[ao_opt_cmp_range_def, passSharedDefsTheory.is_lit_op_def,
      venomStateTheory.eval_operand_def,
      AllCaseEqs()] >>
  drule_all ao_range_comparison_bounds >> strip_tac >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  Cooper.COOPER_TAC
QED

Theorem word_i2w_neg[local]:
  -(i2w b : 'a word) = i2w (-b)
Proof
  `i2w (-b) + i2w b = 0w : 'a word` by (
    rewrite_tac[integer_wordTheory.word_i2w_add] >>
    `(-b + b : int) = 0` by Cooper.COOPER_TAC >>
    pop_assum (fn th => rewrite_tac[th]) >>
    simp[integer_wordTheory.i2w_def]) >>
  fs[wordsTheory.WORD_SUM_ZERO]
QED

Theorem word_i2w_sub[local]:
  i2w a - i2w b = i2w (a - b) : 'a word
Proof
  rewrite_tac[wordsTheory.word_sub_def, integerTheory.int_sub] >>
  rewrite_tac[GSYM integer_wordTheory.word_i2w_add, word_i2w_neg]
QED

Theorem i2w_signed_int_mod_sign_extend[local]:
  !j x. j <= 30 ==>
        (integer_word$i2w (signed_int_mod (8 * (j + 1)) x) : bytes32) =
        sign_extend (n2w j) (integer_word$i2w x)
Proof
  rpt strip_tac >>
  `fcp$dimindex (:256) = 256` by simp[fcpLib.INDEX_CONV ``fcp$dimindex(:256)``] >>
  `w2n (n2w j : bytes32) = j` by simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  simp[sign_extend_def, signed_int_mod_def] >>
  qabbrev_tac `b = 8 * (j + 1)` >>
  `0 < b /\ b < 256 /\ 8 * j + 7 = b - 1 /\ 8 * j + 8 = b` by
    simp[Abbr `b`] >>
  asm_rewrite_tac[] >>
  `(1w:bytes32) << b - 1w = n2w (2 ** b - 1)` by
    (`(1w:bytes32) << b = n2w (2 ** b)` by simp[wordsTheory.word_lsl_n2w] >>
     simp[wordsTheory.n2w_sub]) >>
  `(integer_word$i2w x >>> (b - 1) && 1w = (1w:bytes32)) <=>
   (integer_word$i2w x : bytes32) ' (b - 1)` by
    (irule lsr_and_1 >> simp[]) >>
  asm_rewrite_tac[] >>
  `(integer_word$i2w (x % &(2 ** b)) : bytes32) =
   integer_word$i2w x && n2w (2 ** b - 1)` by
    (irule i2w_mod_pow2 >> simp[]) >>
  `0 <= x % &(2 ** b) /\ x % &(2 ** b) < &(2 ** b)` by
    (mp_tac (Q.SPECL [`x`, `&(2 ** b)`] integerTheory.INT_MOD_BOUNDS) >> simp[]) >>
  qabbrev_tac `rm = x % &(2 ** b)` >>
  `?tn. rm = &tn` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >>
  `tn < 2 ** b` by fs[] >>
  qpat_x_assum `integer_word$i2w rm = _` mp_tac >>
  asm_rewrite_tac[integer_wordTheory.i2w_pos] >> strip_tac >>
  `(integer_word$i2w x : bytes32) ' (b - 1) =
   (integer_word$i2w x && n2w (2 ** b - 1) : bytes32) ' (b - 1)` by
    simp[wordsTheory.word_and_def, fcpTheory.FCP_BETA,
         wordsTheory.word_index, bitTheory.BIT_EXP_SUB1] >>
  `(n2w tn : bytes32) ' (b - 1) <=> 2 ** (b - 1) <= tn` by
    (simp[wordsTheory.word_index] >> irule bit_top >> simp[]) >>
  `(integer_word$i2w x : bytes32) ' (b - 1) <=> 2 ** (b - 1) <= tn` by
    (qpat_x_assum `integer_word$i2w x ' _ <=> (_ && _) ' _` SUBST1_TAC >>
     qpat_x_assum `n2w tn = _` (SUBST1_TAC o SYM) >> asm_rewrite_tac[]) >>
  `&tn >= (&(2 ** (b - 1)) : int) <=> 2 ** (b - 1) <= tn` by
    simp[integerTheory.INT_GE, integerTheory.INT_LE] >>
  qpat_assum `&tn >= _ <=> _` (fn th1 =>
    qpat_assum `integer_word$i2w x ' _ <=> 2 ** _ <= tn` (fn th2 =>
      ONCE_REWRITE_TAC [th1, th2])) >>
  Cases_on `2 ** (b - 1) <= tn` >> pure_asm_rewrite_tac[COND_CLAUSES]
  >- (REWRITE_TAC[GSYM word_i2w_sub, integer_wordTheory.i2w_pos] >>
      qpat_x_assum `n2w tn = _` SUBST1_TAC >> irule neg_mask >> simp[]) >>
  REWRITE_TAC[integer_wordTheory.i2w_pos] >>
  qpat_x_assum `n2w tn = _` ACCEPT_TAC
QED

Theorem ao_sign_extend_within:
  !n x. n < 31 /\
    -&(2 ** (8 * (n + 1) - 1)) <= w2i x /\
    w2i x < &(2 ** (8 * (n + 1) - 1)) ==>
    sign_extend (n2w n) x = x
Proof
  rpt strip_tac >>
  qabbrev_tac `m = 8 * (n + 1)` >>
  `0 < m` by simp[Abbr `m`] >>
  `2n ** m = 2n * 2n ** (m - 1)` by
    (`m = SUC (m - 1)` by simp[] >> pop_assum SUBST1_TAC >> simp[arithmeticTheory.EXP]) >>
  `&(2n ** m) = 2 * &(2n ** (m - 1)) : int` by
    asm_rewrite_tac[GSYM integerTheory.INT_MUL] >>
  qpat_x_assum `2n ** m = _` kall_tac >>
  `0 < &(2 ** (m - 1)) : int` by simp[] >>
  qabbrev_tac `H = &(2 ** (m - 1)) : int` >>
  `signed_int_mod m (w2i x) = w2i x` by
    (simp[vyperValueOperationTheory.signed_int_mod_def] >>
     Cases_on `0 <= w2i x`
     >- (`w2i x % (2 * H) = w2i x` by
           (irule integerTheory.INT_LESS_MOD >> Omega.OMEGA_TAC) >>
         rw[] >> Omega.OMEGA_TAC) >>
     `w2i x % (2 * H) = w2i x + 2 * H` by
       (irule integerTheory.INT_MOD_UNIQUE >> qexists `-1` >>
        rw[] >> Omega.OMEGA_TAC) >>
     rw[] >> Omega.OMEGA_TAC) >>
  qspecl_then [`n`, `w2i x`] mp_tac i2w_signed_int_mod_sign_extend >>
  simp[Abbr `m`, integer_wordTheory.i2w_w2i]
QED

Theorem ao_sign_extend_large:
  !n x. 31w <=+ n ==> sign_extend n x = x
Proof
  simp[wordsTheory.WORD_LS, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``fcp$dimindex(:256)``, sign_extend_def] >>
  rpt strip_tac >>
  `30 < w2n n` by decide_tac >> simp[]
QED

Theorem ao_sign_extend_bit[local]:
  !n (x:bytes32) i. n < 31 /\ i < 256 ==>
    ((sign_extend (n2w n) x) ' i <=>
     if i < 8 * (n + 1) then x ' i else x ' (8 * n + 7))
Proof
  rpt strip_tac >>
  `fcp$dimindex (:256) = 256` by
    simp[fcpLib.INDEX_CONV ``fcp$dimindex(:256)``] >>
  `w2n (n2w n : bytes32) = n` by
    simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  `8 * n + 7 < fcp$dimindex (:256)` by simp[] >>
  simp[sign_extend_def, lsr_and_1] >>
  Cases_on `x ' (8 * n + 7)` >>
  simp[wordsTheory.word_or_def, wordsTheory.word_and_def,
       wordsTheory.word_1comp_def, fcpTheory.FCP_BETA,
       wordsTheory.SHIFT_1_SUB_1] >>
  Cases_on `i < 8 * (n + 1)` >> gvs[]
QED

Theorem ao_sign_extend_absorb:
  !inner outer (x:bytes32). inner <=+ outer ==>
    sign_extend outer (sign_extend inner x) = sign_extend inner x
Proof
  rpt strip_tac >>
  Cases_on `31w <=+ outer`
  >- metis_tac[ao_sign_extend_large] >>
  `w2n outer < 31 /\ w2n inner <= w2n outer` by
    gvs[wordsTheory.WORD_LS, wordsTheory.dimword_def,
        fcpLib.INDEX_CONV ``fcp$dimindex(:256)``] >>
  `w2n inner < 31` by decide_tac >>
  `inner = n2w (w2n inner) /\ outer = n2w (w2n outer)` by simp[] >>
  qpat_assum `inner = _` SUBST1_TAC >>
  qpat_assum `outer = _` SUBST1_TAC >>
  pure_rewrite_tac[fcpTheory.CART_EQ] >>
  simp_tac std_ss [fcpLib.INDEX_CONV ``fcp$dimindex(:256)``] >>
  rpt strip_tac >>
  `8 * w2n outer + 7 < 256` by decide_tac >>
  asm_simp_tac std_ss [ao_sign_extend_bit] >>
  Cases_on `i < 8 * (w2n outer + 1)` >>
  Cases_on `i < 8 * (w2n inner + 1)` >>
  asm_simp_tac arith_ss [] >>
  Cases_on `w2n inner = w2n outer`
  >- asm_simp_tac arith_ss [] >>
  `~(8 * w2n outer + 7 < 8 * (w2n inner + 1))` by decide_tac >>
  simp[]
QED
