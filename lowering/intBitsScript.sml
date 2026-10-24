(*
 * Integer bitwise operations and their 256-bit words (#636)
 *
 * The source evaluates And, Or and XOr on integers with int_bitwise and
 * checks the result against the type's bound; the lowering emits the word
 * operation unchecked.  These lemmas say the two agree: the word of the
 * integer result is the word operation on the operands' words, and the
 * result of in-range operands is in range.
 *
 * TOP-LEVEL:
 *   i2w_index              — a bit of i2w is int_bit
 *   i2w_int_and, i2w_int_or, i2w_int_xor
 *   i2w_int_shift_left, i2w_int_shift_right_unsigned,
 *   i2w_int_shift_right_signed — shifts
 *   i2w_mod_pow2           — reduction mod 2 ** b is masking the low bits
 *   neg_mask               — a word with its low bits kept, less 2 ** b
 *   int_bitwise_neg        — the sign of an int_bitwise result
 *   within_int_bound_int_bitwise
 *                          — in-range operands give an in-range result
 *
 * Helpers: bits_above, int_bit_large, num_int_not, neg_n2w, bit_top,
 *   lsr_and_1,
 *   within_int_bound_unsigned_bits, within_int_bound_signed_bits
 *)

Theory intBits
Ancestors
  arithmetic bit logroot integer words fcp integer_word int_bitwise
  vyperValue
Libs
  intLib

(* ===== Bits above a bound ===== *)

Theorem bits_above:
  !k m. (!n. k <= n ==> ~BIT n m) <=> m < 2 ** k
Proof
  rpt gen_tac >> eq_tac >> rpt strip_tac
  >- (CCONTR_TAC >> fs[NOT_LESS] >>
      `m <> 0` by (strip_tac >> fs[]) >>
      first_x_assum (qspec_then `LOG2 m` mp_tac) >>
      simp[BIT_LOG2, TWOEXP_LE_IMP_LE_LOG2]) >>
  `m < 2 ** n` by
    (irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** k` >> simp[]) >>
  imp_res_tac NOT_BIT_GT_TWOEXP
QED

(* The high bits of an integer are its sign. *)
Theorem int_bit_large:
  !i. ?N. !n. N <= n ==> (int_bit n i <=> i < 0)
Proof
  gen_tac >> rw[int_bit_def] >>
  qexists_tac `Num (if i < 0 then int_not i else i)` >> rw[] >>
  irule NOT_BIT_GT_TWOEXP >>
  irule LESS_LESS_EQ_TRANS >>
  qexists_tac `2 ** Num (if i < 0 then int_not i else i)` >>
  simp[X_LT_EXP_X, EXP_BASE_LE_MONO]
QED

Theorem num_int_not:
  !i. i < 0 ==> Num (-i) = Num (int_not i) + 1
Proof
  rw[int_not_def] >> COOPER_TAC
QED

(* ===== The bounds, bit by bit ===== *)

Theorem within_int_bound_unsigned_bits:
  !b i. within_int_bound (Unsigned b) i <=>
        0 <= i /\ !n. b <= n ==> ~int_bit n i
Proof
  rw[within_int_bound_def] >> Cases_on `0 <= i` >> simp[] >>
  `~(i < 0)` by ARITH_TAC >> simp[int_bit_def, bits_above]
QED

Theorem within_int_bound_signed_bits:
  !c i. within_int_bound (Signed (SUC c)) i <=>
        !n. c <= n ==> (int_bit n i <=> i < 0)
Proof
  rpt gen_tac >> Cases_on `i < 0` >>
  asm_simp_tac bool_ss [within_int_bound_def, int_bit_def,
    prim_recTheory.LESS_0, SUC_SUB1, LET_THM, bits_above, num_int_not] >>
  simp[]
QED

Theorem int_bitwise_neg:
  !f i j. int_bitwise f i j < 0 <=> f (i < 0) (j < 0)
Proof
  rpt gen_tac >>
  qspec_then `i` (qx_choose_then `N1` assume_tac) int_bit_large >>
  qspec_then `j` (qx_choose_then `N2` assume_tac) int_bit_large >>
  qspec_then `int_bitwise f i j` (qx_choose_then `N3` assume_tac)
    int_bit_large >>
  qspecl_then [`N1 + N2 + N3`, `f`, `i`, `j`] mp_tac int_bit_bitwise >>
  rpt (first_x_assum (qspec_then `N1 + N2 + N3` mp_tac)) >> simp[]
QED

(* A bitwise operation that is false on two clear bits keeps its operands'
   bound: And, Or and XOr. *)
Theorem within_int_bound_int_bitwise:
  !u f i j.
    ~f F F /\ within_int_bound u i /\ within_int_bound u j ==>
    within_int_bound u (int_bitwise f i j)
Proof
  Cases_on `u` >> rpt gen_tac
  >- (rename1 `Signed b` >> Cases_on `b`
      >- (simp[within_int_bound_def] >> rpt strip_tac >> gvs[] >>
          simp[Once int_bit_equiv, int_bit_bitwise] >>
          simp[int_bit_def, BIT_ZERO]) >>
      simp[within_int_bound_signed_bits, int_bit_bitwise, int_bitwise_neg]) >>
  simp[within_int_bound_unsigned_bits, int_bit_bitwise, int_bitwise_neg] >>
  rpt strip_tac >>
  `~(i < 0) /\ ~(j < 0)` by fs[INT_NOT_LT] >>
  simp[GSYM INT_NOT_LT, int_bitwise_neg]
QED

(* ===== Words ===== *)

Theorem neg_n2w:
  !m. 0 < m ==> -(n2w m : 'a word) = ~n2w (m - 1)
Proof
  rw[WORD_NOT] >> `m = (m - 1) + 1` by decide_tac >>
  pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[GSYM word_add_n2w, WORD_NEG_ADD, word_sub_def]
QED

Theorem i2w_index:
  !x i. i < dimindex (:'a) ==> ((i2w x : 'a word) ' i <=> int_bit i x)
Proof
  rw[i2w_def, int_bit_def]
  >- (`0 < Num (-x)` by COOPER_TAC >>
      `Num (-x) - 1 = Num (int_not x)` by (simp[int_not_def] >> COOPER_TAC) >>
      simp[neg_n2w, word_1comp_def, FCP_BETA] >>
      rw[word_index]) >>
  rw[word_index]
QED

Theorem i2w_int_and:
  !x y. (i2w (int_and x y) : 'a word) = i2w x && i2w y
Proof
  rw[CART_EQ, word_and_def, FCP_BETA, i2w_index, int_bit_and]
QED

Theorem i2w_int_or:
  !x y. (i2w (int_or x y) : 'a word) = i2w x || i2w y
Proof
  rw[CART_EQ, word_or_def, FCP_BETA, i2w_index, int_bit_or]
QED

Theorem i2w_int_xor:
  !x y. (i2w (int_xor x y) : 'a word) = i2w x ?? i2w y
Proof
  rw[CART_EQ, word_xor_def, FCP_BETA, i2w_index, int_bit_xor]
QED

Theorem i2w_int_shift_left:
  !n x. (i2w (int_shift_left n x) : 'a word) = i2w x << n
Proof
  rw[CART_EQ, word_lsl_def, FCP_BETA, i2w_index, int_bit_shift_left] >>
  Cases_on `n <= i` >> simp[i2w_index]
QED

Theorem i2w_int_shift_right_unsigned:
  !n x. within_int_bound (Unsigned (dimindex (:'a))) x ==>
        (i2w (int_shift_right n x) : 'a word) = i2w x >>> n
Proof
  rw[CART_EQ, word_lsr_def, FCP_BETA, i2w_index, int_bit_shift_right] >>
  Cases_on `i + n < dimindex (:'a)` >> simp[i2w_index] >>
  fs[within_int_bound_unsigned_bits]
QED

Theorem i2w_int_shift_right_signed:
  !n x. within_int_bound (Signed (dimindex (:'a))) x ==>
        (i2w (int_shift_right n x) : 'a word) = i2w x >> n
Proof
  rpt strip_tac >>
  `?c. dimindex (:'a) = SUC c` by
    (qexists_tac `dimindex (:'a) - 1` >> simp[DIMINDEX_GT_0, ADD1] >>
     `0 < dimindex (:'a)` by simp[DIMINDEX_GT_0] >> decide_tac) >>
  rw[CART_EQ, word_asr_def, FCP_BETA, i2w_index, int_bit_shift_right,
     word_msb_def] >>
  qpat_x_assum `within_int_bound _ _` mp_tac >>
  asm_rewrite_tac[within_int_bound_signed_bits] >> rw[] >>
  `c <= i + n /\ c <= SUC c - 1` by simp[] >> metis_tac[]
QED

(* ===== Reduction to the low bits ===== *)

Theorem i2w_mod_pow2:
  !b x. b <= dimindex (:'a) ==>
        (i2w (x % &(2 ** b)) : 'a word) = i2w x && n2w (2 ** b - 1)
Proof
  rpt strip_tac >>
  qabbrev_tac `D = &dimword (:'a) : int` >>
  `D <> 0` by simp[Abbr `D`, ZERO_LT_dimword, DECIDE ``0n < n ==> n <> 0``] >>
  `x = x / D * D + x % D` by metis_tac[INT_DIVISION, INT_MUL_COMM] >>
  `D = &(2 ** (dimindex (:'a) - b)) * &(2 ** b)` by
    simp[Abbr `D`, dimword_def, INT_MUL, GSYM EXP_ADD] >>
  `x % &(2 ** b) = (x % D) % &(2 ** b)` by
    (qpat_x_assum `x = _` (fn th =>
       GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) empty_rewrites [th]) >>
     qpat_x_assum `D = _ * _` (fn th =>
       GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
         empty_rewrites [th]) >>
     simp[INT_MUL_ASSOC, INT_MOD_ADD_MULTIPLES]) >>
  `x % D = &w2n (i2w x : 'a word)` by simp[Abbr `D`, w2n_i2w] >>
  simp[INT_MOD, i2w_pos] >>
  simp[GSYM WORD_AND_EXP_SUB1]
QED

(* The top bit of a number below 2 ** b says whether it is in the upper
   half. *)
Theorem bit_top:
  !b n. 0 < b /\ n < 2 ** b ==> (BIT (b - 1) n <=> 2 ** (b - 1) <= n)
Proof
  rpt strip_tac >> eq_tac >> strip_tac
  >- metis_tac[BIT_IMP_GE_TWOEXP] >>
  `n <> 0` by (strip_tac >> fs[] >> metis_tac[ZERO_LT_TWOEXP, NOT_LESS]) >>
  `b - 1 <= LOG2 n` by metis_tac[TWOEXP_LE_IMP_LE_LOG2] >>
  `LOG2 n < b` by metis_tac[LT_TWOEXP] >>
  `LOG2 n = b - 1` by decide_tac >> metis_tac[BIT_LOG2]
QED

Theorem lsr_and_1:
  !(w:'a word) k.
    k < dimindex (:'a) ==> ((w >>> k && 1w = 1w) <=> w ' k)
Proof
  rpt strip_tac >>
  `!i. BIT i 1 <=> i = 0` by
    (gen_tac >> `1n = 2 ** 1 - 1` by EVAL_TAC >>
     pop_assum (fn th =>
       GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
     REWRITE_TAC[BIT_EXP_SUB1] >> DECIDE_TAC) >>
  simp[CART_EQ, word_and_def, word_lsr_def, FCP_BETA, word_index] >>
  eq_tac >> rw[]
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[DIMINDEX_GT_0]) >>
  Cases_on `i = 0` >> fs[]
QED

Theorem neg_mask:
  !b w. b < dimindex (:'a) ==>
        (w && n2w (2 ** b - 1)) - n2w (2 ** b) =
        w || ~(n2w (2 ** b - 1) : 'a word)
Proof
  rpt strip_tac >>
  `-(n2w (2 ** b) : 'a word) = ~n2w (2 ** b - 1)` by
    (irule neg_n2w >> simp[ZERO_LT_TWOEXP]) >>
  REWRITE_TAC[word_sub_def] >> pop_assum (fn th => REWRITE_TAC[th]) >>
  qabbrev_tac `M = (n2w (2 ** b - 1) : 'a word)` >>
  `(w && M) && ~M = 0w` by
    (rw[CART_EQ, word_and_def, word_1comp_def, FCP_BETA, word_0] >>
     metis_tac[]) >>
  drule WORD_ADD_OR >> disch_then SUBST1_TAC >>
  rw[CART_EQ, word_and_def, word_or_def, word_1comp_def, FCP_BETA] >>
  metis_tac[]
QED
