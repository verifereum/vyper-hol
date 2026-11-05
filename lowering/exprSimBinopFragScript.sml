(*
 * Expression simulation: binary operators on typed word operands (#636,
 * Operators)
 *
 * binop_frag_typed, the fragment of a binary operator on operands of
 * word_value_types that have their types, by the operator's group onto the
 * simulation lemmas of exprSimOps, exprSimCompare and exprSimArith.
 *
 * TOP-LEVEL:
 *   binop_frag_typed      — binop_frag at the operands' types, for
 *                           exprSimOperators' compile_bop_word_sim
 *   binop_frag_word_typed — the same over any typed word operands
 *
 * The power and shift fragments carry operand facts supplied by the
 * checker and evaluator: literal/value agreement and nonnegative shifts.
 * binop_frag_shr_narrow also covers signed and unsigned widths below 256.
 * ExpMod is excluded by well_typed_binop.
 *
 * The unsafe operators are covered at integer widths of whole bytes, the
 * ones Vyper has: binop_frag_typed takes that of the left operand's type,
 * which exprSimHyps' expr_sim_pre gives (byte_widths_expr).
 *)

Theory exprSimBinopFrag
Ancestors
  exprBopBitwise exprBopFlag exprBopShift exprBopSimDefs exprBopStraight
  exprSimHypsDefs list finite_map fragExec exprSimHyps exprSimOps exprSimCompare exprSimArith primeFactor freshWrites
  exprBopLowering loweringSlice
  exprLowering compileEnv exprLoweringProps emitHelperProps arithmeticProps
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTyping vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
Libs
  emitTacticsLib

(* Adjacent safe/unsafe endpoints of the finite power search. *)
Theorem pow_search_midpoint[local]:
  !lo hi fuel. lo + 1 < hi /\ hi - lo <= 2 ** SUC fuel ==>
    lo <= (lo + hi) DIV 2 /\ (lo + hi) DIV 2 <= hi /\
    (lo + hi) DIV 2 - lo <= 2 ** fuel /\
    hi - (lo + hi) DIV 2 <= 2 ** fuel
Proof
  rpt strip_tac >>
  qspec_then `2` mp_tac arithmeticTheory.DIVISION >>
  (impl_tac >- decide_tac) >>
  disch_then (qspec_then `lo + hi` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `r < 2` >>
  qmatch_asmsub_abbrev_tac `lo + hi = q * 2 + r` >>
  fs[arithmeticTheory.EXP] >> decide_tac
QED

Theorem largest_pow_base_search_bounds[local]:
  !fuel exponent limit lo hi.
    lo ** exponent < limit /\ limit <= hi ** exponent /\
    lo <= hi /\ hi - lo <= 2 ** fuel ==>
    largest_pow_base_search fuel exponent limit lo hi ** exponent < limit /\
    limit <= (largest_pow_base_search fuel exponent limit lo hi + 1) ** exponent
Proof
  Induct_on `fuel`
  >- (rpt gen_tac >> strip_tac >> simp[largest_pow_base_search_def] >>
      `hi <= lo + 1` by gvs[] >>
      `hi ** exponent <= (lo + 1) ** exponent` by
        simp[arithmeticTheory.EXP_EXP_LE_MONO] >> decide_tac) >>
  rpt gen_tac >> strip_tac >> simp[largest_pow_base_search_def] >>
  Cases_on `hi <= lo + 1`
  >- (simp[] >>
      `hi ** exponent <= (lo + 1) ** exponent` by
        simp[arithmeticTheory.EXP_EXP_LE_MONO] >> decide_tac) >>
  `lo + 1 < hi` by decide_tac >>
  drule_all pow_search_midpoint >> strip_tac >>
  `hi + lo = lo + hi` by decide_tac >>
  asm_rewrite_tac[] >>
  Cases_on `((lo + hi) DIV 2) ** exponent < limit` >>
  asm_rewrite_tac[] >>
  first_x_assum irule >> asm_rewrite_tac[] >> decide_tac
QED

Theorem largest_pow_base_bounds:
  !exponent bits signed.
    0 < exponent ==>
    largest_pow_base exponent bits signed ** exponent < (2 ** (bits - if signed then 1 else 0)) /\
    (2 ** (bits - if signed then 1 else 0)) <= (largest_pow_base exponent bits signed + 1) ** exponent
Proof
  rpt gen_tac >> strip_tac >>
  simp[largest_pow_base_def] >>
  irule largest_pow_base_search_bounds >>
  simp[arithmeticTheory.ZERO_EXP] >>
  irule arithmeticTheory.X_LE_X_EXP >> simp[]
QED
Theorem largest_pow_base_threshold:
  !exponent bits signed k.
    0 < exponent ==>
    (k <= largest_pow_base exponent bits signed <=>
     k ** exponent < 2 ** (bits - if signed then 1 else 0))
Proof
  rpt gen_tac >> strip_tac >>
  drule largest_pow_base_bounds >>
  disch_then (qspecl_then [`bits`, `signed`] mp_tac) >>
  simp[] >> strip_tac >> eq_tac
  >- (strip_tac >>
      `k ** exponent <= largest_pow_base exponent bits signed ** exponent` by
        simp[arithmeticTheory.EXP_EXP_LE_MONO] >> decide_tac) >>
  strip_tac >> spose_not_then assume_tac >>
  `largest_pow_base exponent bits signed + 1 <= k` by decide_tac >>
  `(largest_pow_base exponent bits signed + 1) ** exponent <= k ** exponent` by
    simp[arithmeticTheory.EXP_EXP_LE_MONO] >> decide_tac
QED

Theorem largest_pow_exponent_search_bounds[local]:
  !fuel base limit exponent.
    base ** exponent < limit /\ limit <= base ** (exponent + fuel + 1) ==>
    base ** largest_pow_exponent_search fuel base limit exponent < limit /\
    limit <= base ** (largest_pow_exponent_search fuel base limit exponent + 1)
Proof
  Induct_on `fuel`
  >- simp[largest_pow_exponent_search_def] >>
  rpt gen_tac >> strip_tac >>
  simp[largest_pow_exponent_search_def] >>
  rename1 `b ** exponent < limit` >>
  Cases_on `b ** (exponent + 1) < limit` >> asm_rewrite_tac[]
  >- (first_x_assum irule >>
      `exponent + 1 + fuel + 1 = exponent + SUC fuel + 1` by decide_tac >>
      asm_rewrite_tac[]) >>
  decide_tac
QED

Theorem largest_pow_exponent_bounds:
  !b bits signed.
    2 <= b /\ b < 2 ** (bits - if signed then 1 else 0) ==>
    b ** largest_pow_exponent b bits signed <
      2 ** (bits - if signed then 1 else 0) /\
    2 ** (bits - if signed then 1 else 0) <=
      b ** (largest_pow_exponent b bits signed + 1)
Proof
  rpt gen_tac >> strip_tac >>
  simp[largest_pow_exponent_def] >>
  irule largest_pow_exponent_search_bounds >> simp[] >>
  irule arithmeticTheory.LE_TRANS >>
  qexists_tac `2 ** (1 + (bits + 1) + 1)` >>
  simp[arithmeticTheory.EXP_EXP_LE_MONO,
       arithmeticTheory.EXP_BASE_LE_MONO]
QED

Theorem largest_pow_exponent_threshold:
  !b bits signed k.
    2 <= b /\ b < 2 ** (bits - if signed then 1 else 0) ==>
    (k <= largest_pow_exponent b bits signed <=>
     b ** k < 2 ** (bits - if signed then 1 else 0))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all largest_pow_exponent_bounds >> strip_tac >> eq_tac
  >- (strip_tac >>
      `b ** k <= b ** largest_pow_exponent b bits signed` by
        (simp[arithmeticTheory.EXP_BASE_LE_MONO]) >> decide_tac) >>
  strip_tac >> spose_not_then assume_tac >>
  `largest_pow_exponent b bits signed + 1 <= k` by decide_tac >>
  `b ** (largest_pow_exponent b bits signed + 1) <= b ** k` by
    simp[arithmeticTheory.EXP_BASE_LE_MONO] >> decide_tac
QED


(* The first unsafe exponent is the only possible equality endpoint. *)
Theorem largest_pow_exponent_endpoint:
  !b bits signed k.
    2 <= b /\ b < 2 ** (bits - if signed then 1 else 0) /\
    b ** k = 2 ** (bits - if signed then 1 else 0) ==>
    k = largest_pow_exponent b bits signed + 1
Proof
  rpt strip_tac >>
  drule_all largest_pow_exponent_bounds >> strip_tac >>
  `largest_pow_exponent b bits signed < k` by
    (spose_not_then assume_tac >>
     `b ** k <= b ** largest_pow_exponent b bits signed` by
       simp[arithmeticTheory.EXP_BASE_LE_MONO] >> decide_tac) >>
  Cases_on `k = largest_pow_exponent b bits signed + 1` >- simp[] >>
  `largest_pow_exponent b bits signed + 1 < k` by decide_tac >>
  `b ** (largest_pow_exponent b bits signed + 1) < b ** k` by
    simp[arithmeticTheory.EXP_BASE_LT_MONO] >> decide_tac
QED

Theorem largest_pow_exponent_signed_threshold:
  !b bits neg k.
    2 <= b /\ b < 2 ** (bits - 1) ==>
    (k <= (           if neg /\ ODD ((largest_pow_exponent b bits T) + 1) /\ b ** ((largest_pow_exponent b bits T) + 1) = 2 ** (bits - 1)
           then (largest_pow_exponent b bits T) + 1 else (largest_pow_exponent b bits T)) <=>
     b ** k < 2 ** (bits - 1) \/
     neg /\ ODD k /\ b ** k = 2 ** (bits - 1))
Proof
  rpt strip_tac >> simp_tac (srw_ss()) [LET_THM] >>
  `!k. (k <= largest_pow_exponent b bits T <=>
        b ** k < 2 ** (bits - 1))` by
    (gen_tac >>
     qspecl_then [`b`, `bits`, `T`] mp_tac largest_pow_exponent_threshold >>
     simp[]) >>
  `!k. b ** k = 2 ** (bits - 1) ==>
        k = largest_pow_exponent b bits T + 1` by
    (rpt strip_tac >> irule largest_pow_exponent_endpoint >> simp[] >>
     qexists_tac `T` >> simp[]) >>
  rename1 `if isneg /\ _ then _ else _` >>
  Cases_on `isneg /\ ODD (largest_pow_exponent b bits T + 1) /\
             b ** (largest_pow_exponent b bits T + 1) = 2 ** (bits - 1)`
  >- (qpat_assum `isneg /\ _ /\ _` (fn th => rewrite_tac[th]) >>
      metis_tac[arithmeticTheory.LESS_EQ_IFF_LESS_SUC,
                arithmeticTheory.ADD1, arithmeticTheory.LESS_OR_EQ]) >>
  qpat_assum `~(isneg /\ _ /\ _)` (fn th => rewrite_tac[th]) >>
  metis_tac[]
QED

(* The type and the value of a typed operand of a word_value_type. *)
Theorem word_value_type_value_cases:
  !tenv t tv v.
    word_value_type t /\ evaluate_type tenv t = SOME tv /\
    value_has_type tv v ==>
    (?n i. t = BaseT (UintT n) /\ tv = BaseTV (UintT n) /\ v = IntV i /\
           0 < n /\ n <= 256 /\ within_int_bound (Unsigned n) i) \/
    (?n i. t = BaseT (IntT n) /\ tv = BaseTV (IntT n) /\ v = IntV i /\
           1 < n /\ n <= 256 /\ within_int_bound (Signed n) i) \/
    (?d. t = BaseT DecimalT /\ tv = BaseTV DecimalT /\ v = DecimalV d /\
         within_int_bound (Signed 168) d) \/
    (?b. t = BaseT BoolT /\ tv = BaseTV BoolT /\ v = BoolV b) \/
    (?nsid m k. t = FlagT nsid /\ tv = FlagTV m /\ v = FlagV k /\ m <= 256)
Proof
  rpt strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT DecimalT \/ t = BaseT BoolT \/ (?nsid. t = FlagT nsid)` by
    (Cases_on `t` >> fs[word_value_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_int_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, vyperValueTheory.within_int_bound_def]
QED

(* A typed value of an integer type. *)
Theorem int_type_value:
  !tenv ty tv v.
    is_int_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
    ?i. v = IntV i /\ 0 < type_bits ty /\ type_bits ty <= 256 /\
        type_to_int_bound ty =
          SOME (if is_signed_type ty then Signed (type_bits ty)
                else Unsigned (type_bits ty)) /\
        within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                          else Unsigned (type_bits ty)) i
Proof
  rpt strip_tac >>
  `word_value_type ty` by gvs[word_value_type_def] >>
  qspecl_then [`tenv`, `ty`, `tv`, `v`] mp_tac word_value_type_value_cases >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  gvs[type_to_int_bound_def, type_bits_def, is_signed_type_def]
QED

(* Modular exponentiation preserves the integer encoding, including
   negative bases.  Induct over the mathematical exponent, not its word. *)
Theorem int_pow_word_encoding:
  !a e. (n2w (w2n (i2w a : bytes32) ** e) : bytes32) = i2w (a ** e)
Proof
  Induct_on `e` >>
  simp[arithmeticTheory.EXP, integerTheory.int_exp,
       GSYM wordsTheory.word_mul_n2w,
       integer_wordTheory.word_i2w_mul, integer_wordTheory.i2w_pos]
QED

Theorem word_exp_int_encoding:
  !a b. 0 <= b /\ b < &(dimword (:256)) ==>
    word_exp (i2w a : bytes32) (i2w b) = i2w (a ** Num b)
Proof
  rpt strip_tac >>
  `b = &(Num b)` by simp[] >>
  `Num b < dimword (:256)` by intLib.ARITH_TAC >>
  `i2w b = (n2w (Num b) : bytes32)` by
    metis_tac[integer_wordTheory.i2w_pos] >>
  simp[wordsTheory.word_exp_def, wordsTheory.w2n_n2w,
       int_pow_word_encoding]
QED

(* Multiplicity at a prime scales with the exponent. *)
Theorem pow_prime_multiplicity[local]:
  !a e p. 0 < a ==>
    PRIME_FACTORS (a ** e) p = e * PRIME_FACTORS a p
Proof
  Induct_on `e` >>
  simp[arithmeticTheory.EXP, primeFactorTheory.PRIME_FACTORS_1,
       bagTheory.EMPTY_BAG_alt] >> rpt strip_tac >>
  simp[primeFactorTheory.PRIME_FACTORS_MULT, arithmeticTheory.ZERO_LT_EXP,
       bagTheory.BAG_UNION, arithmeticTheory.MULT_CLAUSES]
QED

(* An even power cannot equal an odd power of two.  This is the
   asymmetric signed lower endpoint used by the literal-exponent guard. *)
Theorem pow_two_odd_exponent:
  !a e k. 0 < a /\ a ** e = 2 ** k /\ ODD k ==> ODD e
Proof
  rpt strip_tac >>
  `PRIME_FACTORS (a ** e) 2 = e * PRIME_FACTORS a 2` by
    simp[pow_prime_multiplicity] >>
  `PRIME_FACTORS (2 ** k) 2 = k` by
    simp[primeFactorTheory.PRIME_FACTORS_EXP, dividesTheory.PRIME_2] >>
  `k = e * PRIME_FACTORS a 2` by metis_tac[] >>
  gvs[arithmeticTheory.ODD_MULT]
QED

(* The signed lower endpoint is included exactly for negative odd powers. *)
Theorem signed_power_bound:
  !a e bits. 0 < bits ==>
    (within_int_bound (Signed bits) (a ** e) <=>
     Num (ABS a) ** e < 2 ** (bits - 1) \/
     a < 0 /\ ODD e /\ Num (ABS a) ** e = 2 ** (bits - 1))
Proof
  rpt strip_tac >>
  qspec_then `a` strip_assume_tac integerTheory.INT_NUM_CASES >>
  gvs[integerTheory.INT_ABS_NEG, integerTheory.INT_EXP,
      vyperValueTheory.within_int_bound_def] >>
  Cases_on `ODD e` >>
  simp[integerTheory.INT_POW_NEG, arithmeticTheory.EVEN_ODD,
       integerTheory.INT_EXP, arithmeticTheory.ZERO_LT_EXP] >> decide_tac
QED

Theorem unsigned_power_bound:
  !a e bits. 0 <= a ==>
    (within_int_bound (Unsigned bits) (a ** e) <=>
     Num a ** e < 2 ** bits)
Proof
  rpt strip_tac >>
  `a = &(Num a)` by simp[] >> pop_assum SUBST_ALL_TAC >>
  simp[integerTheory.INT_EXP, vyperValueTheory.within_int_bound_def]
QED

(* The ordinary signed literal-base guard, including its negative endpoint. *)
Theorem signed_literal_base_power_guard:
  !a bits k.
    0 < bits /\ 2 <= Num (ABS a) /\
    Num (ABS a) < 2 ** (bits - 1) ==>
    (k <= (           if a < 0 /\ ODD ((largest_pow_exponent (Num (ABS a)) bits T) + 1) /\
              Num (ABS a) ** ((largest_pow_exponent (Num (ABS a)) bits T) + 1) = 2 ** (bits - 1)
           then (largest_pow_exponent (Num (ABS a)) bits T) + 1 else (largest_pow_exponent (Num (ABS a)) bits T)) <=>
     within_int_bound (Signed bits) (a ** k))
Proof
  rpt strip_tac >>
  qspecl_then [`Num (ABS a)`, `bits`, `a < 0`, `k`] mp_tac
    largest_pow_exponent_signed_threshold >>
  simp[signed_power_bound]
QED

Theorem unsigned_literal_base_power_guard:
  !a bits k.
    0 <= a /\ 2 <= Num a /\ Num a < 2 ** bits ==>
    (k <= largest_pow_exponent (Num a) bits F <=>
     within_int_bound (Unsigned bits) (a ** k))
Proof
  rpt strip_tac >>
  qspecl_then [`Num a`, `bits`, `F`, `k`] mp_tac
    largest_pow_exponent_threshold >>
  simp[unsigned_power_bound]
QED

Theorem largest_pow_exponent_at_limit:
  !b bits signed.
    2 <= b /\ 2 ** (bits - if signed then 1 else 0) <= b ==>
    largest_pow_exponent b bits signed = 1
Proof
  rpt strip_tac >>
  `2 ** (bits - if signed then 1 else 0) <= b ** 2` by
    (irule arithmeticTheory.LE_TRANS >> qexists_tac `b` >>
     simp[arithmeticTheory.X_LE_X_EXP]) >>
  simp[largest_pow_exponent_def] >>
  Cases_on `bits + 1` >- simp[largest_pow_exponent_search_def] >>
  simp[Once largest_pow_exponent_search_def]
QED

Theorem largest_pow_base_endpoint:
  !e bits signed m.
    0 < e /\ m ** e = 2 ** (bits - if signed then 1 else 0) ==>
    m = largest_pow_base e bits signed + 1
Proof
  rpt strip_tac >>
  drule largest_pow_base_bounds >>
  disch_then (qspecl_then [`bits`, `signed`] mp_tac) >>
  simp[] >> strip_tac >>
  `largest_pow_base e bits signed < m` by
    (spose_not_then assume_tac >>
     `m ** e <= largest_pow_base e bits signed ** e` by
       simp[arithmeticTheory.EXP_EXP_LE_MONO] >> decide_tac) >>
  Cases_on `m = largest_pow_base e bits signed + 1` >- simp[] >>
  `largest_pow_base e bits signed + 1 < m` by decide_tac >>
  `(largest_pow_base e bits signed + 1) ** e < m ** e` by
    simp[arithmeticTheory.EXP_EXP_LT_MONO] >> decide_tac
QED

(* Byte alignment makes every exact negative endpoint an odd power. *)
Theorem largest_pow_base_signed_threshold:
  !e bits m. 0 < e /\ ODD (bits - 1) ==>
    (m <= (           if ((largest_pow_base e bits T) + 1) ** e = 2 ** (bits - 1) then (largest_pow_base e bits T) + 1 else (largest_pow_base e bits T)) <=>
     m ** e < 2 ** (bits - 1) \/
     ODD e /\ m ** e = 2 ** (bits - 1))
Proof
  rpt strip_tac >> simp_tac (srw_ss()) [LET_THM] >>
  `!j. (j <= largest_pow_base e bits T <=>
        j ** e < 2 ** (bits - 1))` by
    (gen_tac >>
     qspecl_then [`e`, `bits`, `T`, `j`] mp_tac largest_pow_base_threshold >>
     simp[]) >>
  `!j. j ** e = 2 ** (bits - 1) ==>
        j = largest_pow_base e bits T + 1` by
    (rpt strip_tac >> irule largest_pow_base_endpoint >> simp[] >>
     qexists_tac `T` >> simp[]) >>
  `!j. j ** e = 2 ** (bits - 1) ==> ODD e` by
    (rpt strip_tac >>
     `0 < j` by
       (qpat_x_assum `!j. j <= _ <=> _` kall_tac >>
        qpat_x_assum `!j. _ ==> j = _` kall_tac >>
        Cases_on `j` >> gvs[arithmeticTheory.ZERO_EXP]) >>
     drule_all pow_two_odd_exponent >> simp[]) >>
  Cases_on `(largest_pow_base e bits T + 1) ** e = 2 ** (bits - 1)`
  >- (qpat_assum `(_ + 1) ** e = _` (fn th => rewrite_tac[th]) >>
      metis_tac[arithmeticTheory.LESS_EQ_IFF_LESS_SUC,
                arithmeticTheory.ADD1, arithmeticTheory.LESS_OR_EQ]) >>
  qpat_assum `~((_ + 1) ** e = _)` (fn th => rewrite_tac[th]) >>
  metis_tac[]
QED

Theorem signed_literal_exponent_power_guard:
  !a e bits. 0 < e /\ 0 < bits /\ ODD (bits - 1) ==>
    ((-&(if (largest_pow_base e bits T + 1) ** e = 2 ** (bits - 1)
           then largest_pow_base e bits T + 1 else largest_pow_base e bits T) <= a /\ a <= &(largest_pow_base e bits T)) <=>
     within_int_bound (Signed bits) (a ** e))
Proof
  rpt strip_tac >>
  qspec_then `a` strip_assume_tac integerTheory.INT_NUM_CASES >>
  gvs[signed_power_bound] >>
  simp[largest_pow_base_threshold, largest_pow_base_signed_threshold,
       arithmeticTheory.ZERO_EXP] >>
  qspecl_then [`e`, `bits`, `n`] mp_tac largest_pow_base_signed_threshold >>
  simp[]
QED

Theorem unsigned_literal_exponent_power_guard:
  !a e bits. 0 <= a /\ 0 < e ==>
    (a <= &(largest_pow_base e bits F) <=>
     within_int_bound (Unsigned bits) (a ** e))
Proof
  rpt strip_tac >>
  `a = &(Num a)` by simp[] >> pop_assum SUBST_ALL_TAC >>
  simp[unsigned_power_bound, largest_pow_base_threshold]
QED

Theorem byte_width_signed_endpoint_odd:
  !bits. 0 < bits /\ bits MOD 8 = 0 ==> ODD (bits - 1)
Proof
  rpt strip_tac >>
  qspec_then `8` mp_tac arithmeticTheory.DIVISION >>
  simp[] >> disch_then (qspec_then `bits` strip_assume_tac) >>
  `bits = bits DIV 8 * 8` by decide_tac >>
  `EVEN bits` by
    (qpat_x_assum `bits = _ * 8` (fn th => once_rewrite_tac[th]) >>
     simp[arithmeticTheory.EVEN_MULT]) >>
  `SUC (bits - 1) = bits` by decide_tac >>
  metis_tac[arithmeticTheory.EVEN, arithmeticTheory.ODD_EVEN]
QED

(* The signed minimum base is outside the strict safe-start search interface. *)
Theorem signed_minimum_power_guard:
  !bits k. 1 < bits ==>
    (k <= (           if ODD ((largest_pow_exponent (2 ** (bits - 1)) bits T) + 1) /\ (2 ** (bits - 1)) ** ((largest_pow_exponent (2 ** (bits - 1)) bits T) + 1) = (2 ** (bits - 1))
           then (largest_pow_exponent (2 ** (bits - 1)) bits T) + 1 else (largest_pow_exponent (2 ** (bits - 1)) bits T)) <=>
     within_int_bound (Signed bits) ((-&(2 ** (bits - 1))) ** k))
Proof
  rpt strip_tac >>
  `2 <= 2 ** (bits - 1)` by
    (irule arithmeticTheory.X_LE_X_EXP >> simp[]) >>
  `!e. (2 ** (bits - 1)) ** e < 2 ** (bits - 1) <=> e < 1` by
    (gen_tac >>
     qspec_then `2 ** (bits - 1)` mp_tac
       arithmeticTheory.EXP_BASE_LT_MONO >>
     (impl_tac >- decide_tac) >>
     disch_then (qspecl_then [`1`, `e`] mp_tac) >>
     rewrite_tac[arithmeticTheory.EXP_1]) >>
  `!e. (2 ** (bits - 1)) ** e = 2 ** (bits - 1) <=> e = 1` by
    (gen_tac >>
     qspec_then `2 ** (bits - 1)` mp_tac
       arithmeticTheory.EXP_BASE_INJECTIVE >>
     (impl_tac >- decide_tac) >>
     disch_then (qspecl_then [`e`, `1`] mp_tac) >>
     rewrite_tac[arithmeticTheory.EXP_1]) >>
  simp[signed_power_bound, largest_pow_exponent_at_limit] >>
  Cases_on `k = 1` >> simp[] >> decide_tac
QED

(* The three small literal bases never overflow at Vyper integer widths. *)
Theorem small_literal_base_power_bound:
  !a e bits signed.
    1 < bits /\ (a = -1 \/ a = 0 \/ a = 1) /\
    (~signed ==> 0 <= a) ==>
    within_int_bound (if signed then Signed bits else Unsigned bits) (a ** e)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `signed` >> gvs[] >>
  simp[signed_power_bound, unsigned_power_bound,
       arithmeticTheory.ZERO_EXP] >>
  Cases_on `e = 0` >> simp[vyperValueTheory.within_int_bound_def]
QED

(* Search outputs fit the comparison literals without modular truncation. *)
Theorem largest_pow_exponent_search_range[local]:
  !fuel b limit e.
    e <= largest_pow_exponent_search fuel b limit e /\
    largest_pow_exponent_search fuel b limit e <= e + fuel
Proof
  Induct_on `fuel` >- simp[largest_pow_exponent_search_def] >>
  rpt gen_tac >> simp[largest_pow_exponent_search_def] >>
  Cases_on `b ** (e + 1) < limit` >> simp[] >>
  first_x_assum (qspecl_then [`b`, `limit`, `e + 1`] strip_assume_tac) >>
  decide_tac
QED

Theorem largest_pow_exponent_le:
  !b bits signed. largest_pow_exponent b bits signed <= bits + 2
Proof
  rpt gen_tac >> simp[largest_pow_exponent_def] >>
  qspecl_then [`bits + 1`, `b`, `2 ** (bits - if signed then 1 else 0)`, `1`]
    mp_tac largest_pow_exponent_search_range >> simp[]
QED

Theorem largest_pow_base_lt_limit:
  !e bits signed. 0 < e ==>
    largest_pow_base e bits signed < 2 ** (bits - if signed then 1 else 0)
Proof
  rpt strip_tac >>
  drule largest_pow_base_bounds >>
  disch_then (qspecl_then [`bits`, `signed`] mp_tac) >>
  simp[] >> strip_tac >>
  `largest_pow_base e bits signed <= largest_pow_base e bits signed ** e` by
    (irule arithmeticTheory.X_LE_X_EXP >> simp[]) >> decide_tac
QED

(* Power's source boundary exposes both negative exponents and overflow. *)
Theorem bop_result_power:
  !cx ann tys a b es u.
    type_to_int_bound ann = SOME u ==>
    bop_result cx ann Exp tys (IntV a) (IntV b) es =
      if b < 0 then INR (Error (RuntimeError "Exp~"))
      else if within_int_bound u (a ** Num b)
           then INL (IntV (a ** Num b))
           else INR (Error (RuntimeError "bounded_int_op bound"))
Proof
  rpt strip_tac >>
  simp[bop_result_def, vyperContextTheory.evaluate_builtin_def,
       vyperValueOperationTheory.evaluate_binop_def,
       vyperValueOperationTheory.bounded_int_op_def] >>
  Cases_on `b < 0` >> simp[] >>
  Cases_on `within_int_bound u (a ** Num b)` >> simp[]
QED

Theorem straight_fresh_compile_safe_pow:
  !x y ty bl el. straight_fresh (compile_safe_pow x y ty bl el)
Proof
  rpt gen_tac >> Cases_on `bl` >> Cases_on `el` >>
  simp[compile_safe_pow_def] >>
  rpt (FIRST [irule straight_fresh_bind >> conj_tac,
              irule straight_fresh_ignore_bind >> conj_tac,
              gen_tac >> BETA_TAC,
              irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
              irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
              MATCH_ACCEPT_TAC straight_fresh_return,
              irule straight_fresh_compile_clamp,
              IF_CASES_TAC])
QED

(* The unconditional ASSERT/EXP branch used by exponents zero and one. *)
Theorem assert_true_exp_run:
  !x y sa op sb ss va vb.
    (do emit_void ASSERT [Lit 1w]; emit_op Exp [x; y] od) sa = (op, sb) /\
    eval_operand x ss = SOME va /\ eval_operand y ss = SOME vb ==>
    ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
          eval_operand op ss' = SOME (word_exp va vb)
Proof
  rpt gen_tac >>
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[exprLoweringPropsTheory.emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM listTheory.APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Once exprLoweringPropsTheory.run_inst_seq_def] >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def, venomInstTheory.mk_inst_def] >>
  simp[Once exprLoweringPropsTheory.run_inst_seq_def] >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def,
       venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_pure2_def] >>
  simp[exprLoweringPropsTheory.run_inst_seq_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* ASSERT rejects exactly zero; on acceptance EXP uses the original operands. *)
Theorem assert_exp_run:
  !c x y sa op sb ss cv va vb.
    (do emit_void ASSERT [c]; emit_op Exp [x; y] od) sa = (op, sb) /\
    eval_operand c ss = SOME cv /\
    eval_operand x ss = SOME va /\ eval_operand y ss = SOME vb ==>
    (cv <> 0w ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
            eval_operand op ss' = SOME (word_exp va vb)) /\
    (cv = 0w ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  rpt gen_tac >>
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[exprLoweringPropsTheory.emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM listTheory.APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  `step_inst_base (mk_inst sa.cs_next_id ASSERT [c] []) ss =
     if cv = 0w then Abort Revert_abort
       (revert_state (set_returndata [] ss)) else OK ss` by
    (once_rewrite_tac[venomExecSemanticsTheory.step_inst_base_def] >>
     simp_tac (srw_ss()) [venomInstTheory.mk_inst_def] >>
     Cases_on `cv = 0w` >> gvs[]) >>
  simp[Once exprLoweringPropsTheory.run_inst_seq_def] >>
  Cases_on `cv = 0w` >> simp[] >>
  simp[Once exprLoweringPropsTheory.run_inst_seq_def] >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def,
       venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_pure2_def] >>
  simp[exprLoweringPropsTheory.run_inst_seq_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* The unsigned upper guard shared by literal-base and literal-exponent code. *)
Theorem upper_guard_exp_run:
  !z x y upper sa op sb ss vz va vb.
    (do high <- emit_op GT [z; Lit upper];
        ok <- emit_op ISZERO [high];
        emit_void ASSERT [ok]; emit_op Exp [x; y] od) sa = (op, sb) /\
    fresh_vars_wrt sa ss /\ eval_operand z ss = SOME vz /\
    eval_operand x ss = SOME va /\ eval_operand y ss = SOME vb ==>
    (w2n vz <= w2n upper ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
            eval_operand op ss' = SOME (word_exp va vb)) /\
    (~(w2n vz <= w2n upper) ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ sa = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_all (elim_lit 2 emit_op_GT_correct) >> strip_tac >>
  forward_all_evals >>
  drule_all emit_op_ISZERO_correct_mem >> strip_tac >>
  forward_all_evals >>
  ` (do emit_void ASSERT [ok]; emit_op Exp [x; y] od) cs'' = (op, sb)` by
    simp[comp_bind_def, comp_ignore_bind_def] >>
  drule_all assert_exp_run >> strip_tac >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `run_inst_seq (emitted_insts sa cs'') ss = OK ss''` by
    (drule_all (Q.SPECL [`sa`, `cs'`, `cs''`] run_inst_seq_chain) >> simp[]) >>
  `sb.cs_current_insts = cs''.cs_current_insts ++ emitted_insts cs'' sb` by
    metis_tac[extends_trans] >>
  `cs''.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa cs''` by
    metis_tac[extends_trans] >>
  drule_all run_inst_seq_chain >> strip_tac >>
  gvs[venomExecSemanticsTheory.bool_to_word_def] >>
  Cases_on `w2n vz <= w2n upper` >> gvs[]
QED

(* The signed interval guard used when only the exponent is literal. *)
Theorem signed_guard_exp_run:
  !x y lower upper sa op sb ss va vb.
    (do below <- emit_op SLT [x; Lit lower];
        ge <- emit_op ISZERO [below];
        above <- emit_op SGT [x; Lit upper];
        le <- emit_op ISZERO [above];
        ok <- emit_op AND [ge; le];
        emit_void ASSERT [ok]; emit_op Exp [x; y] od) sa = (op, sb) /\
    fresh_vars_wrt sa ss /\
    eval_operand x ss = SOME va /\ eval_operand y ss = SOME vb ==>
    (w2i lower <= w2i va /\ w2i va <= w2i upper ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
            eval_operand op ss' = SOME (word_exp va vb)) /\
    (~(w2i lower <= w2i va /\ w2i va <= w2i upper) ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ sa = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_all (elim_lit 2 emit_op_SLT_correct) >> strip_tac >>
  forward_all_evals >>
  drule_all emit_op_ISZERO_correct_mem >> strip_tac >>
  forward_all_evals >>
  drule_all (elim_lit 2 emit_op_SGT_correct) >> strip_tac >>
  forward_all_evals >>
  drule_all emit_op_ISZERO_correct_mem >> strip_tac >>
  forward_all_evals >>
  drule_all emit_op_AND_correct >> strip_tac >>
  forward_all_evals >>
  rename1 `emit_op AND [ge; le] c4 = (ok,c5)` >>
  rename1 `emit_op ISZERO [above] c3 = (le,c4)` >>
  rename1 `emit_op SGT [x; Lit upper] c2 = (above,c3)` >>
  rename1 `emit_op ISZERO [below] c1 = (ge,c2)` >>
  rename1 `emit_void ASSERT [ok] c5 = ((),c6)` >>
  rename1 `run_inst_seq (emitted_insts c4 c5) s4 = OK s5` >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  ` (do emit_void ASSERT [ok]; emit_op Exp [x; y] od) c5 = (op, sb)` by
    simp[comp_bind_def, comp_ignore_bind_def] >>
  drule_all assert_exp_run >> strip_tac >>
  rpt (qpat_x_assum `!a. a < LENGTH _ ==> _` kall_tac) >>
  rpt (qpat_x_assum `LENGTH _.vs_memory = _` kall_tac) >>
  rpt (qpat_x_assum `!op w. _ ==> _` kall_tac) >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `run_inst_seq (emitted_insts sa c2) ss = OK s2` by
    metis_tac[run_inst_seq_chain] >>
  `c2.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c2` by
    metis_tac[extends_trans] >>
  `run_inst_seq (emitted_insts sa c3) ss = OK s3` by
    metis_tac[run_inst_seq_chain] >>
  `c3.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c3` by
    metis_tac[extends_trans] >>
  `run_inst_seq (emitted_insts sa c4) ss = OK s4` by
    metis_tac[run_inst_seq_chain] >>
  `c4.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c4` by
    metis_tac[extends_trans] >>
  `run_inst_seq (emitted_insts sa c5) ss = OK s5` by
    metis_tac[run_inst_seq_chain] >>
  `c5.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c5` by
    metis_tac[extends_trans] >>
  `sb.cs_current_insts = c5.cs_current_insts ++ emitted_insts c5 sb` by
    metis_tac[extends_trans] >>
  drule_all run_inst_seq_chain >> strip_tac >>
  Cases_on `w2i lower <= w2i va` >> Cases_on `w2i va <= w2i upper` >>
  gvs[venomExecSemanticsTheory.bool_to_word_def, integer_wordTheory.WORD_LTi,
      integer_wordTheory.WORD_GTi, integerTheory.INT_NOT_LT,
      integerTheory.INT_NOT_LE, integerTheory.INT_GT]
QED

(* Small signed literal bases need only reject negative exponents. *)
Theorem nonnegative_guard_exp_run:
  !x y sa op sb ss va vb.
    (do negative <- emit_op SLT [y; Lit 0w];
        ok <- emit_op ISZERO [negative];
        emit_void ASSERT [ok]; emit_op Exp [x; y] od) sa = (op, sb) /\
    fresh_vars_wrt sa ss /\
    eval_operand x ss = SOME va /\ eval_operand y ss = SOME vb ==>
    (0 <= w2i vb ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
            eval_operand op ss' = SOME (word_exp va vb)) /\
    (~(0 <= w2i vb) ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ sa = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_all (elim_lit 2 emit_op_SLT_correct) >> strip_tac >>
  forward_all_evals >>
  drule_all emit_op_ISZERO_correct_mem >> strip_tac >>
  forward_all_evals >>
  ` (do emit_void ASSERT [ok]; emit_op Exp [x; y] od) cs'' = (op, sb)` by
    simp[comp_bind_def, comp_ignore_bind_def] >>
  drule_all assert_exp_run >> strip_tac >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `run_inst_seq (emitted_insts sa cs'') ss = OK ss''` by
    metis_tac[run_inst_seq_chain] >>
  `sb.cs_current_insts = cs''.cs_current_insts ++ emitted_insts cs'' sb` by
    metis_tac[extends_trans] >>
  `cs''.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa cs''` by
    metis_tac[extends_trans] >>
  drule_all run_inst_seq_chain >> strip_tac >>
  Cases_on `0 <= w2i vb` >>
  gvs[venomExecSemanticsTheory.bool_to_word_def, integer_wordTheory.WORD_LTi,
      integerTheory.INT_NOT_LT, integerTheory.INT_NOT_LE,
      integer_wordTheory.word_0_w2i]
QED

(* Successful integer type evaluation enforces byte-aligned widths. *)
Theorem int_type_byte_width:
  !tenv ty tv.
    is_int_type ty /\ evaluate_type tenv ty = SOME tv ==>
    type_bits ty MOD 8 = 0
Proof
  Cases_on `ty` >> simp[is_int_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_int_type_def, vyperValueTheory.evaluate_type_def,
       type_bits_def] >> rpt strip_tac >> gvs[AllCaseEqs()]
QED

(* Typed nonnegative integers are represented without word truncation. *)
Theorem power_nonnegative_word_bound:
  !bits s z.
    0 < bits /\ bits <= 256 /\
    within_int_bound (if s then Signed bits else Unsigned bits) z /\
    0 <= z ==>
    z < &(dimword (:256)) /\ w2n (i2w z : bytes32) = Num z
Proof
  rpt gen_tac >> strip_tac >>
  `~(z < 0)` by intLib.ARITH_TAC >>
  `2 ** bits <= 2 ** 256` by simp[arithmeticTheory.EXP_BASE_LE_MONO] >>
  `2 ** (bits - 1) <= 2 ** 256` by
    simp[arithmeticTheory.EXP_BASE_LE_MONO] >>
  `Num z < 2 ** 256` by
    (Cases_on `s`
     >- (`Num z < 2 ** (bits - 1)` by
           gvs[vyperValueTheory.within_int_bound_def,
               integerTheory.INT_NOT_LT] >>
         irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
         qexists_tac `2 ** (bits - 1)` >> simp[]) >>
     `Num z < 2 ** bits` by
       gvs[vyperValueTheory.within_int_bound_def] >>
     irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** bits` >> simp[]) >>
  `z = &(Num z)` by simp[] >>
  `z < &(2 ** 256)` by intLib.ARITH_TAC >>
  `Num z < dimword (:256)` by
    fs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  conj_tac
  >- fs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  qpat_x_assum `z = _` SUBST1_TAC >>
  simp[integer_wordTheory.i2w_pos, wordsTheory.w2n_n2w]
QED

Theorem power_upper_word_signed:
  !k. k < 2 ** 255 ==> w2i (n2w k : bytes32) = &k
Proof
  rpt strip_tac >>
  rewrite_tac[GSYM integer_wordTheory.i2w_pos] >>
  irule integer_wordTheory.w2i_i2w >>
  fs[integer_wordTheory.INT_MIN_def, integer_wordTheory.INT_MAX_def,
     wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def,
     venomMemPropsTheory.dimindex_256] >> intLib.ARITH_TAC
QED

Theorem power_lower_word_signed:
  !k. k <= 2 ** 255 ==> w2i (i2w (-&k) : bytes32) = -&k
Proof
  rpt strip_tac >> irule integer_wordTheory.w2i_i2w >>
  fs[integer_wordTheory.INT_MIN_def, integer_wordTheory.INT_MAX_def,
     wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def,
     venomMemPropsTheory.dimindex_256] >> intLib.ARITH_TAC
QED

(* An unsigned comparison with a small threshold also rejects signed negatives. *)
Theorem power_exponent_word_guard:
  !bits s z k.
    0 < bits /\ bits <= 256 /\
    within_int_bound (if s then Signed bits else Unsigned bits) z /\
    k < 2 ** 255 ==>
    (w2n (i2w z : bytes32) <= w2n (n2w k : bytes32) <=>
     0 <= z /\ Num z <= k)
Proof
  rpt gen_tac >> strip_tac >>
  `k < dimword (:256)` by
    fs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  `w2n (n2w k : bytes32) = k` by simp[wordsTheory.w2n_n2w] >>
  Cases_on `0 <= z`
  >- (drule_all power_nonnegative_word_bound >> simp[]) >>
  `s` by
    (Cases_on `s` >> gvs[vyperValueTheory.within_int_bound_def]) >>
  gvs[] >>
  `w2i (i2w z : bytes32) = z` by
    metis_tac[vyperArithTheory.w2i_i2w_within_signed] >>
  `word_msb (i2w z : bytes32)` by
    (Cases_on `word_msb (i2w z : bytes32)` >>
     gvs[integer_wordTheory.w2i_def] >> intLib.ARITH_TAC) >>
  fs[wordsTheory.WORD_MSB_INT_MIN_LS, wordsTheory.WORD_LS,
     wordsTheory.word_L_def, wordsTheory.INT_MIN_def, wordsTheory.dimword_def,
     venomMemPropsTheory.dimindex_256, wordsTheory.w2n_n2w]
QED

(* Extend the literal-base threshold to every typed nonsmall base,
   including the signed minimum endpoint. *)
Theorem typed_literal_base_power_guard:
  !a bits signed k.
    1 < bits /\
    within_int_bound (if signed then Signed bits else Unsigned bits) a /\
    ~(a = -1 \/ a = 0 \/ a = 1) ==>
    (k <= (           if a < 0 /\ ODD ((largest_pow_exponent (Num (ABS a)) bits signed) + 1) /\
              Num (ABS a) ** ((largest_pow_exponent (Num (ABS a)) bits signed) + 1) = 2 ** (bits - if signed then 1 else 0)
           then (largest_pow_exponent (Num (ABS a)) bits signed) + 1 else (largest_pow_exponent (Num (ABS a)) bits signed)) <=>
     within_int_bound (if signed then Signed bits else Unsigned bits) (a ** k))
Proof
  rpt gen_tac >> strip_tac >>
  `2 <= ABS a` by
    (Cases_on `a < 0` >> simp[integerTheory.INT_ABS] >> intLib.ARITH_TAC) >>
  `2 <= Num (ABS a)` by intLib.ARITH_TAC >>
  Cases_on `signed`
  >- (gvs[] >>
      Cases_on `a = -&(2 ** (bits - 1))`
      >- (qspecl_then [`bits`, `k`] mp_tac signed_minimum_power_guard >>
          gvs[]) >>
      `Num (ABS a) < 2 ** (bits - 1)` by
        (Cases_on `a < 0` >>
         gvs[vyperValueTheory.within_int_bound_def, integerTheory.INT_ABS] >>
         intLib.ARITH_TAC) >>
      qspecl_then [`a`, `bits`, `k`] mp_tac signed_literal_base_power_guard >>
      simp[]) >>
  gvs[] >>
  `0 <= a` by gvs[vyperValueTheory.within_int_bound_def] >>
  `~(a < 0)` by intLib.ARITH_TAC >>
  `Num a < 2 ** bits` by gvs[vyperValueTheory.within_int_bound_def] >>
  qspecl_then [`a`, `bits`, `k`] mp_tac unsigned_literal_base_power_guard >>
  fs[integerTheory.INT_ABS]
QED

Theorem compile_safe_pow_base_run:
  !x y ty el a b sa op sb ss.
    0 < type_bits ty /\ type_bits ty <= 256 /\ type_bits ty MOD 8 = 0 /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) a /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) b /\
    compile_safe_pow x y ty (SOME a) el sa = (op,sb) /\
    fresh_vars_wrt sa ss /\ eval_operand x ss = SOME (i2w a) /\
    eval_operand y ss = SOME (i2w b) ==>
    (0 <= b /\ within_int_bound
       (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
       (a ** Num b) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
           eval_operand op ss' = SOME (i2w (a ** Num b))) /\
    (~(0 <= b /\ within_int_bound
       (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
       (a ** Num b)) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  rpt gen_tac >> strip_tac >>
  `1 < type_bits ty` by
    (Cases_on `type_bits ty < 2` >> simp[] >>
     `type_bits ty = 1` by decide_tac >> gvs[]) >>
  `0 <= b ==> word_exp (i2w a : bytes32) (i2w b) = i2w (a ** Num b)` by
    (strip_tac >> drule_all power_nonnegative_word_bound >> strip_tac >>
     irule word_exp_int_encoding >> simp[]) >>
  Cases_on `a = -1 \/ a = 0 \/ a = 1`
  >- (`within_int_bound
         (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
         (a ** Num b)` by
        (irule small_literal_base_power_bound >> simp[] >>
         Cases_on `is_signed_type ty` >>
         gvs[vyperValueTheory.within_int_bound_def]) >>
      qpat_x_assum `compile_safe_pow _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_safe_pow_def] >>
      Cases_on `is_signed_type ty` >> simp[]
      >- (simp[comp_ignore_bind_def, comp_bind_assoc] >> strip_tac >>
          drule_all (SRULE [comp_ignore_bind_def] nonnegative_guard_exp_run) >>
          `w2i (i2w b : bytes32) = b` by
            metis_tac[vyperArithTheory.w2i_i2w_within_signed] >>
          simp[] >> metis_tac[]) >>
      simp[comp_bind_def, comp_return_def] >> strip_tac >>
      drule_all assert_true_exp_run >>
      `0 <= b` by gvs[vyperValueTheory.within_int_bound_def] >>
      simp[]) >>
  qpat_x_assum `compile_safe_pow _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_safe_pow_def] >>
  qmatch_goalsub_abbrev_tac `Lit (n2w upper)` >> strip_tac >>
  `upper <= type_bits ty + 3` by
    (simp[Abbr `upper`] >>
     qspec_then `Num (ABS a)` (qspec_then `type_bits ty`
       (qspec_then `is_signed_type ty` assume_tac)) largest_pow_exponent_le >>
     IF_CASES_TAC >> decide_tac) >>
  `upper < 2 ** 255` by
    (qpat_x_assum `upper <= _` mp_tac >> simp[] >> decide_tac) >>
  `w2n (i2w b : bytes32) <= w2n (n2w upper : bytes32) <=>
   0 <= b /\ within_int_bound
      (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
      (a ** Num b)` by
    (drule_all power_exponent_word_guard >>
     strip_tac >> simp[] >>
     drule_all typed_literal_base_power_guard >>
     disch_then (qspec_then `Num b` mp_tac) >>
     simp[Abbr `upper`] >> metis_tac[]) >>
  drule_all upper_guard_exp_run >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem compile_safe_pow_exponent_run:
  !x y ty a b sa op sb ss.
    0 < type_bits ty /\ type_bits ty <= 256 /\ type_bits ty MOD 8 = 0 /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) a /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) b /\ 0 <= b /\
    compile_safe_pow x y ty NONE (SOME b) sa = (op,sb) /\
    fresh_vars_wrt sa ss /\ eval_operand x ss = SOME (i2w a) /\
    eval_operand y ss = SOME (i2w b) ==>
    (0 <= b /\ within_int_bound
       (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
       (a ** Num b) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
           eval_operand op ss' = SOME (i2w (a ** Num b))) /\
    (~(0 <= b /\ within_int_bound
       (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
       (a ** Num b)) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  rpt gen_tac >> strip_tac >>
  `1 < type_bits ty` by
    (Cases_on `type_bits ty < 2` >> simp[] >>
     `type_bits ty = 1` by decide_tac >> gvs[]) >>
  `word_exp (i2w a : bytes32) (i2w b) = i2w (a ** Num b)` by
    (drule_all power_nonnegative_word_bound >> strip_tac >>
     irule word_exp_int_encoding >> simp[]) >>
  Cases_on `Num b = 0 \/ Num b = 1`
  >- (`within_int_bound
         (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
         (a ** Num b)` by
        (`a ** 1 = a` by
           (CONV_TAC (LAND_CONV (RAND_CONV numLib.num_CONV)) >>
            simp[integerTheory.int_exp]) >>
         Cases_on `Num b = 0` >> fs[integerTheory.int_exp] >>
         Cases_on `is_signed_type ty` >>
         fs[vyperValueTheory.within_int_bound_def] >>
         `2 <= 2 ** (type_bits ty - 1)` by
           (irule arithmeticTheory.X_LE_X_EXP >> simp[]) >>
         `2 <= 2 ** type_bits ty` by
           (irule arithmeticTheory.X_LE_X_EXP >> simp[]) >> intLib.ARITH_TAC) >>
      qpat_x_assum `compile_safe_pow _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_safe_pow_def] >> strip_tac >>
      drule_all assert_true_exp_run >> simp[]) >>
  `0 < Num b` by decide_tac >>
  qpat_x_assum `compile_safe_pow _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_safe_pow_def] >>
  Cases_on `is_signed_type ty` >> simp[]
  >- (qmatch_goalsub_abbrev_tac `Lit (n2w upper)` >>
      qmatch_goalsub_abbrev_tac `Lit (i2w lower)` >> strip_tac >>
      `upper < 2 ** (type_bits ty - 1)` by
        (qspecl_then [`Num b`, `type_bits ty`, `T`] mp_tac
           largest_pow_base_lt_limit >> simp[Abbr `upper`]) >>
      `2 ** (type_bits ty - 1) <= 2 ** 255` by
        simp[arithmeticTheory.EXP_BASE_LE_MONO] >>
      `upper < 2 ** 255` by decide_tac >>
      `w2i (n2w upper : bytes32) = &upper` by
        (irule power_upper_word_signed >> simp[]) >>
      `w2i (i2w lower : bytes32) = lower` by
        (simp[Abbr `lower`] >> IF_CASES_TAC >>
         irule power_lower_word_signed >> decide_tac) >>
      `w2i (i2w a : bytes32) = a` by
        metis_tac[vyperArithTheory.w2i_i2w_within_signed] >>
      `ODD (type_bits ty - 1)` by
        (irule byte_width_signed_endpoint_odd >> simp[]) >>
      `lower <= a /\ a <= &upper <=>
       within_int_bound (Signed (type_bits ty)) (a ** Num b)` by
        (qspecl_then [`a`, `Num b`, `type_bits ty`] mp_tac
           signed_literal_exponent_power_guard >>
         simp[Abbr `lower`, Abbr `upper`] >>
         IF_CASES_TAC >> simp[]) >>
      drule_all signed_guard_exp_run >> asm_rewrite_tac[] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `Lit (n2w upper)` >> strip_tac >>
  `upper < 2 ** type_bits ty` by
    (qspecl_then [`Num b`, `type_bits ty`, `F`] mp_tac
       largest_pow_base_lt_limit >> simp[Abbr `upper`]) >>
  `2 ** type_bits ty <= 2 ** 256` by
    simp[arithmeticTheory.EXP_BASE_LE_MONO] >>
  `upper < 2 ** 256` by
    (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** type_bits ty` >> simp[]) >>
  `upper < dimword (:256)` by
    fs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  `0 <= a` by gvs[vyperValueTheory.within_int_bound_def] >>
  `w2n (i2w a : bytes32) = Num a` by
    metis_tac[power_nonnegative_word_bound] >>
  `w2n (n2w upper : bytes32) = upper` by simp[wordsTheory.w2n_n2w] >>
  `Num a <= upper <=>
   within_int_bound (Unsigned (type_bits ty)) (a ** Num b)` by
    (qspecl_then [`a`, `Num b`, `type_bits ty`] mp_tac
       unsigned_literal_exponent_power_guard >> simp[Abbr `upper`] >>
     `a = &(Num a)` by simp[] >> pop_assum SUBST1_TAC >> simp[]) >>
  drule_all upper_guard_exp_run >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem compile_safe_pow_run:
  !x y ty bl el a b sa op sb ss.
    0 < type_bits ty /\ type_bits ty <= 256 /\ type_bits ty MOD 8 = 0 /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) a /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) b /\
    (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
    (!n. bl = SOME n ==> a = n) /\ (!n. el = SOME n ==> b = n) /\
    compile_safe_pow x y ty bl el sa = (op,sb) /\
    fresh_vars_wrt sa ss /\ eval_operand x ss = SOME (i2w a) /\
    eval_operand y ss = SOME (i2w b) ==>
    (0 <= b /\ within_int_bound
       (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
       (a ** Num b) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
           eval_operand op ss' = SOME (i2w (a ** Num b))) /\
    (~(0 <= b /\ within_int_bound
       (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
       (a ** Num b)) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  rpt gen_tac >> disch_tac >> Cases_on `bl` >> gvs[]
  >- (drule_all compile_safe_pow_exponent_run >> simp[]) >>
  drule_all compile_safe_pow_base_run >> simp[] >> metis_tac[]
QED

(* Checked + - * / % on two integers of one type. *)
Theorem binop_frag_int_arith:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    MEM bop [Add; Sub; Mul; Div; Mod] /\ is_int_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  Cases_on `bop` >> fs[]
  >~ [`binop_frag _ _ _ _ Div`] >- (irule compile_divmod_sim >> simp[])
  >~ [`binop_frag _ _ _ _ Mod`] >- (irule compile_divmod_sim >> simp[]) >>
  irule compile_checked_sim >> simp[]
QED

(* A typed value of type decimal. *)
Theorem decimal_type_value:
  !tenv tv v.
    evaluate_type tenv (BaseT DecimalT) = SOME tv /\ value_has_type tv v ==>
    ?d. v = DecimalV d /\ within_int_bound (Signed 168) d
Proof
  rw[vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
QED

(* Checked + - * / % on two decimals. *)
Theorem binop_frag_decimal_arith:
  !ctx func cenv cx bop bl el tys v1 v2 es0 tenv tv.
    MEM bop [Add; Sub; Mul; Div; Mod] /\
    evaluate_type tenv (BaseT DecimalT) = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop (BaseT DecimalT) (BaseT DecimalT) bl el
      tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `tv`, `v1`] mp_tac decimal_type_value >>
  qspecl_then [`tenv`, `tv`, `v2`] mp_tac decimal_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  Cases_on `MEM bop [Mul; Div]`
  >- (irule compile_decimal_mul_div_sim >> simp[]) >>
  irule compile_decimal_add_sub_mod_sim >> simp[] >>
  Cases_on `bop` >> fs[]
QED

(* The wrapping operators on two integers of one type of a whole number of
   bytes. *)
Theorem binop_frag_unsafe_typed:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    is_int_type ty /\ type_bits ty MOD 8 = 0 /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  irule compile_unsafe_sim >> simp[]
QED

(* The comparisons, min and max on two word values of one type. *)
Theorem binop_frag_compare_typed:
  !ctx func cenv cx bop ty ann bl el tys v1 v2 es0 tenv tv.
    MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max] /\ word_value_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt strip_tac >>
  `word_value v1 /\ (is_uint256 ty <=> tv = BaseTV (UintT 256)) /\
   !m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
       m <= 256` by
    (qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac
       word_value_type_value_cases >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     gvs[word_value_def, is_uint256_def]) >>
  Cases_on `bop = Min \/ bop = Max`
  >- (irule compile_minmax_sim >> metis_tac[]) >>
  irule compile_compare_sim >> gvs[] >> metis_tac[]
QED

(* & | ^ on two word values of one type. *)
Theorem binop_frag_bitwise_typed:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    (bop = And \/ bop = Or \/ bop = XOr) /\ word_value_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> irule compile_bitwise_sim >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac word_value_type_value_cases >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac word_value_type_value_cases >>
  asm_rewrite_tac[] >> rpt strip_tac >> gvs[type_to_int_bound_def]
QED

(* Flag membership on two flags of one type. *)
Theorem binop_frag_flag_in_typed:
  !ctx func cenv cx bop nsid ty ann bl el tys v1 v2 es0 tenv tv.
    (bop = In \/ bop = NotIn) /\
    evaluate_type tenv (FlagT nsid) = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  irule compile_flag_in_sim >> metis_tac[]
QED

(* A non-negative integer within the bound of an integer type of at most
   256 bits is a uint256. *)
Theorem within_int_bound_unsigned_256:
  !u n i.
    (u = Unsigned n \/ u = Signed n) /\ n <= 256 /\ within_int_bound u i /\
    0 <= i ==>
    within_int_bound (Unsigned 256) i
Proof
  rpt strip_tac >>
  `?k. i = &k` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >>
  `k < 2 ** n` by
    (gvs[vyperValueTheory.within_int_bound_def] >> Cases_on `0 < n` >>
     gvs[] >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** (n - 1)` >> simp[arithmeticTheory.EXP_BASE_LE_MONO]) >>
  `2 ** n <= 2 ** 256` by
    (irule arithmeticTheory.EXP_BASE_LEQ_MONO_IMP >> simp[]) >>
  `k < 2 ** 256` by decide_tac >>
  pop_assum mp_tac >> simp[vyperValueTheory.within_int_bound_def]
QED

(* << and >> on a 256-bit integer by a non-negative amount. *)
Theorem binop_frag_shift_typed:
  !ctx func cenv cx bop ty t2 bl el tys v1 v2 es0 tenv tv1 tv2 i2.
    (bop = ShL \/ bop = ShR) /\ is_int_type ty /\ type_bits ty = 256 /\
    is_int_type t2 /\ v2 = IntV i2 /\ 0 <= i2 /\
    evaluate_type tenv ty = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `ty`, `tv1`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `t2`, `tv2`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `within_int_bound (Unsigned 256) i2` by
    (Cases_on `is_signed_type t2` >> fs[] >>
     metis_tac[within_int_bound_unsigned_256]) >>
  irule compile_shift_sim >> gvs[]
QED

(* Power guards reflect source bounds when literal metadata agrees with
   the typed operands.  A base literal or nonnegative exponent literal is
   required; the emitted ASSERT rejects negative exponents and overflow. *)
Theorem binop_frag_pow:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    bop = Exp /\ well_typed_binop ann bop t1 t2 /\
    (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
    (!n. bl = SOME n ==> v1 = IntV n) /\
    (!n. el = SOME n ==> v2 = IntV n) /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> disch_tac >>
  `is_int_type t1 /\ is_int_type t2` by gvs[well_typed_binop_def] >>
  qspecl_then [`tenv`, `t1`, `tv1`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `t2`, `tv2`, `v2`] mp_tac int_type_value >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (impl_tac >- gvs[]) >> strip_tac >>
  gvs[well_typed_binop_def] >>
  (rename1 `binop_frag _ _ _ _ Exp _ _ _ _ _ (IntV a) (IntV b) _` >>
  `type_bits ann MOD 8 = 0` by metis_tac[int_type_byte_width] >>

  drule_then assume_tac bop_result_power >>
  irule binop_frag_straight >> conj_tac
  >- simp[compile_binop_def, straight_fresh_compile_safe_pow] >>
  simp[] >>
  Cases_on `b < 0`
  >- (simp[] >> strip_tac >>
      rpt gen_tac >> simp[compile_binop_def, valueEncodingTheory.val_to_w256_def] >> strip_tac >>
      drule_at (Pat `compile_safe_pow _ _ _ _ _ _ = _`) compile_safe_pow_run >> simp[] >>
      `~(0 <= b)` by intLib.ARITH_TAC >> metis_tac[]) >>
  Cases_on `within_int_bound
    (if is_signed_type ann then Signed (type_bits ann) else Unsigned (type_bits ann))
    (a ** Num b)`
  >- (simp[word_value_def] >> strip_tac >> rpt gen_tac >>
      simp[compile_binop_def, valueEncodingTheory.val_to_w256_def] >> strip_tac >>
      drule_at (Pat `compile_safe_pow _ _ _ _ _ _ = _`) compile_safe_pow_run >> simp[] >>
      `0 <= b` by intLib.ARITH_TAC >> metis_tac[]) >>
  simp[] >> strip_tac >>
  rpt gen_tac >> simp[compile_binop_def, valueEncodingTheory.val_to_w256_def] >> strip_tac >>
  drule_at (Pat `compile_safe_pow _ _ _ _ _ _ = _`) compile_safe_pow_run >> simp[] >> metis_tac[])
QED

(* Right-shift arithmetic at genuinely narrow widths, independent of any
   checker restriction: signed and unsigned encodings widen safely to 256 bits. *)
Theorem binop_frag_shr_narrow:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    bop = ShR /\ type_bits t1 < 256 /\ ~(?i. v2 = IntV i /\ i < 0) /\
    ann = t1 /\ is_int_type t1 /\ is_int_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qspecl_then [`tenv`, `ann`, `tv1`, `v1`] mp_tac int_type_value >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`tenv`, `t2`, `tv2`, `v2`] mp_tac int_type_value >>
  (impl_tac >- simp[]) >> strip_tac >>
  gvs[] >>
  rename1 `value_has_type tv2 (IntV i2)` >>
  `0 <= i2` by intLib.ARITH_TAC >>
  `within_int_bound (Unsigned 256) i2` by
    (Cases_on `is_signed_type t2` >> fs[] >>
     metis_tac[within_int_bound_unsigned_256]) >>
  `type_bits ann <= 256` by decide_tac >>
  `?v. bop_result cx ann ShR tys (IntV i) (IntV i2) es0 = INL v /\
       word_value v /\ val_to_w256 v =
         (if is_signed_type ann
          then word_asr (val_to_w256 (IntV i)) (w2n (val_to_w256 (IntV i2)))
          else word_lsr (val_to_w256 (IntV i)) (w2n (val_to_w256 (IntV i2))))` by
    (irule bop_result_shr >> simp[] >>
     qexists_tac `type_bits ann` >> simp[]) >>
  irule binop_frag_straight >>
  (conj_tac >- metis_tac[straight_fresh_compile_shift]) >>
  disch_tac >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`) compile_shift_run >>
  disch_then (qspecl_then [`ss`, `val_to_w256 (IntV i)`, `val_to_w256 (IntV i2)`] mp_tac) >>
  simp[]
QED

(* Accepted shifts retain the nonnegative evaluated amount.  ShL is
   full-width; ShR also uses the independently proved narrow arithmetic. *)
Theorem binop_frag_shift_572:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    (bop = ShL \/ bop = ShR) /\ (?i. v2 = IntV i /\ 0 <= i) /\
    well_typed_binop ann bop t1 t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> gvs[well_typed_binop_def]
  >- (irule binop_frag_shift_typed >> simp[is_int_type_def, type_bits_def] >>
      metis_tac[])
  >- (irule binop_frag_shift_typed >> simp[is_int_type_def, type_bits_def] >>
      metis_tac[]) >>
  `type_bits ann <= 256` by
    (qspecl_then [`tenv`, `ann`, `tv1`, `v1`] mp_tac int_type_value >>
     simp[] >> metis_tac[]) >>
  Cases_on `type_bits ann = 256`
  >- (irule binop_frag_shift_typed >> simp[] >> metis_tac[]) >>
  irule binop_frag_shr_narrow >> simp[] >>
  `type_bits ann < 256` by decide_tac >> metis_tac[integerTheory.INT_NOT_LE]
QED

(* Instantiates a dispatch lemma at the current goal's variables and
   discharges its premises from the assumptions. *)
fun binop_dispatch_tac th =
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ann`, `t1`, `t2`, `bl`,
               `el`, `tys`, `v1`, `v2`, `es0`, `tenv`, `tv1`, `tv2`]
    mp_tac th >>
  impl_tac >- (asm_rewrite_tac[] >> Cases_on `bop` >> fs[]) >>
  simp[];

(* Each operator on typed operands of word_value_types, by its group. *)
Theorem binop_frag_arith_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    MEM bop [Add; Sub; Mul; Div; Mod] /\ well_typed_binop ann bop t1 t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  `t1 = ann /\ t2 = ann /\ is_numeric_type ann` by
    (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
  qpat_x_assum `t1 = ann` SUBST_ALL_TAC >>
  qpat_x_assum `t2 = ann` SUBST_ALL_TAC >>
  `tv2 = tv1` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  Cases_on `ann = BaseT DecimalT`
  >- (pop_assum SUBST_ALL_TAC >> irule binop_frag_decimal_arith >>
      metis_tac[]) >>
  irule binop_frag_int_arith >> gvs[] >> metis_tac[]
QED

Theorem binop_frag_unsafe_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    well_typed_binop ann bop t1 t2 /\ type_bits t1 MOD 8 = 0 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  `t1 = ann /\ t2 = ann /\ is_int_type ann` by
    (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
  qpat_x_assum `t1 = ann` SUBST_ALL_TAC >>
  qpat_x_assum `t2 = ann` SUBST_ALL_TAC >>
  `tv2 = tv1` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  irule binop_frag_unsafe_typed >> metis_tac[]
QED

Theorem binop_frag_shift_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    (bop = ShL \/ bop = ShR) /\ well_typed_binop ann bop t1 t2 /\
    (?i. v2 = IntV i /\ 0 <= i) /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  binop_dispatch_tac binop_frag_shift_572
QED

Theorem binop_frag_in_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    (bop = In \/ bop = NotIn) /\ well_typed_binop ann bop t1 t2 /\
    word_value_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  `?nsid. t1 = FlagT nsid /\ t2 = FlagT nsid` by
    (Cases_on `t2` >> gvs[well_typed_binop_def, word_value_type_def]) >>
  gvs[] >> irule binop_frag_flag_in_typed >> metis_tac[]
QED

Theorem binop_frag_rest_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    MEM bop [And; Or; XOr; Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max] /\
    well_typed_binop ann bop t1 t2 /\ word_value_type t1 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  `t2 = t1` by
    (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
  qpat_x_assum `t2 = t1` SUBST_ALL_TAC >>
  `tv2 = tv1` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  Cases_on `bop = And \/ bop = Or \/ bop = XOr`
  >- (`ann = t1` by
        (qpat_x_assum `bop = _ \/ _` strip_assume_tac >>
         gvs[well_typed_binop_def]) >>
      pop_assum SUBST_ALL_TAC >>
      qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `t1`, `bl`, `el`, `tys`,
                   `v1`, `v2`, `es0`, `tenv`, `tv1`]
        mp_tac binop_frag_bitwise_typed >>
      impl_tac >- asm_rewrite_tac[] >> simp[]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `t1`, `ann`, `bl`, `el`,
               `tys`, `v1`, `v2`, `es0`, `tenv`, `tv1`]
    mp_tac binop_frag_compare_typed >>
  impl_tac >- (asm_rewrite_tac[] >> Cases_on `bop` >> fs[]) >> simp[]
QED

Theorem binop_frag_word_typed:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    well_typed_binop ann bop t1 t2 /\ type_bits t1 MOD 8 = 0 /\
    (bop = Exp ==>
      (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
      (!n. bl = SOME n ==> v1 = IntV n) /\
      (!n. el = SOME n ==> v2 = IntV n)) /\
    (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
    word_value_type t1 /\ word_value_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `bop = ExpMod` >- gvs[well_typed_binop_def] >>
  Cases_on `bop = Exp`
  >- binop_dispatch_tac binop_frag_pow >>
  Cases_on `MEM bop [Add; Sub; Mul; Div; Mod]`
  >- binop_dispatch_tac binop_frag_arith_any >>
  Cases_on `MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv]`
  >- binop_dispatch_tac binop_frag_unsafe_any >>
  Cases_on `bop = ShL \/ bop = ShR`
  >- binop_dispatch_tac binop_frag_shift_any >>
  Cases_on `bop = In \/ bop = NotIn`
  >- binop_dispatch_tac binop_frag_in_any >>
  binop_dispatch_tac binop_frag_rest_any
QED

Theorem binop_frag_typed:
  !ctx func cenv cx bop ann e1 e2 v1 v2 es0 tv1 tv2.
    well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
    (bop = Exp ==>
      IS_SOME (expr_int_literal e1) \/
      ?n. expr_int_literal e2 = SOME n /\ 0 <= n) /\
    (!n. expr_int_literal e1 = SOME n ==> v1 = IntV n) /\
    (!n. expr_int_literal e2 = SOME n ==> v2 = IntV n) /\
    (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
    type_bits (expr_type e1) MOD 8 = 0 /\
    word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    value_has_type tv1 v1 /\
    evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
    value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop (expr_type e1) ann
      (if bop = Exp then expr_int_literal e1 else NONE)
      (if bop = Exp then expr_int_literal e2 else NONE)
      [expr_type e1; expr_type e2] v1 v2 es0
Proof
  rpt strip_tac >>
  irule binop_frag_word_typed >>
  Cases_on `bop = Exp` >> gvs[] >> metis_tac[]
QED
