(*
 * rangeEvalProofsLib.sml
 *
 * Bridge lemmas for signed integer word operations (quot).
 * Proved as SML vals to avoid Theory format issues with
 * nested >- and ARITH_TAC on nonlinear terms.
 *
 * Exported: w2i_word_quot, abs_lt_neg_min_gives_range
 *)
structure rangeEvalProofsLib :> sig
  val w2i_word_quot : Thm.thm
  val w2i_word_rem : Thm.thm
  val abs_lt_neg_min_gives_range : Thm.thm
  val sdiv_overflow : Thm.thm
  val quot_sign_abs : Thm.thm
  val quot_mono_pos_denom : Thm.thm
  val neg_quot_eq : Thm.thm
  val nonneg_quot_eq : Thm.thm
end = struct

open HolKernel boolLib bossLib;
open integerTheory integer_wordTheory wordsTheory;
open intLib fcpLib;
open valueRangeDefsTheory;

val dim256 = fcpLib.INDEX_CONV ``dimindex(:256)``;

val w2i_le_256 = INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_le
  |> REWRITE_RULE [GSYM INT256_MAX_def];
val w2i_ge_256 = INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_ge
  |> REWRITE_RULE [GSYM INT256_MIN_def];
val w2i_i2w_256 =
  INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_i2w
  |> REWRITE_RULE [GSYM INT256_MIN_def, GSYM INT256_MAX_def];

(* Concrete expansions of INT256_MIN/MAX for converting int↔nat *)
val INT256_MIN_concrete = SIMP_CONV (srw_ss())
  [INT256_MIN_def, wordsTheory.INT_MIN_def, dim256] ``INT256_MIN``;
val INT256_MAX_concrete = SIMP_CONV (srw_ss())
  [INT256_MAX_def, integer_wordTheory.INT_MAX_def,
   wordsTheory.INT_MIN_def, dim256] ``INT256_MAX``;

(* Rewrite rules for converting int inequalities to nat *)
val int_to_nat_rwts = [INT_LE, INT_LE_NEG, INT_EQ_NEG, INT_INJ];

(* --- quot_to_nat reduction: signed quot → nat DIV --- *)
val quot_nat = CONJUNCT1 INT_QUOT_CALCULATE;
val quot_neg = CONJUNCT1 (CONJUNCT2 INT_QUOT_CALCULATE);

val quot_to_nat_pp = prove(
  ``!m n. 0 < n ==> &m quot &n = &(m DIV n)``,
  rpt strip_tac >> `&n <> 0i` by intLib.ARITH_TAC >> simp[quot_nat]);
val quot_to_nat_pn = prove(
  ``!m n. 0 < n ==> &m quot -&n = -&(m DIV n)``,
  rpt strip_tac >> `&n <> 0i` by intLib.ARITH_TAC >>
  mp_tac (Q.SPECL [`&m`, `&n`] quot_neg) >> simp[] >> strip_tac >>
  simp[quot_nat]);
val quot_to_nat_np = prove(
  ``!m n. 0 < n ==> -&m quot &n = -&(m DIV n)``,
  rpt strip_tac >> `&n <> 0i` by intLib.ARITH_TAC >>
  mp_tac (Q.SPECL [`&m`, `&n`] quot_neg) >> simp[] >> strip_tac >>
  simp[quot_nat]);
val quot_to_nat_nn = prove(
  ``!m n. 0 < n ==> -&m quot -&n = &(m DIV n)``,
  rpt strip_tac >> `&n <> 0i` by intLib.ARITH_TAC >>
  mp_tac (Q.SPECL [`&m`, `&n`] quot_neg) >> simp[] >> strip_tac >>
  `- -&n = &n` by intLib.ARITH_TAC >>
  ASM_REWRITE_TAC[] >> simp[quot_nat]);

(* Tactic: case-split w2i into &m or -&m form *)
fun w2i_nat_tac wt =
  Cases_on `0 <= ^wt` >| [
    `?m. ^wt = &m` by (qexists_tac `Num(^wt)` >> simp[INT_OF_NUM]),
    `^wt < 0` by intLib.ARITH_TAC >>
    `?m. ^wt = -&m /\ 0 < m` by (
      qexists_tac `Num(-( ^wt ))` >>
      simp[INT_OF_NUM] >> intLib.ARITH_TAC)
  ];

(* --- Lower bound: quot result ≥ INT256_MIN --- *)
val w2i_quot_lower = prove(
  ``!a:256 word b:256 word.
    w2i b <> 0 ==> INT256_MIN <= w2i a quot w2i b``,
  rpt strip_tac >>
  w2i_nat_tac ``w2i (a:256 word)`` >> w2i_nat_tac ``w2i (b:256 word)`` >>
  gvs[] >| [
    (* pp: &(m DIV m') ≥ 0 ≥ MIN *)
    `0 < m'` by intLib.ARITH_TAC >>
    simp[quot_to_nat_pp, INT256_MIN_concrete],
    (* pn: -&(m DIV m') ≥ MIN *)
    simp[quot_to_nat_pn] >>
    `m DIV m' <= m` by (irule arithmeticTheory.DIV_LESS_EQ >> DECIDE_TAC) >>
    mp_tac (Q.SPEC `a` w2i_le_256) >> gvs[] >>
    REWRITE_TAC[INT256_MIN_concrete, INT256_MAX_concrete] >>
    REWRITE_TAC int_to_nat_rwts >> DECIDE_TAC,
    (* np: -&(m DIV m') ≥ MIN *)
    `0 < m'` by intLib.ARITH_TAC >> simp[quot_to_nat_np] >>
    `m DIV m' <= m` by (irule arithmeticTheory.DIV_LESS_EQ >> DECIDE_TAC) >>
    mp_tac (Q.SPEC `a` w2i_ge_256) >> gvs[] >>
    REWRITE_TAC[INT256_MIN_concrete] >> REWRITE_TAC int_to_nat_rwts >> DECIDE_TAC,
    (* nn: &(m DIV m') ≥ 0 ≥ MIN *)
    simp[quot_to_nat_nn, INT256_MIN_concrete]
  ]);

(* --- Upper bound: quot result ≤ INT256_MAX (excluding overflow) --- *)
val w2i_quot_upper = prove(
  ``!a:256 word b:256 word.
    w2i b <> 0 /\ ~(w2i a = INT256_MIN /\ w2i b = -1) ==>
    w2i a quot w2i b <= INT256_MAX``,
  rpt gen_tac >> strip_tac >>
  w2i_nat_tac ``w2i (a:256 word)`` >> w2i_nat_tac ``w2i (b:256 word)`` >>
  gvs[] >| [
    (* pp: &(m DIV m') ≤ &m ≤ MAX *)
    `0 < m'` by intLib.ARITH_TAC >> simp[quot_to_nat_pp] >>
    `m DIV m' <= m` by (irule arithmeticTheory.DIV_LESS_EQ >> DECIDE_TAC) >>
    mp_tac (Q.SPEC `a` w2i_le_256) >> simp[] >>
    REWRITE_TAC[INT256_MAX_concrete, INT_LE] >> DECIDE_TAC,
    (* pn: -&(m DIV m') ≤ 0 ≤ MAX *)
    simp[quot_to_nat_pn, INT256_MAX_concrete],
    (* np: -&(m DIV m') ≤ 0 ≤ MAX *)
    `0 < m'` by intLib.ARITH_TAC >>
    simp[quot_to_nat_np, INT256_MAX_concrete],
    (* nn: &(m DIV m') ≤ MAX *)
    simp[quot_to_nat_nn] >>
    (* Get m ≤ 2^255 *)
    `m <= 57896044618658097711785492504343953926634992332820282019728792003956564819968` by (
      mp_tac (Q.SPEC `a` w2i_ge_256) >> simp[] >>
      REWRITE_TAC[INT256_MIN_concrete] >> REWRITE_TAC int_to_nat_rwts >> DECIDE_TAC) >>
    Cases_on `m = 0` >- simp[INT256_MAX_concrete] >>
    Cases_on `m' >= 2` >- (
      `m DIV m' < m` by (irule arithmeticTheory.DIV_LESS >> DECIDE_TAC) >>
      REWRITE_TAC[INT256_MAX_concrete, INT_LE] >> DECIDE_TAC) >>
    (* m'=1: b=-1, precond gives a ≠ MIN, so m ≠ 2^255, m < 2^255 *)
    `m' = 1` by DECIDE_TAC >> simp[arithmeticTheory.DIV_1] >>
    `m <> 57896044618658097711785492504343953926634992332820282019728792003956564819968` by (
      strip_tac >> fs[INT256_MIN_concrete] >> intLib.ARITH_TAC) >>
    REWRITE_TAC[INT256_MAX_concrete, INT_LE] >> DECIDE_TAC
  ]);

(* --- Helper: word precondition → integer precondition --- *)
val check = prove(``integer_word$INT_MIN(:256) = INT256_MIN``,
  simp[integer_wordTheory.INT_MIN_def, INT256_MIN_def, INT256_MAX_def,
       integer_wordTheory.INT_MAX_def, wordsTheory.INT_MIN_def, dim256]);

val i2w_neg1 = prove(``w2i (i2w (-1) : 256 word) = -1``,
  match_mp_tac (INST_TYPE [alpha |-> ``:256``] w2i_i2w) >>
  simp[wordsTheory.INT_MIN_def, integer_wordTheory.INT_MIN_def,
       integer_wordTheory.INT_MAX_def, dim256]);

val word_to_int_precond = prove(
  ``!(a:256 word) (b:256 word).
    ~(a = INT_MINw /\ b = i2w (-1)) ==>
    ~(w2i a = INT256_MIN /\ w2i b = -1)``,
  rpt strip_tac >>
  `a = INT_MINw` by metis_tac[w2i_11, w2i_INT_MINw, check] >>
  `b = i2w(-1)` by metis_tac[w2i_11, i2w_neg1] >>
  metis_tac[]);

(* --- Main theorem: w2i(a / b) = w2i a quot w2i b --- *)
val w2i_word_quot = prove(
  ``!a:256 word b:256 word.
    b <> 0w /\ ~(a = INT_MINw /\ b = i2w (-1)) ==>
    w2i (a / b) = w2i a quot w2i b``,
  rpt strip_tac >>
  `w2i b <> 0` by (strip_tac >> fs[w2i_eq_0]) >>
  `~(w2i a = INT256_MIN /\ w2i b = -1)` by metis_tac[word_to_int_precond] >>
  `a / b = i2w (w2i a quot w2i b)` by (
    mp_tac (INST_TYPE [alpha |-> ``:256``] word_quot) >>
    disch_then (qspecl_then [`a`, `b`] mp_tac) >> simp[]) >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  match_mp_tac w2i_i2w_256 >>
  conj_tac >| [
    match_mp_tac (REWRITE_RULE [AND_IMP_INTRO] w2i_quot_lower) >> simp[],
    match_mp_tac (REWRITE_RULE [AND_IMP_INTRO] w2i_quot_upper) >>
    ASM_REWRITE_TAC[]
  ]);

(* ABS x < -INT256_MIN implies x is in representable range *)
val abs_lt_neg_min_gives_range = prove(
  ``!x:int. ABS x < -INT256_MIN ==> INT256_MIN <= x /\ x <= INT256_MAX``,
  rpt strip_tac >> pop_assum mp_tac >>
  REWRITE_TAC[integerTheory.INT_ABS_LT] >>
  simp[INT256_MIN_def, INT256_MAX_def, integer_wordTheory.INT_MIN_def,
       integer_wordTheory.INT_MAX_def, wordsTheory.INT_MIN_def, dim256] >>
  intLib.ARITH_TAC
);

(* w2i bounds: |w2i b| <= -INT256_MIN for any 256-bit word *)
val w2i_abs_le_neg_min = prove(
  ``!b:256 word. ABS (w2i b) <= -INT256_MIN``,
  gen_tac >>
  mp_tac (Q.SPEC `b` w2i_ge_256) >> mp_tac (Q.SPEC `b` w2i_le_256) >>
  REWRITE_TAC[INT256_MIN_def, INT256_MAX_def, integer_wordTheory.INT_MIN_def,
              integer_wordTheory.INT_MAX_def, wordsTheory.INT_MIN_def, dim256] >>
  REWRITE_TAC[integerTheory.INT_ABS] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> intLib.ARITH_TAC);

(* --- Main theorem: w2i(word_rem a b) = w2i a rem w2i b --- *)
(* Simpler than quot: no overflow exception needed.
   |a rem b| < |b| <= 2^255 = -INT256_MIN, so result always in range. *)
val rem_abs_bound = prove(
  ``!a b:int. b <> 0 ==> ABS (a rem b) < ABS b``,
  rpt strip_tac >>
  mp_tac (Q.SPEC `b` INT_REMQUOT) >> ASM_REWRITE_TAC[] >>
  disch_then (qspec_then `a` strip_assume_tac) >> simp[]);

val w2i_word_rem = prove(
  ``!a:256 word b:256 word.
    b <> 0w ==> w2i (word_rem a b) = w2i a rem w2i b``,
  rpt strip_tac >>
  `w2i b <> 0` by (strip_tac >> fs[w2i_eq_0]) >>
  `word_rem a b = i2w (w2i a rem w2i b)` by (
    mp_tac (INST_TYPE [alpha |-> ``:256``] word_rem) >>
    disch_then (qspecl_then [`a`, `b`] mp_tac) >> simp[]) >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  match_mp_tac w2i_i2w_256 >>
  match_mp_tac abs_lt_neg_min_gives_range >>
  irule integerTheory.INT_LTE_TRANS >>
  qexists_tac `ABS (w2i b)` >>
  simp[rem_abs_bound, w2i_abs_le_neg_min]);

(* --- quot relates to sign * (ABS/ABS) --- *)
val quot_eq_div_nonneg = prove(
  ``!a b. 0 <= a /\ 0 < b ==> a quot b = a / b``,
  rpt strip_tac >>
  `?m. a = &m` by (qexists_tac `Num a` >> simp[INT_OF_NUM]) >>
  `?n. b = &n /\ 0 < n` by (qexists_tac `Num b` >> simp[INT_OF_NUM] >> intLib.ARITH_TAC) >>
  gvs[] >> `&n <> 0i` by intLib.ARITH_TAC >> simp[INT_QUOT, INT_DIV]);

val quot_sign_abs = prove(
  ``!a b. b <> 0 ==>
    a quot b = (if (a < 0) <> (b < 0) then -1 else 1) * (ABS a / ABS b)``,
  rpt strip_tac >>
  Cases_on `0 <= a` >> Cases_on `0 < b` >| [
    `?m. a = &m` by (qexists_tac `Num a` >> simp[INT_OF_NUM]) >>
    `?n. b = &n /\ 0 < n` by (qexists_tac `Num b` >> simp[INT_OF_NUM] >> intLib.ARITH_TAC) >>
    gvs[INT_ABS_NUM, INT_QUOT, INT_DIV],
    `b < 0` by intLib.ARITH_TAC >>
    `?m. a = &m` by (qexists_tac `Num a` >> simp[INT_OF_NUM]) >>
    `?n. b = -&n /\ 0 < n` by (qexists_tac `Num(-b)` >> simp[INT_OF_NUM] >> intLib.ARITH_TAC) >>
    gvs[INT_ABS_NUM, INT_ABS_NEG] >> `&n <> 0i` by intLib.ARITH_TAC >>
    simp[CONJUNCT1 (CONJUNCT2 INT_QUOT_CALCULATE), INT_QUOT, INT_DIV] >> intLib.ARITH_TAC,
    `a < 0` by intLib.ARITH_TAC >>
    `?m. a = -&m /\ 0 < m` by (qexists_tac `Num(-a)` >> simp[INT_OF_NUM] >> intLib.ARITH_TAC) >>
    `?n. b = &n /\ 0 < n` by (qexists_tac `Num b` >> simp[INT_OF_NUM] >> intLib.ARITH_TAC) >>
    gvs[INT_ABS_NUM, INT_ABS_NEG] >> `&n <> 0i` by intLib.ARITH_TAC >>
    simp[CONJUNCT1 (CONJUNCT2 INT_QUOT_CALCULATE), INT_QUOT, INT_DIV] >> intLib.ARITH_TAC,
    `a < 0 /\ b < 0` by intLib.ARITH_TAC >>
    `?m. a = -&m /\ 0 < m` by (qexists_tac `Num(-a)` >> simp[INT_OF_NUM] >> intLib.ARITH_TAC) >>
    `?n. b = -&n /\ 0 < n` by (qexists_tac `Num(-b)` >> simp[INT_OF_NUM] >> intLib.ARITH_TAC) >>
    gvs[INT_ABS_NUM, INT_ABS_NEG] >> `&n <> 0i` by intLib.ARITH_TAC >>
    simp[CONJUNCT1 (CONJUNCT2 INT_QUOT_CALCULATE), INT_QUOT, INT_DIV] >> intLib.ARITH_TAC
  ]);

(* int_div helpers (self-contained, no Script dependencies) *)
val int_div_le_mono_lib = prove(
  ``!m x y:int. 0 < m /\ x <= y ==> x / m <= y / m``,
  rpt strip_tac >> SPOSE_NOT_THEN ASSUME_TAC >>
  `y / m + 1 <= x / m` by intLib.ARITH_TAC >>
  `m <> 0i` by intLib.ARITH_TAC >>
  mp_tac (Q.SPEC `m` INT_DIVISION) >> ASM_REWRITE_TAC[] >>
  disch_then (fn th =>
    assume_tac (Q.SPEC `x` th) >> assume_tac (Q.SPEC `y` th)) >>
  `~(m < 0)` by intLib.ARITH_TAC >> fs[] >>
  `m * (y / m + 1) <= m * (x / m)` by fs[INT_LE_MONO] >>
  intLib.ARITH_TAC);

val int_div_nonneg_lib = prove(
  ``!x m:int. 0 <= x /\ 0 < m ==> 0 <= x / m``,
  rpt strip_tac >> SPOSE_NOT_THEN ASSUME_TAC >>
  `m <> 0i` by intLib.ARITH_TAC >>
  mp_tac (Q.SPEC `m` INT_DIVISION) >> ASM_REWRITE_TAC[] >>
  disch_then (qspec_then `x` strip_assume_tac) >>
  `~(m < 0)` by intLib.ARITH_TAC >> fs[] >>
  `x / m <= -1` by intLib.ARITH_TAC >>
  `m * (x / m) <= m * -1` by simp[INT_LE_MONO] >>
  intLib.ARITH_TAC);

(* quot is monotone in dividend for positive divisor *)
val quot_mono_pos_denom = prove(
  ``!a b (d:int). 0 < d /\ a <= b ==> a quot d <= b quot d``,
  rpt strip_tac >> `d <> 0` by intLib.ARITH_TAC >>
  Cases_on `0 <= a` >| [
    `0 <= b` by intLib.ARITH_TAC >>
    simp[quot_eq_div_nonneg] >> irule int_div_le_mono_lib >> simp[],
    `a < 0` by intLib.ARITH_TAC >>
    Cases_on `0 <= b` >| [
      simp[quot_eq_div_nonneg] >>
      `a quot d <= 0` by (
        `?m. a = -&m /\ 0 < m` by (qexists_tac `Num(-a)` >> simp[INT_OF_NUM] >> intLib.ARITH_TAC) >>
        `?n. d = &n /\ 0 < n` by (qexists_tac `Num d` >> simp[INT_OF_NUM] >> intLib.ARITH_TAC) >>
        gvs[] >> `&n <> 0i` by intLib.ARITH_TAC >>
        simp[CONJUNCT1 (CONJUNCT2 INT_QUOT_CALCULATE), INT_QUOT]) >>
      mp_tac (Q.SPECL [`b`, `d`] int_div_nonneg_lib) >> simp[] >> intLib.ARITH_TAC,
      `b < 0` by intLib.ARITH_TAC >>
      `?m1. a = -&m1 /\ 0 < m1` by (qexists_tac `Num(-a)` >> simp[INT_OF_NUM] >> intLib.ARITH_TAC) >>
      `?m2. b = -&m2 /\ 0 < m2` by (qexists_tac `Num(-b)` >> simp[INT_OF_NUM] >> intLib.ARITH_TAC) >>
      `?n. d = &n /\ 0 < n` by (qexists_tac `Num d` >> simp[INT_OF_NUM] >> intLib.ARITH_TAC) >>
      gvs[] >> `&n <> 0i` by intLib.ARITH_TAC >>
      simp[CONJUNCT1 (CONJUNCT2 INT_QUOT_CALCULATE), INT_QUOT] >>
      `m2 <= m1` by intLib.ARITH_TAC >>
      mp_tac (Q.SPECL [`n`, `m2`, `m1`] arithmeticTheory.DIV_LE_MONOTONE) >> simp[] >>
      intLib.ARITH_TAC
    ]
  ]);

(* Helpers relating quot to definition's ABS formulation *)
val neg_quot_eq = prove(
  ``!a d. a < 0 /\ 0 < d ==> a quot d = -(ABS a / d)``,
  rpt strip_tac >> `d <> 0` by intLib.ARITH_TAC >>
  `?m. a = -&m /\ 0 < m` by (qexists_tac `Num(-a)` >> simp[INT_OF_NUM] >> intLib.ARITH_TAC) >>
  `?n. d = &n /\ 0 < n` by (qexists_tac `Num d` >> simp[INT_OF_NUM] >> intLib.ARITH_TAC) >>
  gvs[INT_ABS_NEG, INT_ABS_NUM] >> `&n <> 0i` by intLib.ARITH_TAC >>
  simp[CONJUNCT1 (CONJUNCT2 INT_QUOT_CALCULATE), INT_QUOT, INT_DIV]);

val nonneg_quot_eq = prove(
  ``!a d. 0 <= a /\ 0 < d ==> a quot d = a / d``,
  rpt strip_tac >> simp[quot_eq_div_nonneg]);

(* sdiv overflow: INT_MINw / i2w(-1) wraps back to INT_MINw *)
val w2i_i2w_neg1 = prove(``w2i (i2w (-1) : 256 word) = -1``,
  mp_tac (INST_TYPE [alpha |-> ``:256``] w2i_i2w) >>
  simp[wordsTheory.INT_MIN_def, INT_MIN_def, INT_MAX_def, dim256] >>
  intLib.ARITH_TAC);
val check = prove(``integer_word$INT_MIN(:256) = INT256_MIN``,
  simp[INT_MIN_def, INT256_MIN_def, INT256_MAX_def, INT_MAX_def,
       wordsTheory.INT_MIN_def, dim256]);
val neg_INT256_MIN = prove(``-INT256_MIN = &(words$INT_MIN(:256))``,
  simp[INT256_MIN_def, wordsTheory.INT_MIN_def, dim256]);
val sdiv_overflow = prove(
  ``w2i (INT_MINw / i2w (-1) : 256 word) = INT256_MIN``,
  `i2w (-1) <> (0w:256 word)` by (
    strip_tac >> mp_tac w2i_i2w_neg1 >>
    ASM_REWRITE_TAC[word_0_w2i] >> intLib.ARITH_TAC) >>
  mp_tac (INST_TYPE [alpha |-> ``:256``] word_quot) >>
  disch_then (qspecl_then [`INT_MINw`, `i2w(-1)`] mp_tac) >>
  ASM_REWRITE_TAC[] >> strip_tac >> pop_assum (fn th => REWRITE_TAC[th]) >>
  REWRITE_TAC[INST_TYPE [alpha |-> ``:256``] w2i_INT_MINw, check, w2i_i2w_neg1] >>
  `INT256_MIN quot -1 = -INT256_MIN` by (
    `(-1:int) <> 0` by intLib.ARITH_TAC >>
    mp_tac (Q.SPECL [`INT256_MIN`, `1i`] (CONJUNCT1 (CONJUNCT2 INT_QUOT_CALCULATE))) >>
    simp[INT_QUOT_1]) >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  REWRITE_TAC[neg_INT256_MIN, i2w_def] >>
  `~(&(words$INT_MIN(:256)) < 0i)` by simp[] >>
  ASM_REWRITE_TAC[] >>
  `Num (&(words$INT_MIN(:256))) = words$INT_MIN(:256)` by simp[] >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  REWRITE_TAC[GSYM wordsTheory.word_L_def] >>
  REWRITE_TAC[INST_TYPE [alpha |-> ``:256``] w2i_INT_MINw, check]);

end (* struct *)
