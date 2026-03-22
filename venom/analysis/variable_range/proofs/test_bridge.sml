open HolKernel boolLib bossLib;
open integerTheory integer_wordTheory wordsTheory;
open intLib fcpLib;
open valueRangeDefsTheory;

val dim256 = fcpLib.INDEX_CONV ``dimindex(:256)``;
val w2i_le_256 = INST_TYPE [alpha |-> ``:256``] w2i_le |> REWRITE_RULE [GSYM INT256_MAX_def];
val w2i_ge_256 = INST_TYPE [alpha |-> ``:256``] w2i_ge |> REWRITE_RULE [GSYM INT256_MIN_def];
val w2i_i2w_256 = INST_TYPE [alpha |-> ``:256``] w2i_i2w
  |> REWRITE_RULE [GSYM INT256_MIN_def, GSYM INT256_MAX_def];

val quot_nat = CONJUNCT1 INT_QUOT_CALCULATE;
val quot_neg = CONJUNCT1 (CONJUNCT2 INT_QUOT_CALCULATE);

(* Reduction lemmas: signed quot → nat DIV *)
val quot_to_nat_pp = prove(
  ``!m n. 0 < n ==> &m quot &n = &(m DIV n)``,
  rpt strip_tac >> `&n <> 0i` by intLib.ARITH_TAC >> simp[quot_nat]);
val quot_to_nat_pn = prove(
  ``!m n. 0 < n ==> &m quot -&n = -&(m DIV n)``,
  rpt strip_tac >> `&n <> 0i` by intLib.ARITH_TAC >>
  mp_tac (Q.SPECL [`&m`, `&n`] quot_neg) >> simp[] >> strip_tac >> simp[quot_nat]);
val quot_to_nat_np = prove(
  ``!m n. 0 < n ==> -&m quot &n = -&(m DIV n)``,
  rpt strip_tac >> `&n <> 0i` by intLib.ARITH_TAC >>
  mp_tac (Q.SPECL [`&m`, `&n`] quot_neg) >> simp[] >> strip_tac >> simp[quot_nat]);
val quot_to_nat_nn = prove(
  ``!m n. 0 < n ==> -&m quot -&n = &(m DIV n)``,
  rpt strip_tac >> `&n <> 0i` by intLib.ARITH_TAC >>
  mp_tac (Q.SPECL [`&m`, `&n`] quot_neg) >> simp[] >> strip_tac >>
  `- -&n = &n` by intLib.ARITH_TAC >>
  ASM_REWRITE_TAC[] >> simp[quot_nat]);

val _ = print "=== reduction lemmas proved ===\n";

(* Tactic for introducing nat form of a w2i value *)
(* Given `0 <= w2i w`, introduce m such that w2i w = &m *)
(* Given `w2i w < 0`, introduce m such that w2i w = -&m and 0 < m *)
fun w2i_nat_tac wt =
  Cases_on `0 <= ^wt` >| [
    `?m. ^wt = &m` by (qexists_tac `Num(^wt)` >> simp[INT_OF_NUM]),
    `^wt < 0` by intLib.ARITH_TAC >>
    `?m. ^wt = -&m /\ 0 < m` by (
      qexists_tac `Num(-( ^wt ))` >>
      simp[INT_OF_NUM] >> intLib.ARITH_TAC)
  ];

val _ = print "=== w2i_nat_tac defined ===\n";

(* Lower bound *)
val w2i_quot_lower = prove(
  ``!a:256 word b:256 word.
    w2i b <> 0 ==> INT256_MIN <= w2i a quot w2i b``,
  rpt strip_tac >>
  w2i_nat_tac ``w2i (a:256 word)`` >> w2i_nat_tac ``w2i (b:256 word)`` >>
  gvs[] >| [
    (* a=&m, b=&m': quot = &(m DIV m') ≥ 0 ≥ MIN *)
    `0 < m'` by intLib.ARITH_TAC >>
    simp[quot_to_nat_pp, INT256_MIN_def, INT_MIN_def,
         wordsTheory.INT_MIN_def, dim256],
    (* a=&m, b=-&m': quot = -&(m DIV m'), need -&(m DIV m') ≥ MIN *)
    simp[quot_to_nat_pn] >>
    `m DIV m' <= m` by (irule arithmeticTheory.DIV_LESS_EQ >> DECIDE_TAC) >>
    mp_tac (Q.SPEC `a` w2i_le_256) >> gvs[] >>
    simp[INT256_MIN_def, INT256_MAX_def, INT_MIN_def, INT_MAX_def,
         wordsTheory.INT_MIN_def, dim256] >> DECIDE_TAC,
    (* a=-&m, b=&m': quot = -&(m DIV m'), need ≥ MIN *)
    `0 < m'` by intLib.ARITH_TAC >>
    simp[quot_to_nat_np] >>
    `m DIV m' <= m` by (irule arithmeticTheory.DIV_LESS_EQ >> DECIDE_TAC) >>
    mp_tac (Q.SPEC `a` w2i_ge_256) >> gvs[] >>
    simp[INT256_MIN_def, INT_MIN_def, wordsTheory.INT_MIN_def, dim256] >>
    DECIDE_TAC,
    (* a=-&m, b=-&m': quot = &(m DIV m') ≥ 0 ≥ MIN *)
    simp[quot_to_nat_nn, INT256_MIN_def, INT_MIN_def,
         wordsTheory.INT_MIN_def, dim256]
  ]);

val _ = print "=== w2i_quot_lower proved ===\n";

(* Upper bound *)
val w2i_quot_upper = prove(
  ``!a:256 word b:256 word.
    w2i b <> 0 /\ ~(w2i a = INT256_MIN /\ w2i b = -1) ==>
    w2i a quot w2i b <= INT256_MAX``,
  rpt gen_tac >> strip_tac >>
  w2i_nat_tac ``w2i (a:256 word)`` >> w2i_nat_tac ``w2i (b:256 word)`` >>
  gvs[] >| [
    (* a=&m, b=&m': quot = &(m DIV m') ≤ &m ≤ MAX *)
    `0 < m'` by intLib.ARITH_TAC >>
    simp[quot_to_nat_pp] >>
    `m DIV m' <= m` by (irule arithmeticTheory.DIV_LESS_EQ >> DECIDE_TAC) >>
    mp_tac (Q.SPEC `a` w2i_le_256) >> fs[] >>
    simp[INT256_MAX_def, INT_MAX_def, wordsTheory.INT_MIN_def, dim256] >>
    DECIDE_TAC,
    (* a=&m, b=-&m': quot = -&(m DIV m') ≤ 0 ≤ MAX *)
    simp[quot_to_nat_pn,
         INT256_MAX_def, INT_MAX_def, wordsTheory.INT_MIN_def, dim256],
    (* a=-&m, b=&m': quot = -&(m DIV m') ≤ 0 ≤ MAX *)
    `0 < m'` by intLib.ARITH_TAC >>
    simp[quot_to_nat_np,
         INT256_MAX_def, INT_MAX_def, wordsTheory.INT_MIN_def, dim256],
    (* a=-&m, b=-&m': quot = &(m DIV m')
       Need m DIV m' ≤ MAX-value.
       If m' ≥ 2: m DIV m' ≤ m DIV 2 ≤ (-MIN)/2 < -MIN = MAX+1
       If m' = 1: b=-1, precond says a ≠ MIN, so m < -MIN, m ≤ MAX-value *)
    simp[quot_to_nat_nn] >>
    `m DIV m' <= m` by (irule arithmeticTheory.DIV_LESS_EQ >> DECIDE_TAC) >>
    mp_tac (Q.SPEC `a` w2i_ge_256) >>
    Cases_on `m' >= 2` >- (
      `m DIV m' <= m DIV 2` by (
        irule dividesTheory.DIV_LE_MONOTONE_REVERSE >> DECIDE_TAC) >>
      simp[INT256_MAX_def, INT256_MIN_def, INT_MAX_def, INT_MIN_def,
           wordsTheory.INT_MIN_def, dim256] >> DECIDE_TAC) >>
    (* m' = 1, so b = -1. Precond: ¬(a=MIN ∧ b=-1), b=-1, so a ≠ MIN *)
    `m' = 1` by DECIDE_TAC >>
    gvs[arithmeticTheory.DIV_1] >>
    (* w2i a = -&m, w2i b = -1 *)
    (* precond: ¬(-&m = INT256_MIN ∧ -1 = -1), so -&m ≠ INT256_MIN *)
    (* Thus m ≠ Num(-INT256_MIN) and m ≤ Num(-INT256_MIN), so m < Num(-INT256_MIN) *)
    simp[INT256_MAX_def, INT256_MIN_def, INT_MAX_def, INT_MIN_def,
         wordsTheory.INT_MIN_def, dim256] >> intLib.ARITH_TAC
  ]);

val _ = print "=== w2i_quot_upper proved ===\n";

(* Now w2i_word_quot *)
val w2i_word_quot = prove(
  ``!a:256 word b:256 word.
    b <> 0w /\ ~(a = INT_MINw /\ b = i2w (-1)) ==>
    w2i (a / b) = w2i a quot w2i b``,
  rpt strip_tac >>
  `w2i b <> 0` by (strip_tac >> fs[w2i_eq_0]) >>
  `a / b = i2w (w2i a quot w2i b)` by (
    mp_tac (INST_TYPE [alpha |-> ``:256``] word_quot) >>
    disch_then (qspecl_then [`a`, `b`] mp_tac) >> simp[]) >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  match_mp_tac w2i_i2w_256 >>
  `~(w2i a = INT256_MIN /\ w2i b = -1)` by (
    strip_tac >> fs[] >>
    qpat_x_assum `~(_ /\ _)` mp_tac >> simp[] >>
    conj_tac >| [
      irule w2i_11 >> simp[w2i_INT_MINw],
      irule w2i_11 >> simp[]
    ]) >>
  conj_tac >| [
    mp_tac (Q.SPECL [`a`, `b`] w2i_quot_lower) >> simp[],
    mp_tac (Q.SPECL [`a`, `b`] w2i_quot_upper) >> simp[]
  ]);

val _ = print "=== ALL PROVED ===\n";
