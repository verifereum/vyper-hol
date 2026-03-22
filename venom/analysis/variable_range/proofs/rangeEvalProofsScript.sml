(*
 * Range Evaluators — Proofs
 *
 * Soundness: each per-opcode evaluator over-approximates the
 * concrete result for all values within the input ranges.
 *)

Theory rangeEvalProofs
Ancestors
  valueRangeDefs rangeEvalDefs valueRangeProofs integer_word
Libs
  integerTheory integer_wordTheory intLib fcpLib rangeEvalProofsLib

(* ===== Shared toolkit ===== *)

val dim256 = fcpLib.INDEX_CONV ``dimindex(:256)``;

val w2i_simp = [integer_wordTheory.w2i_1, integer_wordTheory.w2i_def,
  wordsTheory.word_msb_n2w, wordsTheory.w2n_n2w,
  wordsTheory.dimword_def, dim256];

(* w2i bounds specialized to 256 bits, stated with INT256_MIN/MAX *)
val w2i_le_256 = INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_le
  |> REWRITE_RULE [GSYM INT256_MAX_def];
val w2i_ge_256 = INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_ge
  |> REWRITE_RULE [GSYM INT256_MIN_def];

(* w2i_eq_w2n specialized to 256 bits and universally quantified *)
val w2i_eq_w2n_256 = GEN ``w:256 word``
  (INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_eq_w2n);

(* w2i_i2w specialized to 256 bits using INT256_MIN/MAX *)
val w2i_i2w_256 =
  INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_i2w
  |> REWRITE_RULE [GSYM INT256_MIN_def, GSYM INT256_MAX_def];
  (* ⊢ ∀i. INT256_MIN ≤ i ∧ i ≤ INT256_MAX ⇒ w2i(i2w i) = i *)

(* i2w_DIV specialized to 256 bits using INT256_MIN/MAX *)
val i2w_DIV_256 =
  INST_TYPE [alpha |-> ``:256``] integer_wordTheory.i2w_DIV
  |> REWRITE_RULE [GSYM INT256_MIN_def, GSYM INT256_MAX_def, dim256];
  (* ⊢ ∀n i. n < 256 ∧ INT256_MIN ≤ i ∧ i ≤ INT256_MAX ⇒
             i2w(i / 2^n) = i2w(i) ≫ n *)

(* Key numeric facts for ARITH_TAC: INT256_MIN < 0 < INT256_MAX *)
Theorem int256_min_neg[local]:
  INT256_MIN < 0
Proof
  simp[INT256_MIN_def, integer_wordTheory.INT_MIN_def,
       integer_wordTheory.INT_MAX_def,
       wordsTheory.INT_MIN_def, dim256]
QED

Theorem int256_max_pos[local]:
  INT256_MAX > 0
Proof
  simp[INT256_MAX_def, integer_wordTheory.INT_MAX_def,
       wordsTheory.INT_MIN_def, dim256]
QED

Theorem uint256_gt_int256[local]:
  UINT256_MAX_int > INT256_MAX
Proof
  simp[UINT256_MAX_def, INT256_MAX_def,
       integer_wordTheory.UINT_MAX_def, integer_wordTheory.INT_MAX_def,
       wordsTheory.INT_MIN_def, wordsTheory.dimword_def, dim256]
QED

(* === eval_range soundness shared tactics === *)

(* Standard gvs arguments for closing VR_Top/Bottom/constant and normalizing ¬(<)/¬(≤) *)
val eval_range_gvs_args =
  [in_range_top, in_range_def, vr_lo_def, vr_hi_def,
   in_range_constant, int256_min_neg, int256_max_pos,
   integerTheory.INT_NOT_LT, integerTheory.INT_NOT_LE];

(* Close goals with false assumption 0 ≤ INT256_MIN *)
val vr_top_contra_tac =
  TRY (mp_tac int256_min_neg >> intLib.ARITH_TAC >> NO_TAC);

(* w2i/w2n sign bridge — shared tactic for both helpers *)
val w2n_sign_tac =
  rpt gen_tac >> strip_tac >>
  REWRITE_TAC[w2i_eq_w2n_256] >>
  rpt (first_x_assum (mp_tac o REWRITE_RULE [w2i_eq_w2n_256])) >>
  mp_tac (Q.SPEC `w1` (INST_TYPE [alpha |-> ``:256``] wordsTheory.w2n_lt)) >>
  mp_tac (Q.SPEC `w2` (INST_TYPE [alpha |-> ``:256``] wordsTheory.w2n_lt)) >>
  mp_tac (INST_TYPE [alpha |-> ``:256``] wordsTheory.dimword_IS_TWICE_INT_MIN) >>
  rpt IF_CASES_TAC >> rpt strip_tac >> intLib.ARITH_TAC;

(* Cross-sign: negative w2i ⇒ strictly larger w2n than non-negative w2i *)
Theorem cross_sign_w2n[local]:
  ∀(w1:256 word) (w2:256 word). w2i w1 < 0 ∧ 0 ≤ w2i w2 ⇒ w2n w2 < w2n w1
Proof
  w2n_sign_tac
QED

(* Same-sign: w2n order = w2i order when both signs agree *)
Theorem same_sign_w2n[local]:
  ∀(w1:256 word) (w2:256 word).
    (0 ≤ w2i w1 ∧ 0 ≤ w2i w2) ∨ (w2i w1 < 0 ∧ w2i w2 < 0) ⇒
    (w2n w1 < w2n w2 ⇔ w2i w1 < w2i w2)
Proof
  w2n_sign_tac
QED

(* Boolean result is always in [0,1] *)
Theorem in_range_bool_result[local]:
  ∀b:bool. in_range vr_bool_range (if b then (1w:256 word) else 0w)
Proof
  rw[in_range_def, vr_bool_range_def] >> simp w2i_simp
QED

(* wrap256_signed in terms of INT_MIN/dimword *)
Theorem wrap256_alt[local]:
  ∀v:int. wrap256_signed v =
    (v + &INT_MIN(:256)) % &dimword(:256) - &INT_MIN(:256)
Proof
  rw[wrap256_signed_def, LET_THM, wordsTheory.INT_MIN_def,
     wordsTheory.dimword_def, dim256]
QED

(* KEY: w2i(i2w x) = wrap256_signed x *)
Theorem w2i_i2w_wrap256[local]:
  ∀x:int. w2i ((i2w x):256 word) = wrap256_signed x
Proof
  rpt strip_tac >>
  REWRITE_TAC[wrap256_alt, integer_wordTheory.w2i_eq_w2n] >>
  qabbrev_tac `n = &w2n ((i2w x):256 word) : int` >>
  qabbrev_tac `M = &INT_MIN(:256) : int` >>
  qabbrev_tac `D = &dimword(:256) : int` >>
  `D = 2 * M` by simp[Abbr `D`, Abbr `M`, wordsTheory.dimword_IS_TWICE_INT_MIN] >>
  `0i < M` by (simp[Abbr `M`] >> mp_tac (INST_TYPE [alpha |-> ``:256``] wordsTheory.ZERO_LT_INT_MIN) >> simp[]) >>
  `D <> 0i` by intLib.ARITH_TAC >>
  `0i <= n /\ n < D` by (simp[Abbr `n`, Abbr `D`] >> simp[wordsTheory.w2n_lt, wordsTheory.ZERO_LT_dimword]) >>
  `M % D = M` by (irule integerTheory.INT_LESS_MOD >> intLib.ARITH_TAC) >>
  `(x + M) % D = (n + M) % D` by (
    `n = x % D` by simp[Abbr `n`, Abbr `D`, integer_wordTheory.w2n_i2w] >>
    mp_tac (integerTheory.INT_MOD_PLUS |> INST [``k:int`` |-> ``D:int``, ``i:int`` |-> ``x:int``, ``j:int`` |-> ``M:int``]) >>
    simp[]) >>
  `(w2n ((i2w x):256 word) < INT_MIN(:256)) = (n < M)` by simp[Abbr `n`, Abbr `M`, integerTheory.INT_LT] >>
  pop_assum SUBST1_TAC >>
  IF_CASES_TAC
  >- (
    `(n + M) % D = n + M` by (irule integerTheory.INT_LESS_MOD >> intLib.ARITH_TAC) >>
    intLib.ARITH_TAC)
  >- (
    `n + M = 1 * D + (n - M)` by intLib.ARITH_TAC >>
    `(n + M) % D = (n - M) % D` by (
      pop_assum (fn th => REWRITE_TAC[th]) >>
      simp[integerTheory.INT_MOD_ADD_MULTIPLES]) >>
    `(n - M) % D = n - M` by (irule integerTheory.INT_LESS_MOD >> intLib.ARITH_TAC) >>
    intLib.ARITH_TAC)
QED

(* Corollaries: wrap256_signed models word +, -, * *)
Theorem w2i_add_wrap256[local]:
  ∀w1 w2:256 word. w2i (w1 + w2) = wrap256_signed (w2i w1 + w2i w2)
Proof
  rw[GSYM integer_wordTheory.word_add_i2w, w2i_i2w_wrap256]
QED

Theorem w2i_sub_wrap256[local]:
  ∀w1 w2:256 word. w2i (w1 - w2) = wrap256_signed (w2i w1 - w2i w2)
Proof
  rw[GSYM integer_wordTheory.word_sub_i2w, w2i_i2w_wrap256]
QED

Theorem w2i_mul_wrap256[local]:
  ∀w1 w2:256 word. w2i (w1 * w2) = wrap256_signed (w2i w1 * w2i w2)
Proof
  rw[GSYM integer_wordTheory.word_mul_i2w, w2i_i2w_wrap256]
QED

(* wrap256_signed is identity on signed range *)
Theorem wrap256_signed_id[local]:
  ∀v:int. INT_MIN(:256) ≤ v ∧ v ≤ INT_MAX(:256) ⇒ wrap256_signed v = v
Proof
  rw[wrap256_alt] >>
  qabbrev_tac `M = &INT_MIN(:256) : int` >>
  `&dimword(:256) = 2 * M` by simp[Abbr `M`, wordsTheory.dimword_IS_TWICE_INT_MIN] >>
  `0i < M` by (simp[Abbr `M`, integerTheory.INT_OF_NUM_LT, wordsTheory.ZERO_LT_INT_MIN]) >>
  `&INT_MAX(:256) = M - 1` by (
    simp[Abbr `M`, wordsTheory.INT_MAX_def] >>
    `1n <= INT_MIN(:256)` by simp[wordsTheory.INT_MIN_def, dim256] >>
    imp_res_tac (GSYM integerTheory.INT_SUB) >> simp[]) >>
  `0 <= v + M /\ v + M < 2 * M` by intLib.ARITH_TAC >>
  ASM_REWRITE_TAC[] >>
  `(v + M) % (2 * M) = v + M` by (
    irule integerTheory.INT_LESS_MOD >> intLib.ARITH_TAC) >>
  intLib.ARITH_TAC
QED

(* Bridge: w2i(w1 op w2) = w2i w1 op w2i w2 when result in signed range.
   Uses word_op_i2w (modular identity) + w2i_i2w (signed-range identity). *)
Theorem w2i_add_id[local]:
  ∀w1 w2:256 word. INT256_MIN ≤ w2i w1 + w2i w2 ∧
    w2i w1 + w2i w2 ≤ INT256_MAX ⇒ w2i (w1 + w2) = w2i w1 + w2i w2
Proof
  rpt strip_tac >>
  `w1 + w2 = i2w (w2i w1 + w2i w2)` by simp[GSYM integer_wordTheory.word_add_i2w] >>
  pop_assum SUBST1_TAC >>
  irule integer_wordTheory.w2i_i2w >>
  REWRITE_TAC[GSYM INT256_MIN_def, GSYM INT256_MAX_def] >> fs[]
QED

Theorem w2i_sub_id[local]:
  ∀w1 w2:256 word. INT256_MIN ≤ w2i w1 - w2i w2 ∧
    w2i w1 - w2i w2 ≤ INT256_MAX ⇒ w2i (w1 - w2) = w2i w1 - w2i w2
Proof
  rpt strip_tac >>
  `w1 - w2 = i2w (w2i w1 - w2i w2)` by simp[GSYM integer_wordTheory.word_sub_i2w] >>
  pop_assum SUBST1_TAC >>
  irule integer_wordTheory.w2i_i2w >>
  REWRITE_TAC[GSYM INT256_MIN_def, GSYM INT256_MAX_def] >> fs[]
QED

Theorem w2i_mul_id[local]:
  ∀w1 w2:256 word. INT256_MIN ≤ w2i w1 * w2i w2 ∧
    w2i w1 * w2i w2 ≤ INT256_MAX ⇒ w2i (w1 * w2) = w2i w1 * w2i w2
Proof
  rpt strip_tac >>
  `w1 * w2 = i2w (w2i w1 * w2i w2)` by simp[GSYM integer_wordTheory.word_mul_i2w] >>
  pop_assum SUBST1_TAC >>
  irule integer_wordTheory.w2i_i2w >>
  REWRITE_TAC[GSYM INT256_MIN_def, GSYM INT256_MAX_def] >> fs[]
QED

(* Multiplication monotonicity for non-negative integers *)
Theorem int_le_mul_mono[local]:
  ∀a b c d:int. 0 ≤ a ∧ a ≤ c ∧ 0 ≤ b ∧ b ≤ d ⇒ a * b ≤ c * d
Proof
  rpt strip_tac >>
  irule integerTheory.INT_LE_TRANS >> qexists_tac `c * b` >> conj_tac
  >- (Cases_on `b = 0` >- simp[] >>
      `0 < b` by intLib.ARITH_TAC >>
      ONCE_REWRITE_TAC[integerTheory.INT_MUL_COMM] >>
      ASM_SIMP_TAC std_ss [integerTheory.INT_LE_MONO])
  >- (Cases_on `c = 0` >- (`a = 0` by intLib.ARITH_TAC >> simp[]) >>
      `0 < c` by intLib.ARITH_TAC >>
      ASM_SIMP_TAC std_ss [integerTheory.INT_LE_MONO])
QED

(* Constant range soundness for +, -, * *)
Theorem in_range_constant_add[local]:
  ∀w1 w2:256 word lo1 lo2.
    w2i w1 = lo1 ∧ w2i w2 = lo2 ⇒
    in_range (vr_constant (wrap256_signed (lo1 + lo2))) (w1 + w2)
Proof
  rw[in_range_constant, w2i_add_wrap256]
QED

Theorem in_range_constant_sub[local]:
  ∀w1 w2:256 word lo1 lo2.
    w2i w1 = lo1 ∧ w2i w2 = lo2 ⇒
    in_range (vr_constant (wrap256_signed (lo1 - lo2))) (w1 - w2)
Proof
  rw[in_range_constant, w2i_sub_wrap256]
QED

Theorem in_range_constant_mul[local]:
  ∀w1 w2:256 word lo1 lo2.
    w2i w1 = lo1 ∧ w2i w2 = lo2 ⇒
    in_range (vr_constant (wrap256_signed (lo1 * lo2))) (w1 * w2)
Proof
  rw[in_range_constant, w2i_mul_wrap256]
QED

(* ===== ASSIGN soundness ===== *)

Theorem eval_range_assign_sound:
  ∀r w. in_range r w ⇒ in_range (eval_range_assign r) w
Proof
  rw[eval_range_assign_def]
QED

(* ===== ISZERO soundness ===== *)

Theorem eval_range_iszero_sound:
  ∀r w.
    in_range r w ⇒
    in_range (eval_range_iszero r)
             (if w = 0w then 1w else 0w)
Proof
  Cases >> rw[eval_range_iszero_def, in_range_def, vr_constant_def, vr_bool_range_def]
  >- simp w2i_simp
  >> rw[in_range_def] >> fs[integer_wordTheory.word_0_w2i, GSYM integer_wordTheory.w2i_eq_0]
  >> simp w2i_simp >> intLib.ARITH_TAC
QED

(* ===== ADD soundness ===== *)

Theorem eval_range_add_sound:
  ∀r1 r2 w1 w2.
    in_range r1 w1 ∧ in_range r2 w2 ⇒
    in_range (eval_range_add r1 r2) (w1 + w2)
Proof
  Cases >> Cases >> rw[eval_range_add_def, in_range_def, LET_THM]
  >> TRY (simp[in_range_top] >> NO_TAC) >> TRY (simp[] >> NO_TAC)
  >> rpt strip_tac
  >> TRY (
    `w2i w1 = i /\ w2i w2 = i'` by metis_tac[integerTheory.INT_LE_ANTISYM] >>
    simp[in_range_constant_add] >> NO_TAC)
  >> qabbrev_tac `a = w2i w1` >> qabbrev_tac `b = w2i w2`
  >> `INT256_MIN <= a + b /\ a + b <= INT256_MAX` by
    (mp_tac int256_min_neg >> intLib.ARITH_TAC)
  >> `w2i (w1 + w2) = a + b` by simp[Abbr `a`, Abbr `b`, w2i_add_id]
  >> intLib.ARITH_TAC
QED

(* ===== SUB soundness ===== *)

Theorem eval_range_sub_sound:
  ∀r1 r2 w1 w2.
    in_range r1 w1 ∧ in_range r2 w2 ⇒
    in_range (eval_range_sub r1 r2) (w1 - w2)
Proof
  Cases >> Cases >> rw[eval_range_sub_def, in_range_def, LET_THM]
  >> TRY (simp[in_range_top] >> NO_TAC) >> TRY (simp[] >> NO_TAC)
  >> rpt strip_tac
  >> TRY (
    `w2i w1 = i /\ w2i w2 = i'` by metis_tac[integerTheory.INT_LE_ANTISYM] >>
    simp[in_range_constant_sub] >> NO_TAC)
  >> qabbrev_tac `a = w2i w1` >> qabbrev_tac `b = w2i w2`
  >> `INT256_MIN <= a - b /\ a - b <= INT256_MAX` by intLib.ARITH_TAC
  >> `w2i (w1 - w2) = a - b` by simp[Abbr `a`, Abbr `b`, w2i_sub_id]
  >> intLib.ARITH_TAC
QED

(* ===== MUL soundness ===== *)

Theorem eval_range_mul_sound:
  ∀r1 r2 w1 w2.
    in_range r1 w1 ∧ in_range r2 w2 ⇒
    in_range (eval_range_mul r1 r2) (w1 * w2)
Proof
  Cases >> Cases >>
  rw[eval_range_mul_def, in_range_def, in_range_constant, LET_THM]
  >> TRY (simp[in_range_top] >> NO_TAC) >> TRY (simp[] >> NO_TAC)
  >> rpt strip_tac
  (* constant-constant case: both ranges are singletons *)
  >> TRY (
    `w2i w1 = i /\ w2i w2 = i'` by metis_tac[integerTheory.INT_LE_ANTISYM] >>
    simp[w2i_mul_wrap256] >> NO_TAC)
  (* zero-factor cases: w2i (w1 * w2) = 0 when one factor is 0.
     metis_tac[INT_LE_ANTISYM] fails fast (~60ms) on non-zero goals. *)
  >> TRY (
    `w2i w1 = 0` by metis_tac[integerTheory.INT_LE_ANTISYM] >>
    fs[integer_wordTheory.w2i_eq_0, wordsTheory.WORD_MULT_CLAUSES,
       integer_wordTheory.word_0_w2i] >> NO_TAC)
  >> TRY (
    `w2i w2 = 0` by metis_tac[integerTheory.INT_LE_ANTISYM] >>
    fs[integer_wordTheory.w2i_eq_0, wordsTheory.WORD_MULT_CLAUSES,
       integer_wordTheory.word_0_w2i] >> NO_TAC)
  (* general range case: both non-negative.
     Remove the division assumption that makes ARITH_TAC diverge. *)
  >> Q.PAT_X_ASSUM `~(_ /\ _ > _ / _)` kall_tac
  >> Q.PAT_X_ASSUM `~(_ > RANGE_WIDTH_LIMIT \/ _)` kall_tac
  >> qabbrev_tac `a = w2i w1` >> qabbrev_tac `b = w2i w2`
  >> `0 <= a /\ 0 <= b` by intLib.ARITH_TAC
  >> `a * b <= i0 * i0'` by
    (irule int_le_mul_mono >> intLib.ARITH_TAC)
  >> `i * i' <= a * b` by
    (irule int_le_mul_mono >> intLib.ARITH_TAC)
  >> `0 <= a * b` by metis_tac[integerTheory.INT_LE_MUL]
  >> `INT256_MIN <= a * b` by (mp_tac int256_min_neg >> intLib.ARITH_TAC)
  >> `a * b <= INT256_MAX` by intLib.ARITH_TAC
  >> `w2i (w1 * w2) = a * b` by simp[Abbr `a`, Abbr `b`, w2i_mul_id]
  >> intLib.ARITH_TAC
QED

(* ===== Comparison soundness ===== *)

Theorem eval_range_compare_sound:
  ∀op r1 r2 w1 w2.
    in_range r1 w1 ∧ in_range r2 w2 ∧
    (op = LT ∨ op = GT ∨ op = SLT ∨ op = SGT) ⇒
    in_range (eval_range_compare op r1 r2)
             (case op of
                LT => if w2n w1 < w2n w2 then 1w else 0w
              | GT => if w2n w1 > w2n w2 then 1w else 0w
              | SLT => if w2i w1 < w2i w2 then 1w else 0w
              | SGT => if w2i w1 > w2i w2 then 1w else 0w
              | _ => ARB)
Proof
  rpt gen_tac >> strip_tac
  >> Cases_on `r1` >> Cases_on `r2`
  >> fs[eval_range_compare_def, in_range_def, LET_THM,
        vr_spans_sign_boundary_def, vr_lo_def, vr_hi_def,
        vr_constant_def, vr_bool_range_def]
  >> rw[in_range_def, in_range_bool_result]
  >> TRY (simp w2i_simp >> NO_TAC)
  >> TRY (simp[in_range_bool_result] >> NO_TAC)
  (* Remaining: contradictions. Evaluate w2i 0w/1w to get goal = F. *)
  >> simp[integer_wordTheory.word_0_w2i, integer_wordTheory.w2i_1, dim256]
  (* (a) Pure integer contradictions *)
  >> TRY intLib.ARITH_TAC
  (* (b) Cross-sign: w2i signs differ ⇒ w2n strictly ordered *)
  >> TRY (
    mp_tac (Q.SPECL [`w1`,`w2`] cross_sign_w2n) >>
    (impl_tac >- intLib.ARITH_TAC) >> intLib.ARITH_TAC)
  >> TRY (
    mp_tac (Q.SPECL [`w2`,`w1`] cross_sign_w2n) >>
    (impl_tac >- intLib.ARITH_TAC) >> intLib.ARITH_TAC)
  (* (c) Same-sign: w2n order = w2i order, then integer contradiction *)
  >> TRY (
    mp_tac (Q.SPECL [`w1`,`w2`] same_sign_w2n) >>
    (impl_tac >- intLib.ARITH_TAC) >> intLib.ARITH_TAC)
  >> TRY (
    mp_tac (Q.SPECL [`w2`,`w1`] same_sign_w2n) >>
    (impl_tac >- intLib.ARITH_TAC) >> intLib.ARITH_TAC)
  (* (d) Constant bounds: UINT256_MAX vs INT256_MIN/MAX *)
  >> assume_tac int256_min_neg >> assume_tac int256_max_pos
  >> assume_tac uint256_gt_int256
  >> assume_tac (Q.SPEC `w1` w2i_le_256) >> assume_tac (Q.SPEC `w2` w2i_le_256)
  >> assume_tac (Q.SPEC `w1` w2i_ge_256) >> assume_tac (Q.SPEC `w2` w2i_ge_256)
  >> intLib.ARITH_TAC
QED


(* ===== EQ soundness ===== *)

Theorem eval_range_eq_sound:
  ∀r1 r2 w1 w2.
    in_range r1 w1 ∧ in_range r2 w2 ⇒
    in_range (eval_range_eq r1 r2)
             (if w1 = w2 then 1w else 0w)
Proof
  Cases >> Cases >>
  rw[eval_range_eq_def, in_range_def, LET_THM,
     vr_spans_sign_boundary_def, vr_lo_def, vr_hi_def,
     vr_constant_def, vr_bool_range_def] >>
  rw[in_range_def]
  >> TRY (simp w2i_simp >> NO_TAC)
  >> TRY (simp[in_range_bool_result] >> NO_TAC)
  >> TRY (
    CCONTR_TAC >> fs[] >>
    `w2i w1 = w2i w2` by simp[integer_wordTheory.w2i_11] >>
    intLib.ARITH_TAC)
  >> simp[integer_wordTheory.word_0_w2i, integer_wordTheory.w2i_1, dim256]
  >> intLib.ARITH_TAC
QED

(* ===== NOT soundness ===== *)

Theorem eval_range_not_sound:
  ∀r w. in_range r w ⇒ in_range (eval_range_not r) (word_1comp w)
Proof
  Cases >> simp[eval_range_not_def, in_range_def, in_range_top]
QED

(* ===== XOR soundness (same_var=F) ===== *)

Theorem eval_range_xor_sound:
  ∀r1 r2 w1 w2.
    in_range r1 w1 ∧ in_range r2 w2 ⇒
    in_range (eval_range_xor r1 r2 F) (word_xor w1 w2)
Proof
  Cases >> Cases >> simp[eval_range_xor_def, in_range_def, in_range_top]
QED

(* ===== OR soundness ===== *)

Theorem eval_range_or_sound:
  ∀r1 r2 w1 w2.
    in_range r1 w1 ∧ in_range r2 w2 ⇒
    in_range (eval_range_or r1 r2) (word_or w1 w2)
Proof
  Cases >> Cases >>
  simp[eval_range_or_def, in_range_def, in_range_top, LET_THM,
       vr_is_constant_def, vr_lo_def, vr_hi_def] >>
  rpt strip_tac >> gvs[] >>
  TRY (simp[in_range_top] >> NO_TAC) >>
  rpt IF_CASES_TAC >> gvs[in_range_top, in_range_def] >>
  `w2i w1 = 0 ∨ w2i w2 = 0` by intLib.ARITH_TAC >>
  gvs[integer_wordTheory.w2i_eq_0, wordsTheory.WORD_OR_CLAUSES] >>
  intLib.ARITH_TAC
QED

(* ===== Infrastructure for remaining opcodes ===== *)

(* For non-negative w2i, w2i = &(w2n) *)
Theorem w2i_nonneg_eq_w2n[local]:
  ∀(w:256 word). 0 ≤ w2i w ⇒ w2i w = &(w2n w)
Proof
  rpt strip_tac >>
  REWRITE_TAC[w2i_eq_w2n_256] >>
  first_x_assum (mp_tac o REWRITE_RULE [w2i_eq_w2n_256]) >>
  mp_tac (Q.SPEC `w` (INST_TYPE [alpha |-> ``:256``] wordsTheory.w2n_lt)) >>
  mp_tac (INST_TYPE [alpha |-> ``:256``] wordsTheory.dimword_IS_TWICE_INT_MIN) >>
  rpt IF_CASES_TAC >> rpt strip_tac >> intLib.ARITH_TAC
QED

(* For small natural numbers, w2i (n2w k) = &k *)
Theorem w2i_n2w_small[local]:
  ∀k. k < INT_MIN(:256) ⇒ w2i ((n2w k):256 word) = &k
Proof
  rpt strip_tac >>
  simp[integer_wordTheory.w2i_eq_w2n, wordsTheory.w2n_n2w] >>
  `k < dimword(:256)` by (
    mp_tac (INST_TYPE [alpha |-> ``:256``]
            wordsTheory.dimword_IS_TWICE_INT_MIN) >>
    DECIDE_TAC) >>
  simp[arithmeticTheory.LESS_MOD]
QED

(* Non-negative w2i implies w2n < INT_MIN *)
Theorem w2n_lt_int_min_of_nonneg[local]:
  ∀(w:256 word). 0 ≤ w2i w ⇒ w2n w < INT_MIN(:256)
Proof
  rpt strip_tac >>
  first_x_assum (mp_tac o REWRITE_RULE [w2i_eq_w2n_256]) >>
  mp_tac (Q.SPEC `w` (INST_TYPE [alpha |-> ``:256``] wordsTheory.w2n_lt)) >>
  mp_tac (INST_TYPE [alpha |-> ``:256``] wordsTheory.dimword_IS_TWICE_INT_MIN) >>
  rpt IF_CASES_TAC >> rpt strip_tac >> intLib.ARITH_TAC
QED

(* ===== BYTE soundness ===== *)

Triviality in_range_vr_bytes_range_0w[local]:
  in_range (vr_bytes_range 1) (0w:256 word)
Proof
  simp[vr_bytes_range_def, in_range_def, integer_wordTheory.word_0_w2i]
QED

(* Pointwise ≤ implies SUM ≤ *)
Triviality sum_le_mono[local]:
  ∀n f g. (∀i. i < n ⇒ f i ≤ g i) ⇒ SUM n f ≤ SUM n g
Proof
  Induct >> simp[sum_numTheory.SUM_def] >>
  rpt strip_tac >> irule arithmeticTheory.LESS_EQ_LESS_EQ_MONO >>
  simp[]
QED

(* w2n(a && b) ≤ w2n b: AND can only clear bits, never set them *)
Triviality w2n_word_and_le:
  ∀(a:'a word) (b:'a word). w2n (a && b) ≤ w2n b
Proof
  rpt gen_tac >>
  simp[wordsTheory.w2n_def, wordsTheory.word_and_def,
       fcpTheory.FCP_BETA] >>
  irule sum_le_mono >> rpt strip_tac >>
  simp[bitTheory.SBIT_def, fcpTheory.FCP_BETA] >> rw[]
QED

Triviality in_range_vr_bytes_range_and_255[local]:
  ∀(w2:256 word) n. in_range (vr_bytes_range 1) (w2 ⋙ n && 255w)
Proof
  rpt gen_tac >>
  simp[vr_bytes_range_def, in_range_def] >>
  mp_tac (Q.SPECL [`w2 ⋙ n`, `255w`]
    (INST_TYPE [alpha |-> ``:256``] w2n_word_and_le)) >>
  simp[wordsTheory.dimword_def, dim256] >>
  strip_tac >>
  `w2n (w2 ⋙ n && 255w) < INT_MIN(:256)` by
    (simp[wordsTheory.INT_MIN_def, dim256] >> DECIDE_TAC) >>
  simp[integer_wordTheory.w2i_eq_w2n]
QED

Theorem eval_range_byte_sound:
  ∀r1 r2 (w1:256 word) (w2:256 word) lit1.
    in_range r1 w1 ∧ in_range r2 w2 ∧
    (∀v. lit1 = SOME v ⇒ w2i w1 = v) ⇒
    in_range (eval_range_byte r1 r2 lit1)
      (if w2n w1 ≥ 32 then 0w
       else word_and (word_lsr w2 ((31 − w2n w1) * 8)) (n2w 255))
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >>
  fs[in_range_bottom, eval_range_byte_def, in_range_top] >>
  CASE_TAC >> simp[in_range_top] >>
  rpt IF_CASES_TAC >> gvs[in_range_top, in_range_constant] >>
  (* All remaining goals: vr_bytes_range 1 or vr_constant 0 applied to
     0w or (shift && 255w). Handle COND + close contradictions + prove range. *)
  rpt (pop_assum mp_tac) >>
  simp[in_range_vr_bytes_range_0w, in_range_vr_bytes_range_and_255,
       integer_wordTheory.word_0_w2i, in_range_constant] >>
  (* Close w2i/w2n contradictions *)
  REWRITE_TAC[integer_wordTheory.w2i_eq_w2n] >>
  mp_tac (Q.SPEC `w1` (INST_TYPE [alpha |-> ``:256``] wordsTheory.w2n_lt)) >>
  mp_tac (INST_TYPE [alpha |-> ``:256``] wordsTheory.dimword_IS_TWICE_INT_MIN) >>
  simp[wordsTheory.INT_MIN_def, dim256] >>
  rpt IF_CASES_TAC >> rpt strip_tac >> intLib.ARITH_TAC
QED

(* ===== Int division toolkit ===== *)

(* Integer division monotonicity: x ≤ y ⇒ x/m ≤ y/m for 0 < m *)
Triviality int_div_le_mono:
  ∀(m:int) (x:int) (y:int). 0 < m ∧ x ≤ y ⇒ x / m ≤ y / m
Proof
  rpt strip_tac >> SPOSE_NOT_THEN ASSUME_TAC >>
  `y / m + 1 ≤ x / m` by intLib.ARITH_TAC >>
  `m ≠ (0:int)` by intLib.ARITH_TAC >>
  `x = x / m * m + x % m` by metis_tac[integerTheory.INT_DIVISION] >>
  `y = y / m * m + y % m` by metis_tac[integerTheory.INT_DIVISION] >>
  `0 ≤ x % m ∧ x % m < m` by (
    `if m < 0 then m < x % m ∧ x % m ≤ 0 else 0 ≤ x % m ∧ x % m < m`
      by metis_tac[integerTheory.INT_DIVISION] >>
    `¬(m < 0)` by intLib.ARITH_TAC >> fs[]) >>
  `0 ≤ y % m ∧ y % m < m` by (
    `if m < 0 then m < y % m ∧ y % m ≤ 0 else 0 ≤ y % m ∧ y % m < m`
      by metis_tac[integerTheory.INT_DIVISION] >>
    `¬(m < 0)` by intLib.ARITH_TAC >> fs[]) >>
  `m * (y / m + 1) ≤ m * (x / m)` by fs[integerTheory.INT_LE_MONO] >>
  intLib.ARITH_TAC
QED

(* Non-negative numerator and positive denominator ⇒ non-negative quotient *)
Triviality int_div_nonneg:
  ∀(x:int) (m:int). 0 ≤ x ∧ 0 < m ⇒ 0 ≤ x / m
Proof
  rpt strip_tac >> SPOSE_NOT_THEN ASSUME_TAC >>
  `m ≠ 0:int` by intLib.ARITH_TAC >>
  `x = x / m * m + x % m` by metis_tac[integerTheory.INT_DIVISION] >>
  `0 ≤ x % m ∧ x % m < m` by (
    `if m < 0 then m < x % m ∧ x % m ≤ 0 else 0 ≤ x % m ∧ x % m < m`
      by metis_tac[integerTheory.INT_DIVISION] >>
    `¬(m < 0)` by intLib.ARITH_TAC >> fs[]) >>
  `x / m ≤ -1` by intLib.ARITH_TAC >>
  `m * (x / m) ≤ m * -1` by simp[integerTheory.INT_LE_MONO] >>
  intLib.ARITH_TAC
QED

(* Mod bounds for non-negative numerator and positive denominator *)
Triviality int_mod_bounds:
  ∀(x:int) (m:int). 0 ≤ x ∧ 0 < m ⇒ 0 ≤ x % m ∧ x % m < m
Proof
  rpt strip_tac >>
  `m ≠ 0:int` by intLib.ARITH_TAC >>
  drule integerTheory.INT_DIVISION >>
  disch_then (qspec_then `x` strip_assume_tac) >>
  intLib.ARITH_TAC
QED

(* Denominator monotonicity for nat DIV *)
Triviality nat_div_le_mono_denom:
  ∀a b x. 0 < a ∧ a ≤ b ⇒ x DIV b ≤ x DIV a
Proof
  rpt strip_tac >>
  `0 < b` by DECIDE_TAC >>
  simp[arithmeticTheory.X_LE_DIV] >>
  `(x DIV b) * b ≤ x` by simp[dividesTheory.DIV_MULT_LE] >>
  `(x DIV b) * a ≤ (x DIV b) * b` by
    (irule arithmeticTheory.LESS_MONO_MULT2 >> DECIDE_TAC) >>
  DECIDE_TAC
QED

(* Denominator monotonicity for int division *)
Triviality int_div_le_mono_denom:
  ∀(a:int) (b:int) (x:int). 0 < a ∧ a ≤ b ∧ 0 ≤ x ⇒ x / b ≤ x / a
Proof
  rpt strip_tac >>
  `0 ≤ a ∧ 0 ≤ b` by intLib.ARITH_TAC >>
  imp_res_tac integerTheory.NUM_POSINT_EXISTS >> gvs[] >>
  fs[integerTheory.INT_DIV, integerTheory.INT_LE,
     integerTheory.INT_LT, integerTheory.INT_INJ] >>
  metis_tac[nat_div_le_mono_denom]
QED

(* x / d ≤ x for non-negative x and d ≥ 1 *)
Triviality int_div_le_dividend:
  ∀(x:int) (d:int). 0 ≤ x ∧ 1 ≤ d ⇒ x / d ≤ x
Proof
  rpt strip_tac >>
  `x / d ≤ x / 1` suffices_by simp[integerTheory.INT_DIV_1] >>
  irule int_div_le_mono_denom >> intLib.ARITH_TAC
QED

(* Int-to-nat bridges (for MOD proof) *)
Triviality int_div_to_nat:
  ∀a b. 0 ≤ a ∧ 0 < b ⇒ a / b = &(Num a DIV Num b)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`a`, `b`] integerTheory.int_div) >>
  `b ≠ 0` by intLib.ARITH_TAC >>
  simp[integerTheory.NUM_OF_INT]
QED

Triviality int_mod_to_nat:
  ∀a b. 0 ≤ a ∧ 0 < b ⇒ a % b = &(Num a MOD Num b)
Proof
  rpt strip_tac >>
  `Num b ≠ 0` by intLib.ARITH_TAC >>
  `a = &(Num a)` by simp[GSYM integerTheory.INT_OF_NUM] >>
  `b = &(Num b)` by intLib.ARITH_TAC >>
  ONCE_ASM_REWRITE_TAC[] >>
  simp[CONJUNCT1 integerTheory.INT_MOD_CALCULATE]
QED

(* ===== w2i bridge lemmas for word operations ===== *)

(* AND bridge: non-negative mask means non-negative result bounded by mask *)
Triviality w2i_word_and_nonneg:
  ∀(a:256 word) (b:256 word).
    0 ≤ w2i b ⇒ 0 ≤ w2i (word_and a b) ∧ w2i (word_and a b) ≤ w2i b
Proof
  rpt strip_tac >>
  imp_res_tac w2i_nonneg_eq_w2n >>
  imp_res_tac w2n_lt_int_min_of_nonneg >>
  `w2n (word_and a b) ≤ w2n b` by simp[w2n_word_and_le] >>
  `w2n (word_and a b) < INT_MIN(:256)` by DECIDE_TAC >>
  `0 ≤ w2i (word_and a b)` by (
    REWRITE_TAC[integer_wordTheory.w2i_eq_w2n] >>
    mp_tac (Q.SPEC `word_and a b`
      (INST_TYPE [alpha |-> ``:256``] wordsTheory.w2n_lt)) >>
    mp_tac (INST_TYPE [alpha |-> ``:256``]
      wordsTheory.dimword_IS_TWICE_INT_MIN) >>
    simp[wordsTheory.INT_MIN_def, dim256] >>
    rpt IF_CASES_TAC >> DECIDE_TAC) >>
  imp_res_tac w2i_nonneg_eq_w2n >> intLib.ARITH_TAC
QED

(* For x ≤ 0 and d ≥ 1, x/d ≥ x (division moves toward 0) *)
Triviality int_div_neg_ge:
  ∀(x:int) (d:int). x ≤ 0 ∧ 1 ≤ d ⇒ x ≤ x / d
Proof
  rpt strip_tac >>
  `d ≠ 0:int` by intLib.ARITH_TAC >> `0 < d` by intLib.ARITH_TAC >>
  Cases_on `x = 0` >- (simp[integerTheory.INT_DIV_0]) >>
  (* x < 0 case: use int_div definition *)
  `x < 0` by intLib.ARITH_TAC >>
  `¬(0 ≤ x)` by intLib.ARITH_TAC >>
  mp_tac (Q.SPECL [`x`, `d`] integerTheory.int_div) >> simp[] >>
  disch_then kall_tac >>
  (* x / d = -&(Num(-x) DIV Num d) + correction where correction ∈ {0, -1} *)
  `0 < Num d` by intLib.ARITH_TAC >>
  `Num (-x) DIV Num d ≤ Num (-x)` by
    simp[arithmeticTheory.DIV_LESS_EQ] >>
  `x = -&(Num (-x))` by intLib.ARITH_TAC >>
  qabbrev_tac `n = Num (-x)` >>
  pop_assum kall_tac >> pop_assum SUBST_ALL_TAC >>
  (* Goal: -&n ≤ -&(n DIV Num d) + correction *)
  simp[integerTheory.INT_LE_NEG]  >>
  Cases_on `n MOD Num d = 0` >> simp[] >>
  (* MOD≠0 case: need n DIV Num d + 1 ≤ n. Use DIV_LESS for d≥2. *)
  `0 < n` by intLib.ARITH_TAC >>
  `1 < Num d` by (Cases_on `Num d = 1` >- fs[] >> DECIDE_TAC) >>
  `n DIV Num d < n` by simp[arithmeticTheory.DIV_LESS] >>
  intLib.ARITH_TAC
QED

(* Integer division by positive preserves INT_MIN/INT_MAX bounds *)
Triviality int_div_in_range_lower:
  ∀(x:int) (d:int). 0 < d ∧ INT256_MIN ≤ x ⇒ INT256_MIN ≤ x / d
Proof
  rpt strip_tac >>
  irule integerTheory.INT_LE_TRANS >>
  qexists_tac `INT256_MIN / d` >>
  reverse conj_tac
  >- (irule int_div_le_mono >> intLib.ARITH_TAC) >>
  irule int_div_neg_ge >>
  simp[INT256_MIN_def, integer_wordTheory.INT_MIN_def,
       integer_wordTheory.INT_MAX_def,
       wordsTheory.INT_MIN_def, dim256] >>
  intLib.ARITH_TAC
QED

Triviality int_div_in_range_upper:
  ∀(x:int) (d:int). 0 < d ∧ x ≤ INT256_MAX ⇒ x / d ≤ INT256_MAX
Proof
  rpt strip_tac >>
  irule integerTheory.INT_LE_TRANS >>
  qexists_tac `INT256_MAX / d` >>
  conj_tac
  >- (irule int_div_le_mono >> intLib.ARITH_TAC) >>
  irule int_div_le_dividend >>
  simp[INT256_MAX_def, integer_wordTheory.INT_MAX_def,
       wordsTheory.INT_MIN_def, dim256] >>
  intLib.ARITH_TAC
QED

(* Bridge lemmas abs_quot_le, w2i_abs_bound, abs_lt_neg_min_gives_range,
   abs_quot_lt_neg_min, w2i_word_quot are in rangeEvalProofsLib.sml *)


(* ===== Unsigned DIV soundness ===== *)

(*
  Unsigned DIV soundness. Why true:
  - w2=0: result is 0w, analysis returns vr_constant 0. Sound.
  - lo2=hi2=0, w2≠0: w2i w2=0 ⇒ w2=0w, contradicts w2≠0w.
  - lo1<0: returns VR_Top. Always sound.
  - lo2<0: divisor has negative w2i ⇒ w2n(divisor) ≥ 2^255 > w2n(dividend),
    so w2n(w1) DIV w2n(w2) = 0. Returns vr_constant 0. Sound.
  - lo1≥0, lo2>0: both non-negative. w2i = w2n for non-negative.
    DIV_LE_MONOTONE gives lo1 DIV lo2 ≤ w2n(w1) DIV w2n(w2) ≤ hi1 DIV lo2.
*)
(* Bridge: w2i of unsigned word div for non-negative operands *)
Triviality w2i_word_div_nonneg:
  ∀(w1:256 word) (w2:256 word).
    0 ≤ w2i w1 ∧ 0 < w2i w2 ⇒
    w2i (w1 // w2) = &(w2n w1) / &(w2n w2)
Proof
  rpt strip_tac >>
  imp_res_tac w2i_nonneg_eq_w2n >> imp_res_tac w2n_lt_int_min_of_nonneg >>
  `0 ≤ w2i w2` by intLib.ARITH_TAC >>
  imp_res_tac w2i_nonneg_eq_w2n >> imp_res_tac w2n_lt_int_min_of_nonneg >>
  `w2n w2 ≠ 0` by (strip_tac >> fs[integer_wordTheory.w2i_eq_0,
                                     integer_wordTheory.word_0_w2i] >>
                    intLib.ARITH_TAC) >>
  `0 < w2n w2` by DECIDE_TAC >>
  simp[wordsTheory.word_div_def] >>
  `w2n w1 DIV w2n w2 ≤ w2n w1` by simp[arithmeticTheory.DIV_LESS_EQ] >>
  `w2n w1 DIV w2n w2 < INT_MIN(:256)` by DECIDE_TAC >>
  `w2n w1 DIV w2n w2 < dimword(:256)` by (
    mp_tac (INST_TYPE [alpha |-> ``:256``] wordsTheory.dimword_IS_TWICE_INT_MIN) >>
    DECIDE_TAC) >>
  simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD, w2i_n2w_small,
       integerTheory.INT_DIV]
QED

Theorem eval_range_div_sound:
  ∀r1 r2 (w1:256 word) (w2:256 word).
    in_range r1 w1 ∧ in_range r2 w2 ⇒
    in_range (eval_range_div r1 r2) (if w2 = 0w then 0w else w1 // w2)
Proof
  rpt strip_tac >> COND_CASES_TAC
  >- (
    gvs[] >> Cases_on `r1` >> Cases_on `r2` >>
    fs[in_range_bottom, eval_range_div_def, in_range_top, in_range_def] >>
    rpt IF_CASES_TAC >>
    gvs[in_range_top, in_range_constant, integer_wordTheory.word_0_w2i,
        in_range_def] >> intLib.ARITH_TAC
  )
  >>
  Cases_on `r1` >> Cases_on `r2` >>
  fs[in_range_bottom, eval_range_div_def, in_range_top, in_range_def] >>
  rpt strip_tac >> rpt IF_CASES_TAC >>
  gvs[in_range_top, in_range_constant, in_range_def] >>
  (* Close lo2=hi2=0 contradiction (w2i w2=0 ⇒ w2=0w) *)
  TRY (`w2i w2 = 0` by intLib.ARITH_TAC >>
       gvs[integer_wordTheory.w2i_eq_0] >> NO_TAC) >>
  (* lo2 < 0 case: w2n(w1) < w2n(w2), unsigned div = 0 *)
  TRY (`0 ≤ w2i w1` by intLib.ARITH_TAC >>
       `w2i w2 < 0` by intLib.ARITH_TAC >>
       `w2n w1 < w2n w2` by (irule cross_sign_w2n >> simp[]) >>
       `w2n w1 DIV w2n w2 = 0` by simp[arithmeticTheory.LESS_DIV_EQ_ZERO] >>
       simp[wordsTheory.word_div_def, wordsTheory.w2n_n2w,
            wordsTheory.dimword_def, dim256,
            integer_wordTheory.word_0_w2i] >> NO_TAC) >>
  (* Main: lo1 ≥ 0, lo2 > 0 *)
  `0 ≤ w2i w1 ∧ 0 ≤ w2i w2 ∧ 0 < w2i w2` by intLib.ARITH_TAC >>
  imp_res_tac w2i_nonneg_eq_w2n >>
  `i' = w2i w2` by intLib.ARITH_TAC >> pop_assum SUBST_ALL_TAC >>
  mp_tac (Q.SPECL [`w1`, `w2`] w2i_word_div_nonneg) >>
  asm_rewrite_tac[] >>
  disch_then SUBST1_TAC >>
  conj_tac >> irule int_div_le_mono >> intLib.ARITH_TAC
QED

(* ===== Unsigned MOD soundness ===== *)

Theorem eval_range_mod_sound:
  ∀r1 r2 (w1:256 word) (w2:256 word).
    in_range r1 w1 ∧ in_range r2 w2 ⇒
    in_range (eval_range_mod r1 r2) (if w2 = 0w then 0w else word_mod w1 w2)
Proof
  Cases >> Cases >>
  simp[eval_range_mod_def, in_range_top, in_range_def] >>
  rpt strip_tac >> rpt IF_CASES_TAC >>
  gvs[in_range_top, in_range_constant, in_range_def]
  (* lo2 = hi2 = 0 → safe_mod gives 0 *)
  >- (gvs[integer_wordTheory.w2i_eq_0, integer_wordTheory.word_0_w2i])
  (* lo2 = hi2 > 0: mod result in [0, lo2-1] *)
  >> TRY (
    `0 ≤ w2i w2` by intLib.ARITH_TAC >>
    imp_res_tac w2i_nonneg_eq_w2n >> imp_res_tac w2n_lt_int_min_of_nonneg >>
    `w2n w2 ≠ 0` by (strip_tac >> fs[integer_wordTheory.w2i_eq_0,
                                       integer_wordTheory.word_0_w2i] >>
                      intLib.ARITH_TAC) >>
    `0 < w2n w2` by DECIDE_TAC >>
    simp[wordsTheory.word_mod_def] >>
    `w2n w1 MOD w2n w2 < w2n w2` by simp[arithmeticTheory.MOD_LESS] >>
    `w2n w1 MOD w2n w2 < INT_MIN(:256)` by DECIDE_TAC >>
    `w2n w1 MOD w2n w2 < dimword(:256)` by (
      mp_tac (INST_TYPE [alpha |-> ``:256``] wordsTheory.dimword_IS_TWICE_INT_MIN) >>
      DECIDE_TAC) >>
    simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD, w2i_n2w_small] >>
    gvs[] >>
    `Num (w2i w2) = w2n w2` by simp[integerTheory.NUM_OF_INT] >>
    gvs[] >> intLib.ARITH_TAC >> NO_TAC)
  (* lo2 = hi2 = 0, w2 ≠ 0: contradiction *)
  >> gvs[integer_wordTheory.word_0_w2i] >> intLib.ARITH_TAC
QED

(* ===== AND soundness ===== *)

Triviality i2w_neg1_is_max[local]:
  i2w (-1) = UINT_MAXw : 256 word
Proof
  simp[integer_wordTheory.i2w_minus_1, wordsTheory.WORD_NEG_1]
QED

Triviality w2i_neg1_eq[local]:
  w2i (i2w (-1) : 256 word) = -1
Proof
  simp[integer_wordTheory.w2i_i2w, wordsTheory.INT_MIN_def,
       integer_wordTheory.INT_MIN_def, integer_wordTheory.INT_MAX_def, dim256]
QED

(* When w2i w = -1, w is all-ones (UINT_MAXw), so AND is identity *)
Triviality and_mask_neg1[local]:
  ∀(w:256 word) (w2:256 word). w2i w = -1 ⇒ word_and w w2 = w2
Proof
  rpt strip_tac >>
  `w = i2w (-1)` by metis_tac[integer_wordTheory.w2i_11, w2i_neg1_eq] >>
  simp[i2w_neg1_is_max, wordsTheory.WORD_AND_CLAUSES]
QED

(* AND with two nonneg operands: result in [0, min(bound1, bound2)] *)
Triviality and_nonneg_bounded[local]:
  ∀(w1:256 word) (w2:256 word) b1 b2.
    0 ≤ w2i w1 ∧ 0 ≤ w2i w2 ∧ w2i w1 ≤ b1 ∧ w2i w2 ≤ b2 ⇒
    0 ≤ w2i (w1 && w2) ∧ w2i (w1 && w2) ≤ b1 ∧ w2i (w1 && w2) ≤ b2
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`w1`, `w2`] w2i_word_and_nonneg) >>
  mp_tac (ONCE_REWRITE_RULE[wordsTheory.WORD_AND_COMM]
    (Q.SPECL [`w2`, `w1`] w2i_word_and_nonneg)) >>
  intLib.ARITH_TAC
QED

Theorem eval_range_and_sound:
  ∀r1 r2 w1 w2 lit1 lit2.
    in_range r1 w1 ∧ in_range r2 w2 ∧
    (∀v. lit1 = SOME v ⇒ w2i w1 = v) ∧
    (∀v. lit2 = SOME v ⇒ w2i w2 = v) ⇒
    in_range (eval_range_and r1 r2 lit1 lit2) (word_and w1 w2)
Proof
  Cases >> Cases >>
  simp[eval_range_and_def, in_range_top, in_range_def, LET_THM,
       vr_lo_def, vr_hi_def] >>
  rpt strip_tac >>
  Cases_on `lit1` >> Cases_on `lit2` >>
  simp[in_range_top] >>
  gvs[] >> rpt IF_CASES_TAC >> gvs eval_range_gvs_args >>
  TRY (simp[in_range_top] >> NO_TAC) >>
  vr_top_contra_tac >>
  (* -1 mask: AND with all-ones is identity *)
  TRY (imp_res_tac and_mask_neg1 >> gvs[in_range_def] >> intLib.ARITH_TAC >> NO_TAC) >>
  TRY (ONCE_REWRITE_TAC[wordsTheory.WORD_AND_COMM] >>
       imp_res_tac and_mask_neg1 >> gvs[in_range_def] >> intLib.ARITH_TAC >> NO_TAC) >>
  (* nonneg mask: direct bound *)
  TRY (
    mp_tac (Q.SPECL [`w1`, `w2`] w2i_word_and_nonneg) >>
    simp[integerTheory.INT_MIN] >> intLib.ARITH_TAC >> NO_TAC) >>
  (* symmetric bound *)
  TRY (
    mp_tac (ONCE_REWRITE_RULE[wordsTheory.WORD_AND_COMM]
      (Q.SPECL [`w2`, `w1`] w2i_word_and_nonneg)) >>
    simp[integerTheory.INT_MIN] >> intLib.ARITH_TAC >> NO_TAC) >>
  (* int_min: need both bounds *)
  mp_tac (Q.SPECL [`w1`, `w2`] w2i_word_and_nonneg) >>
  mp_tac (ONCE_REWRITE_RULE[wordsTheory.WORD_AND_COMM]
    (Q.SPECL [`w2`, `w1`] w2i_word_and_nonneg)) >>
  simp[integerTheory.INT_MIN] >> intLib.ARITH_TAC
QED

(* ===== Shared shift infrastructure (SHR, SAR, SHL) ===== *)

(* Negative w2i ⇒ w2n ≥ dimindex (shift overflows word width) *)
Triviality neg_w2i_ge_dimindex[local]:
  ∀(w:256 word). w2i w < 0 ⇒ w2n w ≥ dimindex(:256)
Proof
  rpt strip_tac >>
  CCONTR_TAC >> fs[arithmeticTheory.NOT_GREATER_EQ] >>
  `w2n w < INT_MIN(:256)` by (
    simp[wordsTheory.INT_MIN_def, dim256] >> DECIDE_TAC) >>
  `0 ≤ w2i w` by (
    REWRITE_TAC[w2i_eq_w2n_256] >>
    first_x_assum (mp_tac o REWRITE_RULE [w2i_eq_w2n_256]) >>
    mp_tac (Q.SPEC `w` (INST_TYPE [alpha |-> ``:256``] wordsTheory.w2n_lt)) >>
    mp_tac (INST_TYPE [alpha |-> ``:256``] wordsTheory.dimword_IS_TWICE_INT_MIN) >>
    rpt IF_CASES_TAC >> rpt strip_tac >> intLib.ARITH_TAC) >>
  intLib.ARITH_TAC
QED

(* Non-negative w2i ≥ 256 ⇒ w2n ≥ dimindex *)
Triviality nonneg_w2i_ge_dimindex[local]:
  ∀(w:256 word). 0 ≤ w2i w ∧ w2i w ≥ 256 ⇒ w2n w ≥ dimindex(:256)
Proof
  rpt strip_tac >>
  imp_res_tac w2i_nonneg_eq_w2n >>
  simp[dim256] >> intLib.ARITH_TAC
QED

(* ===== SHR soundness ===== *)

(* SHR negative shift: shift ≥ wordsize → 0w *)
Triviality shr_neg_shift[local]:
  ∀(w1:256 word) (w2:256 word). w2i w1 < 0 ⇒ w2 ⋙ w2n w1 = 0w
Proof
  rpt strip_tac >> imp_res_tac neg_w2i_ge_dimindex >>
  simp[wordsTheory.LSR_LIMIT]
QED

(* SHR big nonneg shift: shift ≥ 256 → 0w *)
Triviality shr_big_shift[local]:
  ∀(w1:256 word) (w2:256 word). 0 ≤ w2i w1 ∧ w2i w1 ≥ 256 ⇒
    w2 ⋙ w2n w1 = 0w
Proof
  rpt strip_tac >> imp_res_tac nonneg_w2i_ge_dimindex >>
  simp[wordsTheory.LSR_LIMIT]
QED

(* Bridge: w2i(w ⋙ n) = w2i w / &(2^n) for nonneg w2i.
   Reused by SHR and SAR. *)
Triviality w2i_lsr_nonneg[local]:
  ∀(w:256 word) n.
    0 ≤ w2i w ⇒ w2i (w ⋙ n) = w2i w / &(2 ** n)
Proof
  rpt strip_tac >>
  imp_res_tac w2i_nonneg_eq_w2n >>
  imp_res_tac w2n_lt_int_min_of_nonneg >>
  `w2n w DIV 2 ** n ≤ w2n w` by simp[arithmeticTheory.DIV_LESS_EQ] >>
  `w2n w DIV 2 ** n < INT_MIN(:256)` by DECIDE_TAC >>
  `w2n w DIV 2 ** n < dimword(:256)` by (
    mp_tac (INST_TYPE [alpha |-> ``:256``]
            wordsTheory.dimword_IS_TWICE_INT_MIN) >>
    DECIDE_TAC) >>
  REWRITE_TAC[w2i_eq_w2n_256, wordsTheory.w2n_lsr] >>
  ASM_SIMP_TAC std_ss [integerTheory.INT_DIV] >>
  rpt IF_CASES_TAC >> intLib.ARITH_TAC
QED

(* SHR main case: 0 ≤ sh < 256, lo ≥ 0 *)
Triviality shr_main[local]:
  ∀(w1:256 word) (w2:256 word) lo hi.
    0 ≤ lo ∧ lo ≤ w2i w2 ∧ w2i w2 ≤ hi ∧
    0 ≤ w2i w1 ⇒
    lo / &(2 ** w2n w1) ≤ w2i (w2 ⋙ w2n w1) ∧
    w2i (w2 ⋙ w2n w1) ≤ hi / &(2 ** w2n w1)
Proof
  rpt gen_tac >> strip_tac >>
  `0 ≤ w2i w2` by intLib.ARITH_TAC >>
  imp_res_tac w2i_lsr_nonneg >> gvs[] >>
  conj_tac >> irule int_div_le_mono >> simp[]
QED

Theorem eval_range_shr_sound:
  ∀r1 r2 w1 w2 lit1.
    in_range r1 w1 ∧ in_range r2 w2 ∧
    (∀v. lit1 = SOME v ⇒ w2i w1 = v) ⇒
    in_range (eval_range_shr r1 r2 lit1) (word_lsr w2 (w2n w1))
Proof
  Cases >> Cases >>
  simp[eval_range_shr_def, in_range_top, in_range_def, LET_THM,
       vr_lo_def, vr_hi_def] >>
  rpt strip_tac >>
  Cases_on `lit1` >> simp[in_range_top] >>
  rpt IF_CASES_TAC >> gvs eval_range_gvs_args >>
  TRY (imp_res_tac shr_neg_shift >>
       simp[integer_wordTheory.word_0_w2i] >> NO_TAC) >>
  TRY (imp_res_tac shr_big_shift >>
       simp[integer_wordTheory.word_0_w2i] >> NO_TAC) >>
  TRY (
    imp_res_tac w2i_nonneg_eq_w2n >>
    gvs[integerTheory.NUM_OF_INT] >>
    match_mp_tac shr_main >> simp[] >> intLib.ARITH_TAC >> NO_TAC) >>
  vr_top_contra_tac
QED

(* ===== SDIV soundness ===== *)

(*
 * sdiv helpers: exclude the INT_MINw / i2w(-1) overflow case.
 * Both const_const and const_const_neg need the same overflow exclusion.
 * Factor out the shared reasoning.
 *)
val INT_MIN_eq_INT256_MIN = prove(
  ``integer_word$INT_MIN(:256) = INT256_MIN``,
  simp[integer_wordTheory.INT_MIN_def, INT256_MIN_def, INT256_MAX_def,
       integer_wordTheory.INT_MAX_def, wordsTheory.INT_MIN_def, dim256]);
val w2i_INT_MINw_eq =
  REWRITE_RULE [INT_MIN_eq_INT256_MIN]
    (INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_INT_MINw);
  (* ⊢ w2i INT_MINw = INT256_MIN *)
val w2i_i2w_neg1_256 = prove(
  ``w2i (i2w (-1) : 256 word) = -1``,
  mp_tac w2i_i2w_256 >> simp[INT256_MIN_def, INT256_MAX_def,
    integer_wordTheory.INT_MAX_def, integer_wordTheory.INT_MIN_def,
    wordsTheory.INT_MIN_def, dim256] >> intLib.ARITH_TAC);

val sdiv_not_overflow_tac =
  strip_tac >> gvs[] >> fs[w2i_INT_MINw_eq, w2i_i2w_neg1_256];

Triviality sdiv_const_const[local]:
  ∀(w1:256 word) (w2:256 word) i i'.
    w2i w1 = i ∧ w2i w2 = i' ∧ w2 ≠ 0w ∧ i' ≠ 0 ∧
    (i = INT256_MIN ⇒ i' ≠ -1) ∧
    ((i < 0) ⇔ (i' < 0)) ⇒
    w2i (w1 / w2) = ABS i / ABS i'
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`w1`, `w2`] w2i_word_quot) >>
  impl_tac >- (conj_tac >- simp[] >> sdiv_not_overflow_tac) >>
  strip_tac >> gvs[] >> simp[quot_sign_abs]
QED

Triviality sdiv_const_const_neg[local]:
  ∀(w1:256 word) (w2:256 word) i i'.
    w2i w1 = i ∧ w2i w2 = i' ∧ w2 ≠ 0w ∧ i' ≠ 0 ∧
    (i = INT256_MIN ⇒ i' ≠ -1) ∧
    ((i < 0) ⇎ (i' < 0)) ⇒
    w2i (w1 / w2) = -1 * (ABS i / ABS i')
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`w1`, `w2`] w2i_word_quot) >>
  impl_tac >- (conj_tac >- simp[] >> sdiv_not_overflow_tac) >>
  strip_tac >> gvs[] >> simp[quot_sign_abs]
QED


Triviality sdiv_range_nonneg[local]:
  ∀(w1:256 word) (w2:256 word) lo hi d.
    lo ≤ w2i w1 ∧ w2i w1 ≤ hi ∧ w2i w2 = d ∧ w2 ≠ 0w ∧
    lo ≥ 0 ∧ d > 0 ⇒
    lo / d ≤ w2i (w1 / w2) ∧ w2i (w1 / w2) ≤ hi / d
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`w1`, `w2`] w2i_word_quot) >>
  impl_tac >- (conj_tac >- simp[] >> sdiv_not_overflow_tac) >>
  strip_tac >> gvs[] >>
  `0 ≤ w2i w1` by intLib.ARITH_TAC >>
  `0 < w2i w2` by intLib.ARITH_TAC >>
  simp[nonneg_quot_eq] >>
  conj_tac >> irule int_div_le_mono >> simp[]
QED

Triviality sdiv_range_neg[local]:
  ∀(w1:256 word) (w2:256 word) lo hi d.
    lo ≤ w2i w1 ∧ w2i w1 ≤ hi ∧ w2i w2 = d ∧ w2 ≠ 0w ∧
    hi < 0 ∧ d > 0 ⇒
    -(ABS lo / d) ≤ w2i (w1 / w2) ∧ w2i (w1 / w2) ≤ -(ABS hi / d)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`w1`, `w2`] w2i_word_quot) >>
  impl_tac >- (conj_tac >- simp[] >> sdiv_not_overflow_tac) >>
  strip_tac >> gvs[] >>
  `w2i w1 < 0` by intLib.ARITH_TAC >>
  `lo < 0` by intLib.ARITH_TAC >>
  `0 < w2i w2` by intLib.ARITH_TAC >>
  simp[neg_quot_eq] >>
  conj_tac >| [
    `ABS (w2i w1) / w2i w2 ≤ ABS lo / w2i w2` suffices_by intLib.ARITH_TAC >>
    irule int_div_le_mono >> simp[] >>
    simp[integerTheory.INT_ABS_LE] >> intLib.ARITH_TAC,
    `ABS hi / w2i w2 ≤ ABS (w2i w1) / w2i w2` suffices_by intLib.ARITH_TAC >>
    irule int_div_le_mono >> simp[] >>
    simp[integerTheory.INT_ABS_LE] >> intLib.ARITH_TAC
  ]
QED

Triviality sdiv_range_mixed[local]:
  ∀(w1:256 word) (w2:256 word) lo hi d.
    lo ≤ w2i w1 ∧ w2i w1 ≤ hi ∧ w2i w2 = d ∧ w2 ≠ 0w ∧
    lo < 0 ∧ hi ≥ 0 ∧ d > 0 ⇒
    -(ABS lo / d) ≤ w2i (w1 / w2) ∧ w2i (w1 / w2) ≤ hi / d
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`w1`, `w2`] w2i_word_quot) >>
  impl_tac >- (conj_tac >- simp[] >> sdiv_not_overflow_tac) >>
  strip_tac >> gvs[] >>
  `0 < w2i w2` by intLib.ARITH_TAC >>
  `lo < 0` by intLib.ARITH_TAC >>
  `lo quot w2i w2 ≤ w2i w1 quot w2i w2` by
    (match_mp_tac quot_mono_pos_denom >> simp[]) >>
  `lo quot w2i w2 = -(ABS lo / w2i w2)` by
    (match_mp_tac neg_quot_eq >> simp[]) >>
  `0 ≤ hi` by intLib.ARITH_TAC >>
  `w2i w1 quot w2i w2 ≤ hi quot w2i w2` by
    (match_mp_tac quot_mono_pos_denom >> simp[]) >>
  `hi quot w2i w2 = hi / w2i w2` by
    (match_mp_tac nonneg_quot_eq >> simp[]) >>
  intLib.ARITH_TAC
QED

Theorem eval_range_sdiv_sound:
  ∀r1 r2 (w1:256 word) (w2:256 word).
    in_range r1 w1 ∧ in_range r2 w2 ⇒
    in_range (eval_range_sdiv r1 r2) (if w2 = 0w then 0w else w1 / w2)
Proof
  Cases >> Cases >>
  simp[eval_range_sdiv_def, in_range_top, in_range_def, LET_THM] >>
  rpt strip_tac >> rpt IF_CASES_TAC >>
  gvs[in_range_top, in_range_constant, in_range_def,
      integer_wordTheory.w2i_eq_0, integer_wordTheory.word_0_w2i] >>
  TRY (intLib.ARITH_TAC >> NO_TAC) >>
  (* Zero divisor: w2i w2 = 0 → contradiction *)
  TRY (`w2i w2 = 0` by intLib.ARITH_TAC >>
    `w2 = 0w` by metis_tac[integer_wordTheory.w2i_eq_0] >> gvs[] >> NO_TAC) >>
  (* Overflow: w2i w1 = INT256_MIN, w2i w2 = -1 *)
  TRY (`w2i w1 = INT256_MIN` by intLib.ARITH_TAC >>
    `w2i w2 = -1` by intLib.ARITH_TAC >>
    `w1 = INT_MINw` by metis_tac[integer_wordTheory.w2i_11, w2i_INT_MINw_eq] >>
    `w2 = i2w(-1)` by metis_tac[integer_wordTheory.w2i_11, w2i_i2w_neg1_256] >>
    gvs[sdiv_overflow] >> NO_TAC) >>
  (* Const/const *)
  TRY (irule sdiv_const_const >> simp[] >> intLib.ARITH_TAC >> NO_TAC) >>
  TRY (irule sdiv_const_const_neg >> simp[] >> intLib.ARITH_TAC >> NO_TAC) >>
  (* Range: nonneg, neg, mixed *)
  TRY (match_mp_tac sdiv_range_nonneg >>
    simp[integerTheory.INT_NOT_LT] >> intLib.ARITH_TAC >> NO_TAC) >>
  TRY (match_mp_tac sdiv_range_neg >>
    simp[integerTheory.INT_NOT_LT, int_ge] >> intLib.ARITH_TAC >> NO_TAC) >>
  TRY (match_mp_tac sdiv_range_mixed >>
    simp[integerTheory.INT_NOT_LT, int_ge] >> intLib.ARITH_TAC >> NO_TAC)
QED

(* ===== SMOD soundness ===== *)

(* Pure integer helpers for remainder bounds *)
val w2i_word_rem_256 =
  INST_TYPE [alpha |-> ``:256``] w2i_word_rem;

Triviality rem_nonneg_le[local]:
  ∀(a:int) d. d ≠ 0 ∧ 0 ≤ a ⇒ a rem d ≤ a
Proof
  rpt strip_tac >>
  (* Reduce to d > 0 case: a rem (-d) = a rem d by INT_REM_NEG *)
  `a rem d = a rem (ABS d)` by (
    Cases_on `0 < d` >- (`ABS d = d` by intLib.ARITH_TAC >> simp[]) >>
    `d < 0` by intLib.ARITH_TAC >>
    `ABS d = -d` by intLib.ARITH_TAC >>
    mp_tac (Q.SPECL [`a`, `d`] integerTheory.INT_REM_NEG) >>
    simp[]) >>
  `0 < ABS d` by intLib.ARITH_TAC >>
  `ABS d ≠ 0` by intLib.ARITH_TAC >>
  (* Now prove a rem (ABS d) ≤ a when 0 ≤ a and ABS d > 0 *)
  `a quot (ABS d) = a / (ABS d)` by
    (match_mp_tac nonneg_quot_eq >> simp[]) >>
  `0 ≤ a / (ABS d)` by
    (match_mp_tac int_div_nonneg >> simp[]) >>
  mp_tac (Q.SPEC `ABS d` integerTheory.INT_REMQUOT) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then `a` strip_assume_tac) >>
  `0 ≤ a quot (ABS d) * (ABS d)` by
    (match_mp_tac integerTheory.INT_LE_MUL >> simp[] >> intLib.ARITH_TAC) >>
  intLib.ARITH_TAC
QED

Triviality rem_nonpos_ge[local]:
  ∀(a:int) d. d ≠ 0 ∧ a ≤ 0 ⇒ a ≤ a rem d
Proof
  rpt strip_tac >>
  `0 ≤ -a` by intLib.ARITH_TAC >>
  `(-a) rem d ≤ -a` by (match_mp_tac rem_nonneg_le >> simp[]) >>
  `-(a rem d) = (-a) rem d` by (
    mp_tac (Q.SPECL [`a`, `d`] integerTheory.INT_REM_NEG) >> simp[]) >>
  intLib.ARITH_TAC
QED

(* Shared tactic: bridge word_rem to int rem, abstract to pure ints *)
val smod_bridge_tac =
  drule w2i_word_rem_256 >> strip_tac >> gvs[] >>
  qabbrev_tac `a = w2i w1` >> qabbrev_tac `b = w2i w2` >>
  `b ≠ 0` by simp[markerTheory.Abbrev_def] >>
  qpat_x_assum `∀x. _` kall_tac >>
  qpat_x_assum `Abbrev (a = _)` kall_tac >>
  qpat_x_assum `Abbrev (b = _)` kall_tac >>
  qpat_x_assum `w2 ≠ _` kall_tac;

(* Helper: nonneg dividend *)
Triviality smod_range_nonneg[local]:
  ∀(w1:256 word) (w2:256 word) lo hi d.
    lo ≤ w2i w1 ∧ w2i w1 ≤ hi ∧ w2i w2 = d ∧ w2 ≠ 0w ∧
    d ≠ 0 ∧ lo ≥ 0 ⇒
    0 ≤ w2i (word_rem w1 w2) ∧
    w2i (word_rem w1 w2) ≤ int_min (ABS d - 1) hi
Proof
  rpt gen_tac >> strip_tac >> smod_bridge_tac >>
  `0 ≤ a` by intLib.ARITH_TAC >>
  (* 0 ≤ a rem b *)
  mp_tac (Q.SPEC `b` integerTheory.INT_REMQUOT) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then `a` strip_assume_tac) >>
  `0 ≤ a rem b` by (Cases_on `0 < a` >> fs[] >>
    `a = 0` by intLib.ARITH_TAC >> gvs[integerTheory.INT_REM0]) >>
  (* a rem b ≤ ABS b - 1 (from ABS(a rem b) < ABS b) *)
  `a rem b ≤ ABS b - 1` by intLib.ARITH_TAC >>
  (* a rem b ≤ a ≤ hi *)
  `a rem b ≤ a` by (match_mp_tac rem_nonneg_le >> simp[]) >>
  (* Combine: a rem b ≤ int_min (ABS b - 1) hi *)
  simp[integerTheory.INT_MIN] >> intLib.ARITH_TAC
QED

(* Helper: nonpos dividend *)
Triviality smod_range_neg[local]:
  ∀(w1:256 word) (w2:256 word) lo hi d.
    lo ≤ w2i w1 ∧ w2i w1 ≤ hi ∧ w2i w2 = d ∧ w2 ≠ 0w ∧
    d ≠ 0 ∧ hi ≤ 0 ⇒
    int_max (1 - ABS d) lo ≤ w2i (word_rem w1 w2) ∧
    w2i (word_rem w1 w2) ≤ 0
Proof
  rpt gen_tac >> strip_tac >> smod_bridge_tac >>
  `a ≤ 0` by intLib.ARITH_TAC >>
  (* a rem b ≤ 0 *)
  mp_tac (Q.SPEC `b` integerTheory.INT_REMQUOT) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then `a` strip_assume_tac) >>
  `a rem b ≤ 0` by (Cases_on `0 < a` >> fs[] >> intLib.ARITH_TAC) >>
  (* -(ABS b - 1) ≤ a rem b (from ABS(a rem b) < ABS b) *)
  `1 - ABS b ≤ a rem b` by intLib.ARITH_TAC >>
  (* a ≤ a rem b (from rem_nonpos_ge) *)
  `a ≤ a rem b` by (match_mp_tac rem_nonpos_ge >> simp[]) >>
  simp[integerTheory.INT_MAX] >> intLib.ARITH_TAC
QED

(* Helper: mixed sign dividend *)
Triviality smod_range_mixed[local]:
  ∀(w1:256 word) (w2:256 word) d.
    w2i w2 = d ∧ w2 ≠ 0w ∧ d ≠ 0 ⇒
    1 - ABS d ≤ w2i (word_rem w1 w2) ∧
    w2i (word_rem w1 w2) ≤ ABS d - 1
Proof
  rpt gen_tac >> strip_tac >> smod_bridge_tac >>
  mp_tac (Q.SPEC `b` integerTheory.INT_REMQUOT) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then `a` strip_assume_tac) >>
  intLib.ARITH_TAC
QED

Theorem eval_range_smod_sound:
  ∀r1 r2 (w1:256 word) (w2:256 word).
    in_range r1 w1 ∧ in_range r2 w2 ⇒
    in_range (eval_range_smod r1 r2) (if w2 = 0w then 0w else word_rem w1 w2)
Proof
  Cases >> Cases >>
  simp[eval_range_smod_def, in_range_top, in_range_def, LET_THM] >>
  rpt strip_tac >> rpt IF_CASES_TAC >>
  gvs[in_range_top, in_range_constant, in_range_def] >>
  TRY (gvs[integer_wordTheory.w2i_eq_0, integer_wordTheory.word_0_w2i] >> NO_TAC) >>
  TRY (`w2i w2 = 0` by intLib.ARITH_TAC >>
    `w2 = 0w` by metis_tac[integer_wordTheory.w2i_eq_0] >> gvs[] >> NO_TAC) >>
  (* Remaining real goals: nonneg, neg, mixed *)
  TRY (match_mp_tac smod_range_nonneg >>
    simp[integerTheory.INT_NOT_LT, int_ge] >> intLib.ARITH_TAC >> NO_TAC) >>
  TRY (match_mp_tac smod_range_neg >>
    simp[integerTheory.INT_NOT_LT, int_ge] >> intLib.ARITH_TAC >> NO_TAC) >>
  TRY (match_mp_tac smod_range_mixed >>
    simp[integerTheory.INT_NOT_LT, int_ge] >> intLib.ARITH_TAC >> NO_TAC) >>
  gvs[integer_wordTheory.word_0_w2i] >>
  intLib.ARITH_TAC
QED

(* ===== SHL soundness ===== *)

(* SHL huge shift: n ≥ 256 ⇒ result is 0 *)
Triviality shl_huge_zero[local]:
  ∀(w:256 word) n. dimindex(:256) ≤ n ⇒ w ≪ n = 0w
Proof
  metis_tac[wordsTheory.LSL_LIMIT]
QED

(* For nonneg shift < 255, w2i(n2w(2^n)) = &(2^n) *)
Triviality w2i_n2w_pow2[local]:
  ∀n. n < 255 ⇒ w2i (n2w (2 ** n) : 256 word) = &(2 ** n)
Proof
  rpt strip_tac >>
  irule integer_wordTheory.w2i_n2w_pos >>
  simp[wordsTheory.INT_MIN_def, dim256] >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac `2 ** 255` >>
  simp[logrootTheory.LT_EXP_ISO]
QED

(* SHL bridge for nonneg shift < 255:
   w2i(w ≪ n) = wrap256_signed(w2i w * &(2^n)) *)
Triviality wrap256_signed_add_dimword[local]:
  ∀(x:int) k. wrap256_signed (x + k * &dimword(:256)) = wrap256_signed x
Proof
  rpt strip_tac >> simp[wrap256_alt] >>
  qabbrev_tac `D = &dimword(:256):int` >>
  qabbrev_tac `M = &INT_MIN(:256):int` >>
  `x + k * D + M = k * D + (x + M)` by intLib.ARITH_TAC >>
  pop_assum SUBST1_TAC >>
  `(k * D + (x + M)) % D = (x + M) % D` suffices_by simp[] >>
  irule integerTheory.INT_MOD_ADD_MULTIPLES >>
  simp[Abbr `D`, wordsTheory.dimword_def, dim256]
QED

Triviality i2w_wrap256_signed[local]:
  ∀b. i2w (wrap256_signed b) = i2w b : 256 word
Proof
  simp[GSYM w2i_i2w_wrap256, integer_wordTheory.i2w_w2i]
QED

Triviality wrap256_signed_mul_wrap[local]:
  ∀(a:int) b. wrap256_signed (a * wrap256_signed b) = wrap256_signed (a * b)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[GSYM w2i_i2w_wrap256] >>
  AP_TERM_TAC >>
  REWRITE_TAC[GSYM integer_wordTheory.word_i2w_mul, i2w_wrap256_signed]
QED

Triviality w2i_n2w_wrap256[local]:
  ∀k. w2i (n2w k : 256 word) = wrap256_signed (&k)
Proof
  rpt strip_tac >>
  `n2w k = i2w (&k) : 256 word` by
    simp[integer_wordTheory.i2w_def] >>
  pop_assum SUBST1_TAC >>
  simp[w2i_i2w_wrap256]
QED

Triviality w2i_lsl_wrap256[local]:
  ∀(w:256 word) n. n < 256 ⇒
    w2i (w ≪ n) = wrap256_signed (w2i w * &(2 ** n))
Proof
  rpt strip_tac >>
  REWRITE_TAC[wordsTheory.WORD_MUL_LSL] >>
  ONCE_REWRITE_TAC[wordsTheory.WORD_MULT_COMM] >>
  REWRITE_TAC[w2i_mul_wrap256, w2i_n2w_wrap256] >>
  REWRITE_TAC[wrap256_signed_mul_wrap]
QED

(* Helper: modular arithmetic for wrap256_signed *)
Triviality mod_dimword_nonneg[local]:
  ∀(v:int) M D. 0 ≤ v ∧ v < D ∧ D = 2 * M ∧ 0 < M ⇒
    (v + M) % D = if v < M then v + M else v - M
Proof
  rpt strip_tac >> IF_CASES_TAC >-
    (irule integerTheory.INT_LESS_MOD >> intLib.ARITH_TAC) >>
  `v + M = 1 * D + (v - M)` by intLib.ARITH_TAC >>
  pop_assum (fn eq => REWRITE_TAC[eq]) >>
  `(1 * D + (v - M)) % D = (v - M) % D` by
    (irule integerTheory.INT_MOD_ADD_MULTIPLES >> intLib.ARITH_TAC) >>
  pop_assum (fn eq => REWRITE_TAC[eq]) >>
  irule integerTheory.INT_LESS_MOD >> intLib.ARITH_TAC
QED

(* wrap256_signed monotonicity on nonneg interval without wrap inversion *)
Triviality wrap256_signed_mono_nonneg[local]:
  ∀(a:int) b c.
    0 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c < &dimword(:256) ∧
    wrap256_signed a ≤ wrap256_signed c ⇒
    wrap256_signed a ≤ wrap256_signed b ∧
    wrap256_signed b ≤ wrap256_signed c
Proof
  rpt gen_tac >> strip_tac >>
  RULE_ASSUM_TAC (REWRITE_RULE [wrap256_alt]) >>
  simp[wrap256_alt] >>
  qabbrev_tac `M = &INT_MIN(:256):int` >>
  `0 < M` by (simp[Abbr `M`] >>
    mp_tac (INST_TYPE [alpha |-> ``:256``] wordsTheory.ZERO_LT_INT_MIN) >> simp[]) >>
  `&dimword(:256) = 2 * M` by
    simp[Abbr `M`, wordsTheory.dimword_IS_TWICE_INT_MIN] >>
  `(a + M) % &dimword(:256) = if a < M then a + M else a - M` by
    (irule mod_dimword_nonneg >> simp[] >> intLib.ARITH_TAC) >>
  `(b + M) % &dimword(:256) = if b < M then b + M else b - M` by
    (irule mod_dimword_nonneg >> simp[] >> intLib.ARITH_TAC) >>
  `(c + M) % &dimword(:256) = if c < M then c + M else c - M` by
    (irule mod_dimword_nonneg >> simp[] >> intLib.ARITH_TAC) >>
  ntac 3 (pop_assum SUBST_ALL_TAC) >>
  qpat_x_assum `Abbrev _` kall_tac >>
  qpat_x_assum `&dimword(:256) = _` (fn eq =>
    RULE_ASSUM_TAC (REWRITE_RULE [eq])) >>
  rpt IF_CASES_TAC >> gvs[] >> intLib.ARITH_TAC
QED

(* INT_DIV_MUL_LE: (a/b)*b ≤ a for 0 < b *)
Triviality int_div_mul_le[local]:
  ∀(a:int) b. 0 < b ⇒ a / b * b ≤ a
Proof
  rpt strip_tac >>
  `b ≠ 0i` by intLib.ARITH_TAC >>
  mp_tac (Q.SPEC `b` integerTheory.INT_DIVISION) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then `a` strip_assume_tac) >>
  intLib.ARITH_TAC
QED

(* SHL core: nonneg value, bounded shift < 256 *)
Triviality shl_core_sound[local]:
  ∀(w1:256 word) (w2:256 word) lo hi sh.
    0 ≤ lo ∧ lo ≤ w2i w2 ∧ w2i w2 ≤ hi ∧
    0 ≤ sh ∧ sh < 256 ∧ w2i w1 = sh ∧
    hi ≤ UINT256_MAX_int / &(2 ** Num sh) ∧
    ¬(wrap256_signed (lo * &(2 ** Num sh)) >
      wrap256_signed (hi * &(2 ** Num sh))) ⇒
    in_range
      (VR_Range (wrap256_signed (lo * &(2 ** Num sh)))
                (wrap256_signed (hi * &(2 ** Num sh))))
      (w2 ≪ w2n w1)
Proof
  rpt gen_tac >> strip_tac >>
  `0 ≤ w2i w1` by intLib.ARITH_TAC >>
  imp_res_tac w2i_nonneg_eq_w2n >>
  `Num sh < 256` by (
    `Num sh < Num (&256:int)` suffices_by simp[integerTheory.NUM_OF_INT] >>
    simp[integerTheory.NUM_LT]) >>
  gvs[integerTheory.NUM_OF_INT] >>
  simp[in_range_def, w2i_lsl_wrap256] >>
  irule wrap256_signed_mono_nonneg >>
  `0 < &(2 ** w2n w1):int` by simp[] >>
  ONCE_REWRITE_TAC[integerTheory.INT_MUL_COMM] >>
  simp[integerTheory.INT_LE_MONO, integerTheory.INT_LE_MUL,
       integerTheory.INT_NOT_LT, int_gt] >>
  `hi * &(2 ** w2n w1) ≤ UINT256_MAX_int` suffices_by (
    simp[UINT256_MAX_def, integer_wordTheory.UINT_MAX_def,
         wordsTheory.dimword_def, dim256] >> intLib.ARITH_TAC) >>
  irule integerTheory.INT_LE_TRANS >>
  qexists_tac `UINT256_MAX_int / &(2 ** w2n w1) * &(2 ** w2n w1)` >>
  ONCE_REWRITE_TAC[integerTheory.INT_MUL_COMM] >>
  simp[integerTheory.INT_LE_MONO] >>
  ONCE_REWRITE_TAC[integerTheory.INT_MUL_COMM] >>
  match_mp_tac int_div_mul_le >> simp[]
QED

Triviality eval_range_shl_single[local]:
  ∀(w1:256 word) (w2:256 word) lo hi.
    lo ≤ w2i w2 ∧ w2i w2 ≤ hi ⇒
    in_range
      (if w2i w1 < 0 then vr_constant 0
       else if w2i w1 ≥ 256 then vr_constant 0
       else if lo < 0 then VR_Top
       else if hi > UINT256_MAX_int / &(2 ** Num (w2i w1)) then VR_Top
       else if wrap256_signed (lo * &(2 ** Num (w2i w1))) >
               wrap256_signed (hi * &(2 ** Num (w2i w1))) then VR_Top
       else VR_Range (wrap256_signed (lo * &(2 ** Num (w2i w1))))
                     (wrap256_signed (hi * &(2 ** Num (w2i w1)))))
      (w2 ≪ w2n w1)
Proof
  rpt gen_tac >> strip_tac >>
  IF_CASES_TAC
  >- (
    imp_res_tac neg_w2i_ge_dimindex >>
    simp[shl_huge_zero, in_range_constant,
         integer_wordTheory.word_0_w2i, dim256]
  ) >>
  IF_CASES_TAC
  >- (
    `0 ≤ w2i w1` by intLib.ARITH_TAC >>
    imp_res_tac nonneg_w2i_ge_dimindex >>
    simp[shl_huge_zero, in_range_constant,
         integer_wordTheory.word_0_w2i, dim256]
  ) >>
  IF_CASES_TAC >- simp[in_range_top] >>
  IF_CASES_TAC >- simp[in_range_top] >>
  IF_CASES_TAC >- simp[in_range_top] >>
  irule shl_core_sound >>
  gvs[int_gt, integerTheory.INT_NOT_LT, integerTheory.INT_NOT_LE,
      int_ge]
QED

Theorem eval_range_shl_sound:
  ∀r1 r2 w1 w2 lit1.
    in_range r1 w1 ∧ in_range r2 w2 ∧
    (∀v. lit1 = SOME v ⇒ w2i w1 = v) ⇒
    in_range (eval_range_shl r1 r2 lit1) (word_lsl w2 (w2n w1))
Proof
  Cases >> Cases >>
  simp[eval_range_shl_def, in_range_top, in_range_def, LET_THM,
       vr_lo_def, vr_hi_def] >>
  rpt strip_tac >>
  Cases_on `lit1` >> simp[in_range_top] >>
  rpt strip_tac >> gvs[] >>
  irule eval_range_shl_single >> simp[] >>
  strip_tac >>
  mp_tac (Q.SPEC `w2` w2i_ge_256) >>
  mp_tac (Q.SPEC `w2` w2i_le_256) >>
  mp_tac uint256_gt_int256 >> intLib.ARITH_TAC
QED

(* ===== SAR soundness ===== *)

(* Helper: INT_MIN ≤ x ≤ INT_MAX ⇒ INT_MIN ≤ x/2^n ≤ INT_MAX *)
Triviality one_le_pow2_int[local]:
  ∀n. (1:int) ≤ &(2 ** n)
Proof
  simp[integerTheory.INT_LE, integer_wordTheory.ONE_LE_TWOEXP]
QED

Triviality int_div_pow2_lower[local]:
  ∀(x:int) n. INT256_MIN ≤ x ⇒ INT256_MIN ≤ x / &(2 ** n)
Proof
  rpt strip_tac >>
  match_mp_tac integerTheory.INT_LE_TRANS >>
  qexists_tac `INT256_MIN / &(2 ** n)` >>
  CONJ_TAC
  >- (match_mp_tac int_div_neg_ge >>
      mp_tac int256_min_neg >> mp_tac (Q.SPEC `n` one_le_pow2_int) >>
      intLib.ARITH_TAC)
  >> match_mp_tac int_div_le_mono >>
  mp_tac (Q.SPEC `n` one_le_pow2_int) >> intLib.ARITH_TAC
QED

Triviality int_div_pow2_upper[local]:
  ∀(x:int) n. x ≤ INT256_MAX ⇒ x / &(2 ** n) ≤ INT256_MAX
Proof
  rpt strip_tac >>
  match_mp_tac integerTheory.INT_LE_TRANS >>
  qexists_tac `INT256_MAX / &(2 ** n)` >>
  CONJ_TAC
  >- (match_mp_tac int_div_le_mono >>
      mp_tac (Q.SPEC `n` one_le_pow2_int) >> intLib.ARITH_TAC)
  >> match_mp_tac int_div_le_dividend >>
  mp_tac int256_max_pos >> mp_tac (Q.SPEC `n` one_le_pow2_int) >>
  intLib.ARITH_TAC
QED

Triviality w2i_i2w_div_precond[local]:
  ∀(w:256 word) n.
    INT256_MIN ≤ w2i w / &(2 ** n) ∧ w2i w / &(2 ** n) ≤ INT256_MAX
Proof
  rpt gen_tac >> conj_tac >>
  TRY (match_mp_tac int_div_pow2_lower >> simp[w2i_ge_256] >> NO_TAC) >>
  match_mp_tac int_div_pow2_upper >> simp[w2i_le_256]
QED

(* Step 1 of bridge: i2w(w2i w / 2^n) = w ≫ n *)
Triviality i2w_div_w2i_is_asr[local]:
  ∀(w:256 word) n. n < 256 ⇒ i2w (w2i w / &(2 ** n)) = w ≫ n
Proof
  rpt strip_tac >>
  assume_tac (Q.SPEC `w` w2i_ge_256) >>
  assume_tac (Q.SPEC `w` w2i_le_256) >>
  drule_all (REWRITE_RULE [GSYM AND_IMP_INTRO]
    (INST_TYPE [alpha |-> ``:256``] i2w_DIV_256)) >>
  simp[integer_wordTheory.i2w_w2i]
QED

(* Bridge: w2i(w ≫ n) = w2i w / &(2^n) for n < 256 *)
Triviality w2i_asr_bridge[local]:
  ∀(w:256 word) n. n < 256 ⇒ w2i (w ≫ n) = w2i w / &(2 ** n)
Proof
  rpt strip_tac >>
  drule i2w_div_w2i_is_asr >> strip_tac >>
  (* have: i2w(w2i w / 2^n) = w ≫ n, so w ≫ n = i2w(...) *)
  `w ≫ n = (i2w (w2i w / &(2 ** n))):256 word` by metis_tac[] >>
  pop_assum (fn eq => REWRITE_TAC [eq]) >>
  (* goal: w2i(i2w(w2i w / 2^n)) = w2i w / 2^n *)
  mp_tac (Q.SPECL [`w`, `n`] w2i_i2w_div_precond) >> strip_tac >>
  drule_all (REWRITE_RULE [GSYM AND_IMP_INTRO] w2i_i2w_256) >>
  simp[]
QED

(* SAR main: bounds follow from bridge + monotonicity *)
Triviality sar_main[local]:
  ∀(w1:256 word) (w2:256 word) lo hi.
    lo ≤ w2i w2 ∧ w2i w2 ≤ hi ∧ 0 ≤ w2i w1 ∧ w2i w1 < 256 ⇒
    lo / &(2 ** w2n w1) ≤ w2i (w2 ≫ w2n w1) ∧
    w2i (w2 ≫ w2n w1) ≤ hi / &(2 ** w2n w1)
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac w2i_nonneg_eq_w2n >> gvs[integerTheory.NUM_OF_INT] >>
  `w2n w1 < 256` by intLib.ARITH_TAC >>
  imp_res_tac w2i_asr_bridge >> gvs[] >>
  conj_tac >> irule int_div_le_mono >> simp[]
QED

(* Helper: ASR by huge amount — deterministic based on sign of operand *)
Triviality asr_huge_w2i[local]:
  ∀(w:256 word) n. dimindex(:256) ≤ n ⇒
    w2i (w ≫ n) = if w2i w < 0 then -1 else 0
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac (INST_TYPE [alpha |-> ``:256``] wordsTheory.ASR_LIMIT) >>
  Cases_on `w2i w < 0` >> gvs[] >>
  fs[integer_wordTheory.w2i_lt_0, wordsTheory.word_msb_neg] >>
  simp[integer_wordTheory.w2i_UINT_MAXw, integer_wordTheory.word_0_w2i]
QED

(* Huge shift sub-case: dimindex ≤ w2n w1 *)
Triviality sar_huge_dimindex[local]:
  ∀(w1:256 word). w2i w1 < 0 ∨ w2i w1 ≥ 256 ⇒ dimindex(:256) ≤ w2n w1
Proof
  rpt strip_tac >>
  imp_res_tac neg_w2i_ge_dimindex >> simp[dim256] >>
  `0 ≤ w2i w1` by intLib.ARITH_TAC >>
  imp_res_tac nonneg_w2i_ge_dimindex >> simp[dim256]
QED

(* Huge shift: result is in {-1, 0} with sign determined by w2 *)
Triviality sar_huge_sound[local]:
  ∀(w1:256 word) (w2:256 word) lo hi.
    lo ≤ w2i w2 ∧ w2i w2 ≤ hi ∧
    (w2i w1 < 0 ∨ w2i w1 ≥ 256) ⇒
    in_range
      (if lo ≥ 0 then vr_constant 0
       else if hi < 0 then vr_constant (-1)
       else VR_Range (-1) 0)
      (w2 ≫ w2n w1)
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac sar_huge_dimindex >>
  `w2i (w2 ≫ w2n w1) = if w2i w2 < 0 then -1 else 0`
    by metis_tac[asr_huge_w2i] >>
  Cases_on `w2i w2 < 0` >> fs[] >>
  rpt IF_CASES_TAC >>
  fs[in_range_constant, in_range_def] >>
  qpat_x_assum `dimindex _ ≤ _` kall_tac >>
  qpat_x_assum `w2i (_ ≫ _) = _` kall_tac >>
  intLib.ARITH_TAC
QED

(* Core SAR soundness: given concrete shift and value bounds *)
Triviality sar_core_sound[local]:
  ∀(w1:256 word) (w2:256 word) lo hi.
    lo ≤ w2i w2 ∧ w2i w2 ≤ hi ∧ hi ≤ INT256_MAX ⇒
    in_range
      (if w2i w1 < 0 ∨ w2i w1 ≥ 256 then
         if lo ≥ 0 then vr_constant 0
         else if hi < 0 then vr_constant (-1)
         else VR_Range (-1) 0
       else VR_Range (lo / &(2 ** Num (w2i w1))) (hi / &(2 ** Num (w2i w1))))
      (w2 ≫ w2n w1)
Proof
  rpt gen_tac >> strip_tac >>
  IF_CASES_TAC
  >- (irule sar_huge_sound >> simp[] >> intLib.ARITH_TAC)
  >> simp[in_range_def] >>
  `0 ≤ w2i w1 ∧ w2i w1 < 256` by intLib.ARITH_TAC >>
  imp_res_tac w2i_nonneg_eq_w2n >>
  gvs[integerTheory.NUM_OF_INT] >>
  match_mp_tac sar_main >> simp[]
QED

Theorem eval_range_sar_sound:
  ∀r1 r2 w1 w2 lit1.
    in_range r1 w1 ∧ in_range r2 w2 ∧
    (∀v. lit1 = SOME v ⇒ w2i w1 = v) ⇒
    in_range (eval_range_sar r1 r2 lit1) (word_asr w2 (w2n w1))
Proof
  Cases >> Cases >>
  simp[eval_range_sar_def, in_range_top, in_range_def, LET_THM,
       vr_lo_def, vr_hi_def] >>
  rpt strip_tac >>
  Cases_on `lit1` >> simp[in_range_top] >>
  rpt strip_tac >> gvs[] >>
  IF_CASES_TAC >> simp[in_range_top] >>
  irule sar_core_sound >>
  gvs[uint256_gt_int256, int_gt] >> intLib.ARITH_TAC
QED

(* eval_range_signextend_sound is proved in rangeAnalysisProofs
   because sign_extend_def is in venomExecSemantics (not an ancestor here) *)

