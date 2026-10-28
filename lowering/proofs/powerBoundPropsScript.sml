(* Exact arithmetic contracts for the bounds used by compile_safe_pow.
   These are mathematical bounds, not a claim about the emitted execution.
   TOP-LEVEL: largest_pow_base_exact, largest_pow_exponent_exact. *)
Theory powerBoundProps
Ancestors
  exprLowering arithmetic integer vyperValue
Libs
  Omega

Theorem power_midpoint_bounds:
  !lo hi bound.
    hi <= lo + 2 * bound /\ lo + 1 < hi ==>
    lo < (lo + hi) DIV 2 /\ (lo + hi) DIV 2 < hi /\
    hi - (lo + hi) DIV 2 <= bound /\ (lo + hi) DIV 2 - lo <= bound
Proof
  Omega.OMEGA_TAC
QED

(* Binary search preserves a bracket, halving its width at every step. *)
Theorem largest_pow_base_search_exact:
  !fuel exponent limit lo hi.
    lo ** exponent < limit /\ limit <= hi ** exponent /\
    hi - lo <= 2 ** fuel ==>
    let r = largest_pow_base_search fuel exponent limit lo hi in
      r ** exponent < limit /\ limit <= (r + 1) ** exponent
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (simp[largest_pow_base_search_def] >>
      `hi <= lo + 1` by fs[] >>
      `hi ** exponent <= (lo + 1) ** exponent` by simp[] >>
      metis_tac[LESS_EQ_TRANS]) >>
  simp[Once largest_pow_base_search_def] >>
  IF_CASES_TAC
  >- (`hi ** exponent <= (lo + 1) ** exponent` by simp[] >>
      simp[] >> metis_tac[LESS_EQ_TRANS]) >>
  qabbrev_tac `mid = (lo + hi) DIV 2` >>
  `lo < mid /\ mid < hi /\
   hi - mid <= 2 ** fuel /\ mid - lo <= 2 ** fuel` by
    (mp_tac (Q.SPECL [`lo`, `hi`, `2 ** fuel`] power_midpoint_bounds) >>
     fs[Abbr `mid`, EXP]) >>
  fs[Abbr `mid`] >> IF_CASES_TAC >> first_x_assum irule >> simp[]
QED

Theorem largest_pow_base_exact:
  !exponent bits signed.
    0 < exponent ==>
    let limit = 2 ** (bits - if signed then 1 else 0) in
    let r = largest_pow_base exponent bits signed in
      r ** exponent < limit /\ limit <= (r + 1) ** exponent
Proof
  rpt strip_tac >>
  `2 ** (bits - if signed then 1 else 0) <= 2 ** (bits + 1)` by
    (irule LESS_EQ_TRANS >> qexists_tac `2 ** bits` >> simp[]) >>
  mp_tac (Q.SPECL [`bits + 1`, `exponent`,
    `2 ** (bits - if signed then 1 else 0)`, `0`,
    `2 ** (bits - if signed then 1 else 0)`] largest_pow_base_search_exact) >>
  simp[largest_pow_base_def, ZERO_EXP, X_LE_X_EXP]
QED

(* Linear search terminates once the next power reaches the limit.  A
   crossing within the remaining fuel is sufficient; no machine arithmetic
   or approximation is involved. *)
Theorem largest_pow_exponent_search_exact:
  !fuel base limit exponent.
    1 < base /\ base ** exponent < limit /\
    limit <= base ** (exponent + fuel + 1) ==>
    let r = largest_pow_exponent_search fuel base limit exponent in
      base ** r < limit /\ limit <= base ** (r + 1)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- fs[largest_pow_exponent_search_def] >>
  simp[Once largest_pow_exponent_search_def] >> fs[] >>
  IF_CASES_TAC >- (first_x_assum irule >> fs[ADD_CLAUSES, ADD1]) >> simp[]
QED

Theorem largest_pow_exponent_exact:
  !base bits signed.
    1 < base /\ base < 2 ** (bits - if signed then 1 else 0) ==>
    let limit = 2 ** (bits - if signed then 1 else 0) in
    let r = largest_pow_exponent base bits signed in
      base ** r < limit /\ limit <= base ** (r + 1)
Proof
  rpt strip_tac >> rename1 `1 < magnitude` >>
  `2 ** (bits - if signed then 1 else 0) <= magnitude ** (1 + (bits + 1) + 1)` by
    (irule LESS_EQ_TRANS >> qexists_tac `2 ** (1 + (bits + 1) + 1)` >> simp[]) >>
  mp_tac (Q.SPECL [`bits + 1`, `magnitude`,
    `2 ** (bits - if signed then 1 else 0)`, `1`]
    largest_pow_exponent_search_exact) >>
  simp[largest_pow_exponent_def]
QED

Theorem largest_pow_exponent_lt_bits:
  !base bits signed.
    1 < base /\ base < 2 ** (bits - if signed then 1 else 0) ==>
    largest_pow_exponent base bits signed < bits - if signed then 1 else 0
Proof
  rpt strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [LET_THM] largest_pow_exponent_exact) >> strip_tac >>
  rename1 `1 < magnitude` >>
  `2 ** largest_pow_exponent magnitude bits signed <=
   magnitude ** largest_pow_exponent magnitude bits signed` by simp[] >>
  `2 ** largest_pow_exponent magnitude bits signed <
   2 ** (bits - if signed then 1 else 0)` by metis_tac[LESS_EQ_LESS_TRANS] >>
  fs[]
QED

Theorem largest_pow_base_lt_limit:
  !exponent bits signed.
    0 < exponent ==>
    largest_pow_base exponent bits signed <
      2 ** (bits - if signed then 1 else 0)
Proof
  rpt strip_tac >> drule (SIMP_RULE (srw_ss()) [LET_THM] largest_pow_base_exact) >>
  disch_then (qspecl_then [`bits`, `signed`] strip_assume_tac) >>
  irule LESS_EQ_LESS_TRANS >>
  qexists_tac `largest_pow_base exponent bits signed ** exponent` >>
  simp[X_LE_X_EXP]
QED

(* The computed bracket characterises every candidate, not just its ends. *)
Theorem largest_pow_base_characterisation:
  !exponent bits signed n.
    0 < exponent ==>
    (n <= largest_pow_base exponent bits signed <=>
     n ** exponent < 2 ** (bits - if signed then 1 else 0))
Proof
  rpt strip_tac >> drule (SIMP_RULE (srw_ss()) [LET_THM] largest_pow_base_exact) >>
  disch_then (qspecl_then [`bits`, `signed`] strip_assume_tac) >>
  eq_tac >> strip_tac
  >- (irule LESS_EQ_LESS_TRANS >>
      qexists_tac `largest_pow_base exponent bits signed ** exponent` >> simp[]) >>
  CCONTR_TAC >>
  `largest_pow_base exponent bits signed + 1 <= n` by simp[] >>
  `(largest_pow_base exponent bits signed + 1) ** exponent <= n ** exponent`
    by simp[] >>
  metis_tac[LESS_EQ_LESS_TRANS, NOT_LESS_EQUAL]
QED

Theorem largest_pow_exponent_characterisation:
  !base bits signed n.
    1 < base /\ base < 2 ** (bits - if signed then 1 else 0) ==>
    (n <= largest_pow_exponent base bits signed <=>
     base ** n < 2 ** (bits - if signed then 1 else 0))
Proof
  rpt strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [LET_THM] largest_pow_exponent_exact) >> strip_tac >>
  rename1 `1 < magnitude` >>
  eq_tac >> strip_tac
  >- (irule LESS_EQ_LESS_TRANS >>
      qexists_tac `magnitude ** largest_pow_exponent magnitude bits signed` >> simp[]) >>
  CCONTR_TAC >>
  `largest_pow_exponent magnitude bits signed + 1 <= n` by simp[] >>
  `magnitude ** (largest_pow_exponent magnitude bits signed + 1) <= magnitude ** n`
    by simp[] >>
  metis_tac[LESS_EQ_LESS_TRANS, NOT_LESS_EQUAL]
QED

(* Signed powers have one extra representable value: the negative endpoint.
   Extending an exponent bracket is sound exactly for an odd power that
   reaches that endpoint, not for the following (positive) even power. *)
Theorem signed_power_bracket:
  !m limit upper negative n.
    1 < m /\ m ** upper < limit /\ limit <= m ** (upper + 1) ==>
    (n <= (if negative /\ ODD (upper + 1) /\ m ** (upper + 1) = limit
           then upper + 1 else upper) <=>
     m ** n < limit \/ (negative /\ ODD n /\ m ** n = limit))
Proof
  rpt strip_tac >>
  Cases_on `n <= upper`
  >- (`m ** n <= m ** upper` by simp[] >>
      `m ** n < limit` by metis_tac[LESS_EQ_LESS_TRANS] >>
      simp[] >> IF_CASES_TAC >> simp[]) >>
  Cases_on `n = upper + 1` >- (gvs[] >> IF_CASES_TAC >> gvs[] >> decide_tac) >>
  `upper + 1 < n` by decide_tac >>
  `m ** (upper + 1) < m ** n` by simp[] >>
  `limit < m ** n` by metis_tac[LESS_EQ_LESS_TRANS] >>
  simp[] >> IF_CASES_TAC >> simp[] >> decide_tac
QED

Theorem signed_power_in_bound:
  !m bits negative n.
    0 < m /\ 0 < bits ==>
    (within_int_bound (Signed bits) ((if negative then -&m else &m) ** n) <=>
     m ** n < 2 ** (bits - 1) \/
       (negative /\ ODD n /\ m ** n = 2 ** (bits - 1)))
Proof
  rpt strip_tac >> Cases_on `negative` >>
  Cases_on `EVEN n` >>
  simp[INT_EXP_NEG, INT_EXP, ODD_EVEN, within_int_bound_def] >>
  `0 < m ** n` by simp[] >> simp[] >> decide_tac
QED

Theorem largest_signed_pow_exponent_characterisation:
  !m bits negative n.
    1 < m /\ m < 2 ** (bits - 1) ==>
    let upper = largest_pow_exponent m bits T in
    (n <= (if negative /\ ODD (upper + 1) /\ m ** (upper + 1) = 2 ** (bits - 1)
           then upper + 1 else upper) <=>
     m ** n < 2 ** (bits - 1) \/
       (negative /\ ODD n /\ m ** n = 2 ** (bits - 1)))
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`m`, `bits`, `T`] largest_pow_exponent_exact) >>
  simp[] >> strip_tac >> irule signed_power_bracket >> simp[]
QED

Theorem largest_signed_pow_exponent_in_bound:
  !m bits negative n.
    1 < m /\ m < 2 ** (bits - 1) /\ 0 < bits ==>
    let upper = largest_pow_exponent m bits T in
    (within_int_bound (Signed bits) ((if negative then -&m else &m) ** n) <=>
     n <= (if negative /\ ODD (upper + 1) /\ m ** (upper + 1) = 2 ** (bits - 1)
           then upper + 1 else upper))
Proof
  rpt strip_tac >>
  simp[signed_power_in_bound,
       SIMP_RULE (srw_ss()) [LET_THM] largest_signed_pow_exponent_characterisation]
QED

(* The signed literal-exponent lower bound is extended only for an ODD
   exponent. This characterisation includes non-byte widths such as IntT 9. *)
Theorem signed_power_base_bracket:
  !exponent limit upper negative m.
    0 < exponent /\ upper ** exponent < limit /\
    limit <= (upper + 1) ** exponent ==>
    (m <= (if negative /\ ODD exponent /\ (upper + 1) ** exponent = limit
           then upper + 1 else upper) <=>
     m ** exponent < limit \/
       (negative /\ ODD exponent /\ m ** exponent = limit))
Proof
  rpt strip_tac >>
  Cases_on `m <= upper`
  >- (`m ** exponent <= upper ** exponent` by simp[] >>
      `m ** exponent < limit` by metis_tac[LESS_EQ_LESS_TRANS] >>
      simp[] >> IF_CASES_TAC >> simp[]) >>
  Cases_on `m = upper + 1` >- (gvs[] >> IF_CASES_TAC >> gvs[] >> decide_tac) >>
  `upper + 1 < m` by decide_tac >>
  `(upper + 1) ** exponent < m ** exponent` by simp[] >>
  `limit < m ** exponent` by metis_tac[LESS_EQ_LESS_TRANS] >>
  simp[] >> IF_CASES_TAC >> simp[] >> decide_tac
QED

Theorem largest_signed_pow_base_in_bound:
  !exponent bits negative m.
    0 < exponent /\ 0 < bits /\ 0 < m ==>
    let upper = largest_pow_base exponent bits T in
    (within_int_bound (Signed bits) ((if negative then -&m else &m) ** exponent) <=>
     m <= (if negative /\ ODD exponent /\ (upper + 1) ** exponent = 2 ** (bits - 1)
           then upper + 1 else upper))
Proof
  rpt strip_tac >> simp[signed_power_in_bound] >>
  mp_tac (Q.SPECL [`exponent`, `bits`, `T`] largest_pow_base_exact) >>
  simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`exponent`, `2 ** (bits - 1)`,
    `largest_pow_base exponent bits T`, `negative`, `m`] signed_power_base_bracket) >>
  simp[EQ_SYM_EQ]
QED

(* The two uint256 overflow witnesses use opposite literal branches. *)
Theorem power_uint256_overflow_bounds:
  largest_pow_base 256 256 F = 1 /\ largest_pow_exponent 2 256 F = 255
Proof
  `1 <= largest_pow_base 256 256 F` by simp[largest_pow_base_characterisation] >>
  `~(2 <= largest_pow_base 256 256 F)` by simp[largest_pow_base_characterisation] >>
  `255 <= largest_pow_exponent 2 256 F` by
    simp[largest_pow_exponent_characterisation] >>
  `~(256 <= largest_pow_exponent 2 256 F)` by
    simp[largest_pow_exponent_characterisation] >>
  decide_tac
QED
