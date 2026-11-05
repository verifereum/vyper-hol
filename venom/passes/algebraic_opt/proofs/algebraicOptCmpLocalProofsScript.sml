Theory algebraicOptCmpLocalProofs
Ancestors
  algebraicOptDefs integer_word valueRangeDefs venomExecSemantics

Theorem ao_unsigned_gt_complement:
  !x w : bytes32. w <> 0w - 1w ==>
    (x <+ w + 1w <=> ~(w <+ x))
Proof
  rpt strip_tac >>
  qpat_x_assum `w <> _` mp_tac >>
  once_rewrite_tac[GSYM wordsTheory.w2n_11] >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV wordsLib.WORD_EVAL_CONV))) >>
  strip_tac >>
  qspec_then `w : bytes32` mp_tac wordsTheory.w2n_lt >>
  simp[wordsTheory.WORD_LO, wordsTheory.word_add_def,
       wordsTheory.w2n_n2w] >>
  strip_tac >> gvs[] >>
  `w2n w + 1 < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  simp[arithmeticTheory.LESS_MOD, wordsTheory.dimword_def]
QED

Theorem ao_unsigned_lt_complement:
  !x w : bytes32. w <> 0w ==>
    (w - 1w <+ x <=> ~(x <+ w))
Proof
  rpt strip_tac >>
  `w - 1w <> 0w - 1w` by simp[] >>
  drule ao_unsigned_gt_complement >>
  disch_then (qspec_then `x` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem ao_signed_gt_complement:
  !x w : bytes32. w <> i2w INT256_MAX ==>
    (x < w + 1w <=> ~(w < x))
Proof
  rpt strip_tac >>
  `w2i w <> INT256_MAX` by metis_tac[integer_wordTheory.i2w_w2i] >>
  qspec_then `w : bytes32` assume_tac integer_wordTheory.w2i_le >>
  qspec_then `w : bytes32` assume_tac integer_wordTheory.w2i_ge >>
  `w2i (w + 1w) = w2i w + 1` by
    (`w + 1w = i2w (w2i w + 1)` by
       simp[GSYM integer_wordTheory.word_add_i2w, integer_wordTheory.w2i_1] >>
     pop_assum SUBST1_TAC >> irule integer_wordTheory.w2i_i2w >>
     fs[GSYM INT256_MIN_def, GSYM INT256_MAX_def] >> intLib.ARITH_TAC) >>
  simp[integer_wordTheory.WORD_LTi] >> intLib.ARITH_TAC
QED

Theorem ao_signed_lt_complement:
  !x w : bytes32. w <> i2w INT256_MIN ==>
    (w - 1w < x <=> ~(x < w))
Proof
  rpt strip_tac >>
  `w2i w <> INT256_MIN` by metis_tac[integer_wordTheory.i2w_w2i] >>
  qspec_then `w : bytes32` assume_tac integer_wordTheory.w2i_le >>
  qspec_then `w : bytes32` assume_tac integer_wordTheory.w2i_ge >>
  `w2i (w - 1w) = w2i w - 1` by
    (`w - 1w = i2w (w2i w - 1)` by
       simp[GSYM integer_wordTheory.word_sub_i2w, integer_wordTheory.w2i_1] >>
     pop_assum SUBST1_TAC >> irule integer_wordTheory.w2i_i2w >>
     fs[GSYM INT256_MIN_def, GSYM INT256_MAX_def] >> intLib.ARITH_TAC) >>
  simp[integer_wordTheory.WORD_LTi] >> intLib.ARITH_TAC
QED

Theorem ao_cmp_threshold_complement:
  !signed is_gt lo never hi (x : bytes32) w.
    (if signed then ao_signed_boundaries is_gt
     else ao_unsigned_boundaries is_gt) = (lo,never,hi) /\ w <> never ==>
    bool_to_word
      (if signed then (if is_gt then x < w + 1w else w - 1w < x)
       else (if is_gt then x <+ w + 1w else w - 1w <+ x)) =
    bool_to_word
      (bool_to_word
        (if signed then (if is_gt then w < x else x < w)
         else (if is_gt then w <+ x else x <+ w)) = 0w)
Proof
  Cases >> Cases >>
  simp[ao_signed_boundaries_def, ao_unsigned_boundaries_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[ao_signed_gt_complement, SRULE [] ao_signed_lt_complement,
       ao_unsigned_gt_complement, SRULE [] ao_unsigned_lt_complement]
  >~ [`bool_to_word (~(w < x))`] >-
     (Cases_on `w < x` >> simp[bool_to_word_def])
  >~ [`bool_to_word (~(x < w))`] >-
     (Cases_on `x < w` >> simp[bool_to_word_def])
  >~ [`bool_to_word (~(w <+ x))`] >-
     (Cases_on `w <+ x` >> simp[bool_to_word_def])
  >> Cases_on `x <+ w` >> simp[bool_to_word_def]
QED
