Theory algebraicOptRangeProofs
Ancestors
  algebraicOptDefs venomExecSemantics

Theorem ao_range_comparison_bounds:
  !r w signed. ao_range_valid_for_cmp r signed /\ in_range r w ==>
    vr_lo r <= ao_wrap_lit w signed /\ ao_wrap_lit w signed <= vr_hi r
Proof
  Cases_on `r` >> Cases_on `signed` >>
  simp[ao_range_valid_for_cmp_def, valueRangeDefsTheory.in_range_def,
       valueRangeDefsTheory.vr_is_top_def, valueRangeDefsTheory.vr_lo_def,
       valueRangeDefsTheory.vr_hi_def, ao_wrap_lit_def] >>
  rpt strip_tac >>
  `0 <= w2i w` by intLib.COOPER_TAC >>
  `~word_msb w` by
    (metis_tac[integer_wordTheory.w2i_lt_0, wordsTheory.word_msb_neg,
               integerTheory.INT_NOT_LT]) >>
  gvs[integer_wordTheory.w2i_def]
QED
