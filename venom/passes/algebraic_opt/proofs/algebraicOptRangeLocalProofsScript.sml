Theory algebraicOptRangeLocalProofs
Ancestors
  algebraicOptDefs venomExecSemantics exprSimArith

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
  intLib.COOPER_TAC
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
  `2 ** m = 2 * 2 ** (m - 1)` by
    (`m = SUC (m - 1)` by simp[] >> pop_assum SUBST1_TAC >> simp[arithmeticTheory.EXP]) >>
  `&(2 ** m) = 2 * &(2 ** (m - 1)) : int` by
    asm_rewrite_tac[GSYM integerTheory.INT_MUL] >>
  qpat_x_assum `2 ** m = _` kall_tac >>
  `0 < &(2 ** (m - 1)) : int` by simp[] >>
  qabbrev_tac `H = &(2 ** (m - 1)) : int` >>
  `signed_int_mod m (w2i x) = w2i x` by
    (simp[vyperValueOperationTheory.signed_int_mod_def] >>
     Cases_on `0 <= w2i x`
     >- (`w2i x % (2 * H) = w2i x` by
           (irule integerTheory.INT_LESS_MOD >> intLib.ARITH_TAC) >>
         rw[] >> intLib.ARITH_TAC) >>
     `w2i x % (2 * H) = w2i x + 2 * H` by
       (irule integerTheory.INT_MOD_UNIQUE >> qexists `-1` >>
        rw[] >> intLib.ARITH_TAC) >>
     rw[] >> intLib.ARITH_TAC) >>
  qspecl_then [`n`, `w2i x`] mp_tac i2w_signed_int_mod_sign_extend >>
  simp[Abbr `m`, integer_wordTheory.i2w_w2i]
QED

Theorem ao_sign_extend_large:
  !n x. 31w <=+ n ==> sign_extend n x = x
Proof
  simp[wordsTheory.WORD_LS, wordsTheory.dimword_def, sign_extend_def] >> rpt strip_tac >>
  `30 < w2n n` by decide_tac >> simp[]
QED
