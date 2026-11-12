Theory bodyPtrBopArithmeticCompile
Ancestors
  bodyPtrBopScalarCompile exprLowering exprLoweringProps compileEnv freshWrites pred_set list

Theorem bop_scalar_compile_safe_mod:
  compile_safe_mod x y ty st = (v, st') /\ x IN A /\ y IN A /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  simp[compile_safe_mod_def, comp_ignore_bind_def] >> strip_tac >>
  drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      drule bop_scalar_compile_bind_run >>
      disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `B`] mp_tac) >>
      impl_tac
      >- (conj_tac
          >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
          rpt strip_tac >> rule_assum_tac BETA_RULE >>
          drule bop_scalar_compile_bind_run >>
          disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. T`, `B'`] mp_tac) >>
          impl_tac
          >- (conj_tac
              >- (rpt strip_tac >> Cases_on `u''` >>
                  drule bop_scalar_compile_emit_assert >> simp[]) >>
              rpt strip_tac >> rule_assum_tac BETA_RULE >>
              `!z. z IN R ==> not_fresh_at m'' z` by metis_tac[not_fresh_at_mono] >>
              `x IN B'' /\ y IN B''` by metis_tac[SUBSET_DEF] >>
              Cases_on `is_signed_type ty` >> gvs[] >>
              drule bop_scalar_compile_emit_op >> simp[]) >> simp[]) >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_assert_return:
  comp_ignore_bind (emit_void ASSERT [ok]) (comp_return res) st = (v, st') /\
  ok IN A /\ res IN A ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. T`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> Cases_on `u` >>
          drule bop_scalar_compile_emit_assert >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `res IN B` by metis_tac[SUBSET_DEF] >>
      drule bop_scalar_compile_return >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_emit_checked_return:
  comp_bind (emit_op opc ops)
    (\ok. comp_ignore_bind (emit_void ASSERT [ok]) (comp_return res)) st = (v, st') /\
  MEM opc [LT; GT; SLT; SGT; EQ; ISZERO; AND; OR] /\
  EVERY (\op. op IN A) ops /\ res IN A /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[] >>
          disch_then irule >> fs[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `res IN B` by metis_tac[SUBSET_DEF] >>
      drule bop_scalar_compile_assert_return >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_signed_add_sub_check:
  comp_bind (emit_op SLT [y; Lit 0w]) (\neg.
    comp_bind (emit_op opc [res; x]) (\cmp.
      comp_bind (emit_op EQ [neg; cmp]) (\ok.
        comp_ignore_bind (emit_void ASSERT [ok]) (comp_return res)))) st = (v, st') /\
  MEM opc [SLT; SGT] /\ x IN A /\ y IN A /\ res IN A /\ Lit 0w IN A /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      `res IN B /\ x IN B` by metis_tac[SUBSET_DEF] >>
      drule bop_scalar_compile_bind_run >>
      disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `B`] mp_tac) >>
      impl_tac
      >- (conj_tac
          >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[] >>
              disch_then irule >> fs[]) >>
          rpt strip_tac >> rule_assum_tac BETA_RULE >>
          `!z. z IN R ==> not_fresh_at m' z` by metis_tac[not_fresh_at_mono] >>
          `res IN B' /\ u IN B'` by metis_tac[SUBSET_DEF] >>
          drule bop_scalar_compile_emit_checked_return >> simp[]) >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_unsigned_add_sub_check:
  comp_bind (emit_op opc [res; x]) (\cmp.
    comp_bind (emit_op ISZERO [cmp]) (\ok.
      comp_ignore_bind (emit_void ASSERT [ok]) (comp_return res))) st = (v, st') /\
  MEM opc [LT; GT] /\ res IN A /\ x IN A /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[] >>
          disch_then irule >> fs[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      `res IN B` by metis_tac[SUBSET_DEF] >>
      drule bop_scalar_compile_emit_checked_return >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_safe_add:
  compile_safe_add x y ty st = (v, st') /\ x IN A /\ y IN A /\
  (!w. Lit w IN A) /\ (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  simp[compile_safe_add_def] >> strip_tac >>
  drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      `x IN B /\ y IN B /\ (!w. Lit w IN B)` by metis_tac[SUBSET_DEF] >>
      Cases_on `type_bits ty < 256`
      >- (gvs[] >> drule bop_scalar_compile_clamp_and_return >> simp[]) >>
      Cases_on `is_signed_type ty` >> gvs[] >>
      FIRST [
        (drule bop_scalar_compile_signed_add_sub_check >> simp[]),
        (drule bop_scalar_compile_unsigned_add_sub_check >> simp[])]) >> simp[]
QED

Theorem bop_scalar_compile_safe_sub:
  compile_safe_sub x y ty st = (v, st') /\ x IN A /\ y IN A /\
  (!w. Lit w IN A) /\ (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  simp[compile_safe_sub_def] >> strip_tac >>
  drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      `x IN B /\ y IN B /\ (!w. Lit w IN B)` by metis_tac[SUBSET_DEF] >>
      Cases_on `type_bits ty < 256`
      >- (gvs[] >> drule bop_scalar_compile_clamp_and_return >> simp[]) >>
      Cases_on `is_signed_type ty` >> gvs[] >>
      FIRST [
        (drule bop_scalar_compile_signed_add_sub_check >> simp[]),
        (drule bop_scalar_compile_unsigned_add_sub_check >> simp[])]) >> simp[]
QED

Theorem bop_scalar_compile_emit_clamp:
  comp_bind (emit_op opc ops) (\res. clamp_and_return res ty) st = (v, st') /\
  MEM opc [ADD; SUB; MUL; Div; SDIV; Exp] /\ EVERY (\op. op IN A) ops /\
  (!w. Lit w IN A) /\ (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[] >>
          disch_then irule >> fs[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      `!w. Lit w IN B` by metis_tac[SUBSET_DEF] >>
      drule bop_scalar_compile_clamp_and_return >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_safe_decimal_div:
  compile_safe_decimal_div x y divisor ty st = (v, st') /\ x IN A /\ y IN A /\
  (!w. Lit w IN A) /\ (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  simp[compile_safe_decimal_div_def, comp_ignore_bind_def] >> strip_tac >>
  drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      `y IN B` by metis_tac[SUBSET_DEF] >>
      drule bop_scalar_compile_bind_run >>
      disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `B`] mp_tac) >>
      impl_tac
      >- (conj_tac
          >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
          rpt strip_tac >> rule_assum_tac BETA_RULE >>
          `!z. z IN R ==> not_fresh_at m' z` by metis_tac[not_fresh_at_mono] >>
          drule bop_scalar_compile_bind_run >>
          disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `B'`] mp_tac) >>
          impl_tac
          >- (conj_tac
              >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
              rpt strip_tac >> rule_assum_tac BETA_RULE >>
              drule bop_scalar_compile_bind_run >>
              disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. T`, `B''`] mp_tac) >>
              impl_tac
              >- (conj_tac
                  >- (rpt strip_tac >> Cases_on `u'''` >>
                      drule bop_scalar_compile_emit_assert >> simp[]) >>
                  rpt strip_tac >> rule_assum_tac BETA_RULE >>
                  `!z. z IN R ==> not_fresh_at m''' z` by metis_tac[not_fresh_at_mono] >>
                  `u IN B''' /\ y IN B''' /\ (!w. Lit w IN B''')`
                    by metis_tac[SUBSET_DEF] >>
                  drule bop_scalar_compile_emit_clamp >> simp[]) >> simp[]) >> simp[]) >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_exclusion_checked_return:
  comp_bind
    (comp_bind (emit_op EQ [x; k]) (\xmin.
      comp_bind (emit_op NOT [y]) (\ny.
        comp_bind (emit_op ISZERO [ny]) (\yneg.
          comp_bind (emit_op AND [xmin; yneg]) (\bad. emit_op ISZERO [bad])))))
    (\ok. comp_ignore_bind (emit_void ASSERT [ok]) (comp_return res)) st = (v, st') /\
  x IN A /\ y IN A /\ k IN A /\ res IN A /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_exclusion >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `res IN B` by metis_tac[SUBSET_DEF] >>
      drule bop_scalar_compile_assert_return >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_signed_div_check:
  comp_bind (emit_op EQ [x; Lit (n2w (2 ** 255))]) (\xmin.
    comp_bind (emit_op NOT [y]) (\ny.
      comp_bind (emit_op ISZERO [ny]) (\yneg.
        comp_bind (emit_op AND [xmin; yneg]) (\bad.
          comp_bind (emit_op ISZERO [bad]) (\ok.
            comp_ignore_bind (emit_void ASSERT [ok]) (comp_return res)))))) st = (v, st') /\
  x IN A /\ y IN A /\ res IN A /\ (!w. Lit w IN A) /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >>
  drule (SRULE [comp_bind_assoc] bop_scalar_compile_exclusion_checked_return) >> simp[]
QED

Theorem bop_scalar_compile_signed_div_result:
  comp_bind (emit_op SDIV [x; y]) (\res.
    if type_bits ty = 256 then
      comp_bind (emit_op EQ [x; Lit (n2w (2 ** 255))]) (\xmin.
        comp_bind (emit_op NOT [y]) (\ny.
          comp_bind (emit_op ISZERO [ny]) (\yneg.
            comp_bind (emit_op AND [xmin; yneg]) (\bad.
              comp_bind (emit_op ISZERO [bad]) (\ok.
                comp_ignore_bind (emit_void ASSERT [ok]) (comp_return res))))))
    else if type_bits ty < 256 then clamp_and_return res ty
    else comp_return res) st = (v, st') /\
  x IN A /\ y IN A /\ (!w. Lit w IN A) /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      `x IN B /\ y IN B /\ (!w. Lit w IN B)` by metis_tac[SUBSET_DEF] >>
      Cases_on `type_bits ty = 256`
      >- (gvs[] >> drule (SRULE [] bop_scalar_compile_signed_div_check) >> simp[]) >>
      Cases_on `type_bits ty < 256`
      >- (gvs[] >> drule bop_scalar_compile_clamp_and_return >> simp[]) >>
      gvs[] >> drule bop_scalar_compile_return >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_safe_div:
  compile_safe_div x y ty st = (v, st') /\ x IN A /\ y IN A /\
  (!w. Lit w IN A) /\ (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  simp[compile_safe_div_def, comp_ignore_bind_def] >> strip_tac >>
  drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      drule bop_scalar_compile_bind_run >>
      disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `B`] mp_tac) >>
      impl_tac
      >- (conj_tac
          >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
          rpt strip_tac >> rule_assum_tac BETA_RULE >>
          drule bop_scalar_compile_bind_run >>
          disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. T`, `B'`] mp_tac) >>
          impl_tac
          >- (conj_tac
              >- (rpt strip_tac >> Cases_on `u''` >>
                  drule bop_scalar_compile_emit_assert >> simp[]) >>
              rpt strip_tac >> rule_assum_tac BETA_RULE >>
              `!z. z IN R ==> not_fresh_at m'' z` by metis_tac[not_fresh_at_mono] >>
              `x IN B'' /\ y IN B'' /\ (!w. Lit w IN B'')` by metis_tac[SUBSET_DEF] >>
              Cases_on `is_signed_type ty`
              >- (gvs[] >> drule (SRULE [comp_ignore_bind_def] bop_scalar_compile_signed_div_result) >> simp[]) >>
              gvs[] >> drule bop_scalar_compile_emit_op >> simp[]) >> simp[]) >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_exclusion_and_checked:
  comp_bind
    (comp_bind (emit_op EQ [x; k]) (\xmin.
      comp_bind (emit_op NOT [y]) (\ny.
        comp_bind (emit_op ISZERO [ny]) (\yneg.
          comp_bind (emit_op AND [xmin; yneg]) (\bad.
            emit_op ISZERO [bad])))))
    (\ns. comp_bind (emit_op AND [ok; ns]) (\c. emit_void ASSERT [c]))
    st = ((), st') /\
  x IN A /\ y IN A /\ k IN A /\ ok IN A /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var
Proof
  strip_tac >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. T`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_exclusion >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >> Cases_on `v` >>
      `ok IN B` by metis_tac[SUBSET_DEF] >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      drule bop_scalar_compile_emit_checked >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_mul_guard:
  comp_bind (emit_op OR [d; z]) (\ok.
    comp_bind (if signed /\ bits = 256 then
      comp_bind (emit_op EQ [x; Lit (n2w (2 ** 255))]) (\xmin.
        comp_bind (emit_op NOT [y]) (\ny.
          comp_bind (emit_op ISZERO [ny]) (\yneg.
            comp_bind (emit_op AND [xmin; yneg]) (\bad.
              comp_bind (emit_op ISZERO [bad]) (\ns.
                emit_op AND [ok; ns])))))
    else comp_return ok) (\c. emit_void ASSERT [c])) st = ((), st') /\
  d IN A /\ z IN A /\ x IN A /\ y IN A /\ (!w. Lit w IN A) /\
  (!n. n IN R ==> not_fresh_at st n) ==>
  ?B. bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var
Proof
  strip_tac >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. T`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >> Cases_on `v` >>
      `x IN B /\ y IN B /\ (!w. Lit w IN B)` by metis_tac[SUBSET_DEF] >>
      `!n. n IN R ==> not_fresh_at m n` by metis_tac[not_fresh_at_mono] >>
      Cases_on `signed /\ bits = 256`
      >- (gvs[comp_bind_assoc] >>
          drule (SRULE [comp_bind_assoc] bop_scalar_compile_exclusion_and_checked) >> simp[]) >>
      gvs[comp_return_def, comp_bind_def] >>
      drule bop_scalar_compile_emit_assert >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_mul_overflow_check:
  compile_mul_overflow_check x y res signed bits st = ((), st') /\
  x IN A /\ y IN A /\ res IN A /\ (!w. Lit w IN A) /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var
Proof
  simp[compile_mul_overflow_check_def] >> strip_tac >>
  drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. T`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> Cases_on `signed` >> gvs[] >>
          drule bop_scalar_compile_emit_op >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      `x IN B /\ y IN B /\ (!w. Lit w IN B)` by metis_tac[SUBSET_DEF] >>
      drule bop_scalar_compile_bind_run >>
      disch_then (qspecl_then [`R`, `\v B. T`, `\u B. u IN B`, `B`] mp_tac) >>
      impl_tac
      >- (conj_tac
          >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
          rpt strip_tac >> rule_assum_tac BETA_RULE >>
          `!z. z IN R ==> not_fresh_at m' z` by metis_tac[not_fresh_at_mono] >>
          `x IN B' /\ y IN B' /\ (!w. Lit w IN B')` by metis_tac[SUBSET_DEF] >>
          drule bop_scalar_compile_bind_run >>
          disch_then (qspecl_then [`R`, `\v B. T`, `\u B. u IN B`, `B'`] mp_tac) >>
          impl_tac
          >- (conj_tac
              >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
              rpt strip_tac >> rule_assum_tac BETA_RULE >> Cases_on `v''` >>
              `!z. z IN R ==> not_fresh_at m'' z` by metis_tac[not_fresh_at_mono] >>
              `x IN B'' /\ y IN B'' /\ u' IN B'' /\ (!w. Lit w IN B'')`
                by metis_tac[SUBSET_DEF] >>
              drule (SRULE [] bop_scalar_compile_mul_guard) >> simp[]) >> simp[]) >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_mul_scaled_result:
  comp_bind (if is_decimal_type ty then
    emit_op (if is_signed_type ty then SDIV else Div)
      [res; Lit (n2w (decimal_divisor ty))] else comp_return res)
    (\r. if type_bits ty < 256 \/ is_decimal_type ty then clamp_and_return r ty
         else comp_return r) st = (v, st') /\
  res IN A /\ (!w. Lit w IN A) /\ (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> Cases_on `is_decimal_type ty`
          >- (gvs[] >> Cases_on `is_signed_type ty` >> gvs[] >>
              drule bop_scalar_compile_emit_op >> simp[]) >>
          gvs[] >> drule bop_scalar_compile_return >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      `!w. Lit w IN B` by metis_tac[SUBSET_DEF] >>
      Cases_on `type_bits ty < 256 \/ is_decimal_type ty`
      >- (gvs[] >> drule bop_scalar_compile_clamp_and_return >> simp[]) >>
      gvs[] >> drule bop_scalar_compile_return >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_safe_mul:
  compile_safe_mul x y ty st = (v, st') /\ x IN A /\ y IN A /\
  (!w. Lit w IN A) /\ (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  simp[compile_safe_mul_def, comp_ignore_bind_def] >> strip_tac >>
  drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      `x IN B /\ y IN B /\ (!w. Lit w IN B)` by metis_tac[SUBSET_DEF] >>
      drule bop_scalar_compile_bind_run >>
      disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. T`, `B`] mp_tac) >>
      impl_tac
      >- (conj_tac
          >- (rpt strip_tac >> Cases_on `u'` >> Cases_on `128 < type_bits ty`
              >- (gvs[] >> drule bop_scalar_compile_mul_overflow_check >> simp[]) >>
              gvs[comp_return_def] >> qexists_tac `B` >>
              simp[emitted_insts_def, same_blocks_def]) >>
          rpt strip_tac >> rule_assum_tac BETA_RULE >>
          `!z. z IN R ==> not_fresh_at m' z` by metis_tac[not_fresh_at_mono] >>
          `u IN B' /\ (!w. Lit w IN B')` by metis_tac[SUBSET_DEF] >>
          drule bop_scalar_compile_mul_scaled_result >> simp[]) >> simp[]) >> simp[]
QED
