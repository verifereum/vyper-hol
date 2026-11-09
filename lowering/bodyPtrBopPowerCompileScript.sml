Theory bodyPtrBopPowerCompile
Ancestors
  bodyPtrBopArithmeticCompile bodyPtrBopScalarCompile exprLowering
  exprLoweringProps compileEnv freshWrites pred_set list

Theorem bop_scalar_compile_assert_emit:
  comp_ignore_bind (emit_void ASSERT [ok]) (emit_op opc ops) st = (v, st') /\
  ok IN A /\ EVERY (\op. op IN A) ops /\
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  pure_rewrite_tac [comp_ignore_bind_def] >> strip_tac >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. T`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> Cases_on `u` >>
          drule bop_scalar_compile_emit_assert >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      `EVERY (\op. op IN B) ops` by (fs[EVERY_MEM] >> metis_tac[SUBSET_DEF]) >>
      drule bop_scalar_compile_emit_op >> simp[] >> disch_then irule >> fs[]) >> simp[]
QED

Theorem bop_scalar_compile_compare_checked_emit:
  comp_bind
    (comp_bind (emit_op cmp cops) (\u. emit_op ISZERO [u]))
    (\ok. comp_ignore_bind (emit_void ASSERT [ok]) (emit_op opc ops))
    st = (v, st') /\
  MEM cmp [LT; GT; SLT; SGT; EQ] /\ EVERY (\op. op IN A) cops /\
  EVERY (\op. op IN A) ops /\
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_iszero >> simp[] >>
          disch_then irule >> fs[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      `EVERY (\op. op IN B) ops` by (fs[EVERY_MEM] >> metis_tac[SUBSET_DEF]) >>
      drule bop_scalar_compile_assert_emit >> simp[] >> disch_then irule >> fs[]) >> simp[]
QED

Theorem bop_scalar_compile_signed_bounds_emit:
  comp_bind
    (comp_bind (emit_op SLT [x; lo]) (\below.
      comp_bind (emit_op ISZERO [below]) (\ge_lower.
        comp_bind (emit_op SGT [x; hi]) (\above.
          comp_bind (emit_op ISZERO [above]) (\le_upper.
            emit_op AND [ge_lower; le_upper])))))
    (\ok. comp_ignore_bind (emit_void ASSERT [ok]) (emit_op opc ops))
    st = (v, st') /\
  x IN A /\ lo IN A /\ hi IN A /\ EVERY (\op. op IN A) ops /\
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_signed_bounds >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      `EVERY (\op. op IN B) ops` by (fs[EVERY_MEM] >> metis_tac[SUBSET_DEF]) >>
      drule bop_scalar_compile_assert_emit >> simp[] >> disch_then irule >> fs[]) >> simp[]
QED

Theorem bop_scalar_compile_safe_pow:
  compile_safe_pow x y ty base_literal exp_literal st = (v, st') /\
  x IN A /\ y IN A /\ (!w. Lit w IN A) /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> Cases_on `base_literal`
  >- (Cases_on `exp_literal`
      >- (gvs[compile_safe_pow_def] >>
          drule (SRULE [clamp_and_return_def] bop_scalar_compile_emit_clamp) >> simp[]) >>
      rename1 `SOME exponent_int` >>
      Cases_on `Num exponent_int = 0 \/ Num exponent_int = 1`
      >- (gvs[compile_safe_pow_def] >> drule bop_scalar_compile_assert_emit >> simp[]) >>
      Cases_on `is_signed_type ty`
      >- (gvs[compile_safe_pow_def] >>
          drule (SRULE [comp_bind_assoc] bop_scalar_compile_signed_bounds_emit) >> simp[]) >>
      gvs[compile_safe_pow_def] >>
      drule (SRULE [comp_bind_assoc] bop_scalar_compile_compare_checked_emit) >> simp[]) >>
  rename1 `SOME base_int` >>
  Cases_on `base_int = -1 \/ base_int = 0 \/ base_int = 1`
  >- (Cases_on `is_signed_type ty`
      >- (gvs[compile_safe_pow_def, comp_bind_assoc] >>
          drule (SRULE [comp_bind_assoc] bop_scalar_compile_compare_checked_emit) >> simp[]) >>
      gvs[compile_safe_pow_def, comp_return_def, comp_bind_def] >>
      drule bop_scalar_compile_assert_emit >> simp[]) >>
  gvs[compile_safe_pow_def] >>
  drule (SRULE [comp_bind_assoc] bop_scalar_compile_compare_checked_emit) >> simp[]
QED
