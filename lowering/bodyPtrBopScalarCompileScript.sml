Theory bodyPtrBopScalarCompile
Ancestors
  bodyPtrBopScalarSeq emitHelperProps compileEnv exprLoweringProps exprLowering
  freshWrites builtinSimple list pred_set

Theorem bop_scalar_seq_append:
  !xs R A B ys C.
    bop_scalar_seq R A xs B /\ bop_scalar_seq R B ys C ==>
    bop_scalar_seq R A (xs ++ ys) C
Proof
  Induct >> simp[bop_scalar_seq_def] >> rpt strip_tac >>
  metis_tac[]
QED

Theorem bop_scalar_seq_emit_op:
  emit_op opc ops st = (v, st') /\
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  EVERY (\op. op IN A) ops /\ (!x. x IN R ==> not_fresh_at st x) ==>
  bop_scalar_seq R A (emitted_insts st st') (v INSERT A)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  irule bop_scalar_seq_single >> simp[] >>
  fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem bop_scalar_seq_emit_assert:
  emit_void opc [op] st = ((), st') /\
  (opc = ASSERT \/ opc = ASSERT_UNREACHABLE) /\ op IN A ==>
  bop_scalar_seq R A (emitted_insts st st') A
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  gvs[] >> irule bop_scalar_seq_assert >> simp[]
QED

Theorem bop_scalar_seq_wrap_truncate:
  wrap_truncate res ty st = (v, st') /\ res IN A /\
  (!w. Lit w IN A) /\ (!x. x IN R ==> not_fresh_at st x) ==>
  bop_scalar_seq R A (emitted_insts st st') (v INSERT A)
Proof
  Cases_on `type_bits ty < 256`
  >- (Cases_on `is_signed_type ty` >>
      simp[wrap_truncate_def] >> strip_tac >>
      drule bop_scalar_seq_emit_op >> simp[]) >>
  simp[wrap_truncate_def, comp_return_def, emitted_insts_def] >>
  strip_tac >> gvs[] >> simp[EXTENSION] >> metis_tac[]
QED

Theorem bop_scalar_seq_emit_iszero:
  emit_op opc ops st = (u, mid) /\
  emit_op ISZERO [u] mid = (v, st') /\
  MEM opc [LT; GT; SLT; SGT; EQ] /\ EVERY (\op. op IN A) ops /\
  (!x. x IN R ==> not_fresh_at st x) ==>
  bop_scalar_seq R A (emitted_insts st st') (v INSERT u INSERT A)
Proof
  strip_tac >>
  imp_res_tac emit_op_extends >>
  drule_all emitted_insts_append >> disch_then SUBST1_TAC >>
  irule bop_scalar_seq_append >> qexists_tac `u INSERT A` >> conj_tac
  >- (rev_drule bop_scalar_seq_emit_op >>
      simp[] >> disch_then irule >> fs[]) >>
  drule bop_scalar_seq_emit_op >>
  simp[] >> disch_then irule >>
  rev_drule emitted_insts_emit_op >>
  strip_tac >> fs[not_fresh_at_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem bop_scalar_seq_compare:
  MEM cmp [Lt; Gt; Eq; NotEq; LtE; GtE] /\
  compile_compare cmp x y ty st = (v, st') /\ x IN A /\ y IN A /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. bop_scalar_seq R A (emitted_insts st st') B /\ v IN B /\ A SUBSET B
Proof
  strip_tac >> gvs[compile_compare_def] >>
  Cases_on `is_uint256 ty` >> gvs[comp_bind_def] >>
  TRY (pairarg_tac >> gvs[]) >>
  FIRST [
    (drule bop_scalar_seq_emit_iszero >> disch_then drule >>
     simp[] >> disch_then (qspecl_then [`R`, `A`] mp_tac) >>
     simp[] >> strip_tac >> goal_assum (drule_at Any) >> simp[SUBSET_DEF]),
    (drule bop_scalar_seq_emit_op >> simp[] >>
     disch_then (qspecl_then [`R`, `A`] mp_tac) >> simp[] >>
     strip_tac >> goal_assum (drule_at Any) >> simp[SUBSET_DEF])]
QED

Theorem bop_scalar_seq_available:
  !code R A B. bop_scalar_seq R A code B ==> A SUBSET B
Proof
  Induct >> simp[Once bop_scalar_seq_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[SUBSET_DEF]
QED

Theorem bop_scalar_compile_chain:
  bop_scalar_seq R A (emitted_insts s m) B /\ A SUBSET B /\
  m.cs_current_insts = s.cs_current_insts ++ emitted_insts s m /\
  same_blocks s m /\ s.cs_next_var <= m.cs_next_var /\
  bop_scalar_seq R B (emitted_insts m t) C /\ B SUBSET C /\
  t.cs_current_insts = m.cs_current_insts ++ emitted_insts m t /\
  same_blocks m t /\ m.cs_next_var <= t.cs_next_var ==>
  bop_scalar_seq R A (emitted_insts s t) C /\ A SUBSET C /\
  t.cs_current_insts = s.cs_current_insts ++ emitted_insts s t /\
  same_blocks s t /\ s.cs_next_var <= t.cs_next_var
Proof
  strip_tac >> drule_all emitted_insts_append >> strip_tac >>
  simp[] >> rpt conj_tac
  >- (irule bop_scalar_seq_append >> metis_tac[])
  >- metis_tac[SUBSET_TRANS]
  >- fs[same_blocks_def] >> decide_tac
QED

(* The bind rule keeps the exact final available set existential.  Its
   postconditions track returned operands without discarding temporaries. *)
Theorem bop_scalar_compile_bind:
  (!u m. f s = (u,m) ==>
    ?B. (bop_scalar_seq R A (emitted_insts s m) B /\ A SUBSET B /\
         m.cs_current_insts = s.cs_current_insts ++ emitted_insts s m /\
         same_blocks s m /\ s.cs_next_var <= m.cs_next_var) /\ P u B) /\
  (!u m B v t.
    (bop_scalar_seq R A (emitted_insts s m) B /\ A SUBSET B /\
     m.cs_current_insts = s.cs_current_insts ++ emitted_insts s m /\
     same_blocks s m /\ s.cs_next_var <= m.cs_next_var) /\
    P u B /\ g u m = (v,t) ==>
    ?C. (bop_scalar_seq R B (emitted_insts m t) C /\ B SUBSET C /\
         t.cs_current_insts = m.cs_current_insts ++ emitted_insts m t /\
         same_blocks m t /\ m.cs_next_var <= t.cs_next_var) /\ Q v C) /\
  comp_bind f g s = (v,t) ==>
  ?C. (bop_scalar_seq R A (emitted_insts s t) C /\ A SUBSET C /\
       t.cs_current_insts = s.cs_current_insts ++ emitted_insts s t /\
       same_blocks s t /\ s.cs_next_var <= t.cs_next_var) /\ Q v C
Proof
  simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `C` >> reverse conj_tac >- simp[] >>
  irule bop_scalar_compile_chain >>
  qexistsl_tac [`B`, `cs'`] >> simp[]
QED

Theorem bop_scalar_compile_emit_op:
  emit_op opc ops st = (v, st') /\
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  EVERY (\op. op IN A) ops /\ (!x. x IN R ==> not_fresh_at st x) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> drule_all bop_scalar_seq_emit_op >> strip_tac >>
  imp_res_tac emit_op_extends >> drule emitted_insts_emit_op >>
  strip_tac >> qexists_tac `v INSERT A` >> simp[SUBSET_DEF]
QED

Theorem bop_scalar_compile_emit_assert:
  emit_void opc [op] st = ((), st') /\
  (opc = ASSERT \/ opc = ASSERT_UNREACHABLE) /\ op IN A ==>
  ?B. bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
      same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var
Proof
  strip_tac >> drule bop_scalar_seq_emit_assert >> simp[] >>
  disch_then (qspec_then `R` assume_tac) >>
  imp_res_tac emit_void_extends >> drule emitted_insts_emit_void >>
  strip_tac >> qexists_tac `A` >> simp[]
QED

Theorem bop_scalar_compile_return:
  comp_return r st = (v,st') /\ r IN A ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  simp[comp_return_def] >> strip_tac >> gvs[] >> qexists_tac `A` >>
  simp[emitted_insts_def, same_blocks_def]
QED

Theorem bop_scalar_compile_wrap_truncate:
  wrap_truncate res ty st = (v, st') /\ res IN A /\
  (!w. Lit w IN A) /\ (!x. x IN R ==> not_fresh_at st x) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  Cases_on `type_bits ty < 256`
  >- (Cases_on `is_signed_type ty` >> simp[wrap_truncate_def] >>
      strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
  simp[wrap_truncate_def] >> strip_tac >>
  drule bop_scalar_compile_return >> simp[]
QED


Theorem bop_scalar_compile_bind_run:
  comp_bind f g s = (v,t) ==>
  (!u m. f s = (u,m) ==>
    ?B. (bop_scalar_seq R A (emitted_insts s m) B /\ A SUBSET B /\
         m.cs_current_insts = s.cs_current_insts ++ emitted_insts s m /\
         same_blocks s m /\ s.cs_next_var <= m.cs_next_var) /\ P u B) /\
  (!u m B v t.
    (bop_scalar_seq R A (emitted_insts s m) B /\ A SUBSET B /\
     m.cs_current_insts = s.cs_current_insts ++ emitted_insts s m /\
     same_blocks s m /\ s.cs_next_var <= m.cs_next_var) /\
    P u B /\ g u m = (v,t) ==>
    ?C. (bop_scalar_seq R B (emitted_insts m t) C /\ B SUBSET C /\
         t.cs_current_insts = m.cs_current_insts ++ emitted_insts m t /\
         same_blocks m t /\ m.cs_next_var <= t.cs_next_var) /\ Q v C) ==>
  ?C. (bop_scalar_seq R A (emitted_insts s t) C /\ A SUBSET C /\
       t.cs_current_insts = s.cs_current_insts ++ emitted_insts s t /\
       same_blocks s t /\ s.cs_next_var <= t.cs_next_var) /\ Q v C
Proof
  rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) bop_scalar_compile_bind >>
  disch_then (qspecl_then [`R`, `Q`, `P`, `A`] mp_tac) >>
  disch_then irule >> asm_rewrite_tac[]
QED

Theorem bop_scalar_compile_select:
  compile_select cond x y st = (v, st') /\ cond IN A /\ x IN A /\ y IN A /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  simp[compile_select_def] >> strip_tac >>
  drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
      rpt strip_tac >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      `cond IN B /\ y IN B` by metis_tac[SUBSET_DEF] >>
      rule_assum_tac BETA_RULE >>
      drule bop_scalar_compile_bind_run >>
      disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `B`] mp_tac) >>
      impl_tac
      >- (conj_tac
          >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
          rpt strip_tac >> rule_assum_tac BETA_RULE >>
          `!z. z IN R ==> not_fresh_at m' z` by metis_tac[not_fresh_at_mono] >>
          `y IN B'` by metis_tac[SUBSET_DEF] >>
          drule bop_scalar_compile_emit_op >> simp[]) >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_emit_iszero:
  comp_bind (emit_op opc ops) (\u. emit_op ISZERO [u]) st = (v, st') /\
  MEM opc [LT; GT; SLT; SGT; EQ] /\ EVERY (\op. op IN A) ops /\
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
      drule bop_scalar_compile_emit_op >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_compare:
  MEM cmp [Lt; Gt; Eq; NotEq; LtE; GtE] /\
  compile_compare cmp x y ty st = (v, st') /\ x IN A /\ y IN A /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> gvs[compile_compare_def] >>
  Cases_on `is_uint256 ty` >> gvs[] >>
  FIRST [
    (drule bop_scalar_compile_emit_iszero >> simp[]),
    (drule bop_scalar_compile_emit_op >> simp[])]
QED

Theorem bop_scalar_compile_emit_checked:
  comp_bind (emit_op opc ops) (\u. emit_void ASSERT [u]) st = ((), st') /\
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  EVERY (\op. op IN A) ops /\ (!z. z IN R ==> not_fresh_at st z) ==>
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
      drule bop_scalar_compile_emit_assert >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_exclusion:
  comp_bind (emit_op EQ [x; k]) (\xmin.
    comp_bind (emit_op NOT [y]) (\ny.
      comp_bind (emit_op ISZERO [ny]) (\yneg.
        comp_bind (emit_op AND [xmin; yneg]) (\bad.
          emit_op ISZERO [bad])))) st = (v, st') /\
  x IN A /\ y IN A /\ k IN A /\ (!z. z IN R ==> not_fresh_at st z) ==>
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
              `!z. z IN R ==> not_fresh_at m'' z` by metis_tac[not_fresh_at_mono] >>
              `u IN B''` by metis_tac[SUBSET_DEF] >>
              drule bop_scalar_compile_bind_run >>
              disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `B''`] mp_tac) >>
              impl_tac
              >- (conj_tac
                  >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
                  rpt strip_tac >> rule_assum_tac BETA_RULE >>
                  `!z. z IN R ==> not_fresh_at m''' z` by metis_tac[not_fresh_at_mono] >>
                  drule bop_scalar_compile_emit_op >> simp[]) >> simp[]) >> simp[]) >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_signed_bounds:
  comp_bind (emit_op SLT [x; lo]) (\below.
    comp_bind (emit_op ISZERO [below]) (\ge.
      comp_bind (emit_op SGT [x; hi]) (\above.
        comp_bind (emit_op ISZERO [above]) (\le.
          emit_op AND [ge; le])))) st = (v, st') /\
  x IN A /\ lo IN A /\ hi IN A /\ (!z. z IN R ==> not_fresh_at st z) ==>
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
      drule bop_scalar_compile_bind_run >>
      disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `B`] mp_tac) >>
      impl_tac
      >- (conj_tac
          >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
          rpt strip_tac >> rule_assum_tac BETA_RULE >>
          `!z. z IN R ==> not_fresh_at m' z` by metis_tac[not_fresh_at_mono] >>
          `x IN B' /\ hi IN B'` by metis_tac[SUBSET_DEF] >>
          drule bop_scalar_compile_bind_run >>
          disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `B'`] mp_tac) >>
          impl_tac
          >- (conj_tac
              >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
              rpt strip_tac >> rule_assum_tac BETA_RULE >>
              `!z. z IN R ==> not_fresh_at m'' z` by metis_tac[not_fresh_at_mono] >>
              drule bop_scalar_compile_bind_run >>
              disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `B''`] mp_tac) >>
              impl_tac
              >- (conj_tac
                  >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
                  rpt strip_tac >> rule_assum_tac BETA_RULE >>
                  `!z. z IN R ==> not_fresh_at m''' z` by metis_tac[not_fresh_at_mono] >>
                  `u' IN B'''` by metis_tac[SUBSET_DEF] >>
                  drule bop_scalar_compile_emit_op >> simp[]) >> simp[]) >> simp[]) >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_signed_bounds_checked:
  comp_bind
    (comp_bind (emit_op SLT [x; lo]) (\below.
      comp_bind (emit_op ISZERO [below]) (\ge.
        comp_bind (emit_op SGT [x; hi]) (\above.
          comp_bind (emit_op ISZERO [above]) (\le. emit_op AND [ge; le])))))
    (\ok. emit_void ASSERT [ok]) st = ((), st') /\
  x IN A /\ lo IN A /\ hi IN A /\ (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var
Proof
  strip_tac >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. T`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_signed_bounds >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >> Cases_on `v` >>
      drule bop_scalar_compile_emit_assert >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_clamp:
  compile_clamp x ty st = ((), st') /\ x IN A /\ (!w. Lit w IN A) /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var
Proof
  Cases_on `type_bounds ty` >>
  Cases_on `is_signed_type ty` >> simp[compile_clamp_def] >> strip_tac
  >- suspend "signed"
  >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. T`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      Cases_on `v` >> drule bop_scalar_compile_emit_checked >> simp[]) >> simp[]
QED

Resume bop_scalar_compile_clamp[signed]:
  drule (SRULE [comp_bind_assoc] bop_scalar_compile_signed_bounds_checked) >> simp[]
QED
Finalise bop_scalar_compile_clamp

Theorem bop_scalar_compile_clamp_and_return:
  clamp_and_return res ty st = (v, st') /\ res IN A /\ (!w. Lit w IN A) /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  simp[clamp_and_return_def, comp_ignore_bind_def] >> strip_tac >>
  drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. T`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> Cases_on `u` >>
          drule bop_scalar_compile_clamp >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `res IN B` by metis_tac[SUBSET_DEF] >>
      drule bop_scalar_compile_return >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_emit_wrap:
  comp_bind (emit_op opc [x; y]) (\u. wrap_truncate u ty) st = (v, st') /\
  MEM opc [ADD; SUB; MUL; Div; SDIV] /\ x IN A /\ y IN A /\
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
      drule bop_scalar_compile_wrap_truncate >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_emit_select:
  comp_bind (emit_op opc [x; y]) (\u. compile_select u x y) st = (v, st') /\
  MEM opc [LT; GT; SLT; SGT] /\ x IN A /\ y IN A /\
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
      `x IN B /\ y IN B` by metis_tac[SUBSET_DEF] >>
      drule bop_scalar_compile_select >> simp[]) >> simp[]
QED

Theorem bop_scalar_compile_binop_elementary:
  MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv; And; Or; XOr; ShL; ShR;
           Eq; NotEq; Lt; LtE; Gt; GtE; Min; Max] /\
  compile_binop bop x y ty base_literal exp_literal st = (v, st') /\
  x IN A /\ y IN A /\ (!w. Lit w IN A) /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> gvs[compile_binop_def] >>
  Cases_on `is_signed_type ty` >> Cases_on `is_uint256 ty` >> gvs[] >>
  FIRST [
    (drule bop_scalar_compile_emit_wrap >> simp[]),
    (drule bop_scalar_compile_emit_op >> simp[]),
    (drule_at (Pat `compile_compare _ _ _ _ _ = _`) bop_scalar_compile_compare >> simp[]),
    (drule bop_scalar_compile_emit_select >> simp[])]
QED
