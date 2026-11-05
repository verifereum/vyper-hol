Theory bodyPtrBopScalarCompile
Ancestors
  bodyPtrBopScalarSeq emitHelperProps compileEnv exprLoweringProps exprLowering
  freshWrites list pred_set

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
