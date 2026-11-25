(* The size guard is a returndata-size read followed by a protected scalar tail. *)
Theory bodyExtSizeScalarCutMods
Ancestors
  abiReturnSize bodyPtrBopScalarCompile builtinSimple builtinProps
  exprLoweringProps emitHelperProps emitHelper exprLowering
  compileEnv loweringStateRelDefs freshWrites venomInst
  words pred_set list rich_list arithmetic

Theorem size_cut_append[local]:
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  c.cs_current_insts = b.cs_current_insts ++ emitted_insts b c ==>
  emitted_insts a c = emitted_insts a b ++ emitted_insts b c /\
  c.cs_current_insts = a.cs_current_insts ++ emitted_insts a c
Proof
  strip_tac >> drule_all_then assume_tac emitted_insts_append >>
  asm_rewrite_tac[APPEND_ASSOC]
QED

Theorem ext_size_scalar_cut_mods:
  compile_return_value_decode low cap k = (hi,hs) ==>
  ?rds m B.
    emit_op RETURNDATASIZE [] k = (rds,m) /\
    cs_extends k m /\ cs_extends m hs /\
    emitted_insts k hs = emitted_insts k m ++ emitted_insts m hs /\
    hs.cs_current_bb = m.cs_current_bb /\
    hs.cs_current_insts = m.cs_current_insts ++ emitted_insts m hs /\
    bop_scalar_seq {x | not_fresh_at k x}
      (rds INSERT {Lit (n2w low); Lit (n2w cap)}) (emitted_insts m hs) B /\
    hi IN B
Proof
  strip_tac >> drule abi_return_size_code >> strip_tac >>
  qpat_x_assum `compile_return_value_decode _ _ _ = _` mp_tac >>
  simp[compile_return_value_decode_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `emit_op RETURNDATASIZE [] k = (rds,m)` >>
  rename1 `emit_op LT [rds; Lit (n2w low)] m = (small,c2)` >>
  rename1 `emit_op ISZERO [small] c2 = (good,c3)` >>
  rename1 `emit_void ASSERT [good] c3 = (unit_result,c4)` >>
  Cases_on `unit_result` >>
  rename1 `emit_op LT [rds; Lit (n2w cap)] c4 = (cmp,c5)` >>
  every_drule_then strip_assume_tac emitted_insts_emit_op >>
  every_drule_then strip_assume_tac emitted_insts_emit_void >>
  `!x. not_fresh_at k x ==> not_fresh_at m x /\ not_fresh_at c2 x /\
        not_fresh_at c4 x /\ not_fresh_at c5 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `k` >> simp[]) >>
  qabbrev_tac `R = {x | not_fresh_at k x}` >>
  qabbrev_tac `A = rds INSERT {Lit (n2w low); Lit (n2w cap)}` >>
  `bop_scalar_seq R A (emitted_insts m c2) (small INSERT A)` by
    (irule bop_scalar_seq_emit_op >>
     conj_tac >- fs[Abbr `R`] >>
     qexistsl_tac [`LT`, `[rds; Lit (n2w low)]`] >> simp[Abbr `A`]) >>
  `bop_scalar_seq R (small INSERT A) (emitted_insts c2 c3)
      (good INSERT small INSERT A)` by
    (irule bop_scalar_seq_emit_op >>
     conj_tac >- fs[Abbr `R`] >>
     qexistsl_tac [`ISZERO`, `[small]`] >> simp[]) >>
  `bop_scalar_seq R (good INSERT small INSERT A) (emitted_insts c3 c4)
      (good INSERT small INSERT A)` by
    (irule bop_scalar_seq_emit_assert >> qexistsl_tac [`good`, `ASSERT`] >> simp[]) >>
  `bop_scalar_seq R (good INSERT small INSERT A) (emitted_insts c4 c5)
      (cmp INSERT good INSERT small INSERT A)` by
    (irule bop_scalar_seq_emit_op >>
     conj_tac >- fs[Abbr `R`] >>
     qexistsl_tac [`LT`, `[rds; Lit (n2w cap)]`] >> simp[Abbr `A`]) >>
  drule_at (Pat `compile_select _ _ _ c5 = _`) bop_scalar_compile_select >>
  disch_then (qspecl_then [`R`,`cmp INSERT good INSERT small INSERT A`] mp_tac) >>
  impl_tac >- fs[Abbr `R`, Abbr `A`] >> strip_tac >>
  `emitted_insts m c3 = emitted_insts m c2 ++ emitted_insts c2 c3 /\
   c3.cs_current_insts = m.cs_current_insts ++ emitted_insts m c3` by
    (irule size_cut_append >> asm_rewrite_tac[]) >>
  `emitted_insts m c4 = emitted_insts m c3 ++ emitted_insts c3 c4 /\
   c4.cs_current_insts = m.cs_current_insts ++ emitted_insts m c4` by
    (irule size_cut_append >> asm_rewrite_tac[]) >>
  `emitted_insts m c5 = emitted_insts m c4 ++ emitted_insts c4 c5 /\
   c5.cs_current_insts = m.cs_current_insts ++ emitted_insts m c5` by
    (irule size_cut_append >> asm_rewrite_tac[]) >>
  `emitted_insts m hs = emitted_insts m c5 ++ emitted_insts c5 hs /\
   hs.cs_current_insts = m.cs_current_insts ++ emitted_insts m hs` by
    (irule size_cut_append >> asm_rewrite_tac[]) >>
  qexists_tac `B` >>
  qpat_assum `emit_op RETURNDATASIZE [] k = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  `hs.cs_current_bb = m.cs_current_bb /\ hs.cs_blocks = m.cs_blocks` by
    fs[same_blocks_def] >>
  conj_tac >- (simp[cs_extends_def] >> qexists_tac `[]` >> fs[IS_PREFIX_APPEND,same_blocks_def]) >>
  conj_tac >- (simp[cs_extends_def] >> qexists_tac `[]` >> simp[IS_PREFIX_APPEND]) >>
  conj_tac >- (irule emitted_insts_append >> asm_rewrite_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_assum `hs.cs_current_insts = k.cs_current_insts ++ _` (SUBST1_TAC o SYM) >>
                first_assum ACCEPT_TAC) >>
  conj_tac >- (
    qpat_assum `emitted_insts m hs = _` (SUBST1_TAC) >>
    irule bop_scalar_seq_append >> goal_assum (drule_at Any) >>
    qpat_assum `emitted_insts m c5 = _` SUBST1_TAC >>
    irule bop_scalar_seq_append >> goal_assum (drule_at Any) >>
    qpat_assum `emitted_insts m c4 = _` SUBST1_TAC >>
    irule bop_scalar_seq_append >> goal_assum (drule_at Any) >>
    qpat_assum `emitted_insts m c3 = _` SUBST1_TAC >>
    irule bop_scalar_seq_append >> goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
