Theory staticAbortOptConditionalJumpsWalk
Ancestors
  asmOptimizer asmOptInefficientJumps

Theorem conditional_jumps_walk_preserves_contextual:
  (!pre a b c d e tail.
    asm_jumpi_over_jump a b c d e /\
    P (pre ++ [a;b;c;d;e] ++ tail) ==>
    P (pre ++ [AsmOp "ISZERO";c;AsmOp "JUMPI";e] ++ tail)) ==>
  !p. P p ==> P (FST (optimize_inefficient_jumps p))
Proof
  strip_tac >>
  `!p pre. P (pre ++ p) ==>
    P (pre ++ FST (optimize_inefficient_jumps p))`
    suffices_by metis_tac[listTheory.APPEND] >>
  ho_match_mp_tac optimize_inefficient_jumps_ind >>
  reverse (rpt conj_tac)
  >- simp[optimize_inefficient_jumps_def]
  >- simp[optimize_inefficient_jumps_def]
  >- simp[optimize_inefficient_jumps_def]
  >- simp[optimize_inefficient_jumps_def]
  >- simp[optimize_inefficient_jumps_def] >>
  rpt gen_tac >> strip_tac >>
  simp[optimize_inefficient_jumps_fst] >>
  reverse IF_CASES_TAC
  >- (gvs[] >> rpt strip_tac >>
      first_x_assum (qspec_then `pre ++ [a]` mp_tac) >>
      pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
      simp[]) >>
  gvs[] >> rpt strip_tac >>
  first_x_assum irule >>
  qpat_x_assum `!pre a b c d e tail. _`
    (mp_tac o REWRITE_RULE [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  disch_then irule >>
  goal_assum (drule_at Any) >> simp[]
QED
