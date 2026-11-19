Theory staticAbortOptPruneJumpsWalk
Ancestors
  asmOptimizer asmOptPruneJumps

(* Syntax-only lifting: semantic clients must prove the contextual rewrite. *)
Theorem prune_jumps_walk_preserves_contextual:
  (!pre a b c tail.
     asm_jump_to_next a b c /\ P (pre ++ [a;b;c] ++ tail) ==>
     P (pre ++ [c] ++ tail)) ==>
  !p. P p ==> P (FST (prune_inefficient_jumps p))
Proof
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  strip_tac >>
  qsuff_tac `!sfx pre. P (pre ++ sfx) ==>
    P (pre ++ FST (prune_inefficient_jumps sfx))`
  >- (rpt strip_tac >> first_x_assum (qspecl_then [`p`, `[]`] mp_tac) >> simp[]) >>
  recInduct prune_inefficient_jumps_ind >>
  reverse (rpt conj_tac)
  >- simp[prune_inefficient_jumps_def]
  >- simp[prune_inefficient_jumps_def]
  >- simp[prune_inefficient_jumps_def] >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  simp[prune_inefficient_jumps_fst] >>
  IF_CASES_TAC
  >- (gvs[] >> first_x_assum irule >>
      qpat_x_assum `!pre a b c tail. _` mp_tac >>
      disch_then irule >> qexistsl [`a`, `b`] >> simp[]) >>
  gvs[] >>
  first_x_assum (qspec_then `pre ++ [a]` mp_tac) >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  simp[]
QED
