Theory staticAbortOptPruneUnreachableWalk
Ancestors
  asmOptimizer asmOptPruneUnreachable

Theorem prune_unreachable_walk_preserves_contextual_under[local]:
  (!pre op x tail.
    asm_terminal_op op /\ ~asm_reachable_marker x /\
    P (pre ++ [op;x] ++ tail) ==> P (pre ++ [op] ++ tail)) ==>
  !rest dropping pre.
    (dropping ==> ?pre0 op. pre = pre0 ++ [op] /\ asm_terminal_op op) /\
    P (pre ++ rest) ==>
    P (pre ++ FST (prune_unreachable_walk dropping rest))
Proof
  strip_tac >> Induct
  >- simp[prune_unreachable_walk_def] >>
  rpt strip_tac >> simp[prune_unreachable_walk_fst] >>
  IF_CASES_TAC
  >- (gvs[] >>
      first_x_assum (qspecl_then [`T`, `pre0 ++ [op]`] mp_tac) >>
      impl_tac
      >- (conj_tac
          >- (strip_tac >> qexistsl_tac [`pre0`, `op`] >> simp[]) >>
          qpat_x_assum `!pre op x tail. _` (qspecl_then [`pre0`, `op`, `h`, `rest`] mp_tac) >>
          full_simp_tac std_ss [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
      simp[]) >>
  first_x_assum (qspecl_then [`asm_terminal_op h`, `pre ++ [h]`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (strip_tac >> qexistsl_tac [`pre`, `h`] >> simp[]) >>
      full_simp_tac std_ss [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]
QED

Theorem prune_unreachable_walk_preserves_contextual:
  (!pre op x tail.
    asm_terminal_op op /\ ~asm_reachable_marker x /\
    P (pre ++ [op;x] ++ tail) ==> P (pre ++ [op] ++ tail)) ==>
  !p. P p ==> P (FST (prune_unreachable_code p))
Proof
  strip_tac >> gen_tac >> strip_tac >>
  drule prune_unreachable_walk_preserves_contextual_under >>
  disch_then (qspecl_then [`p`, `F`, `[]`] mp_tac) >>
  simp[prune_unreachable_code_def]
QED
