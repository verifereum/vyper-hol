(* Compose the per-pass bounds for runs reading the installed bytes. *)
Theory asmOptFinalizerWithinOwn
Ancestors
  asmSpliceWithinOwn asmOptNonemptyCompose asmOptimizer
  asmOptWithinSplices asmOptWithinRename asmOptWithinPeephole
  asmOptWithinIszero asmOptWithinInefficient

Theorem optimize_round_within_own[local]:
  !p q c. optimize_round p = SOME (q,c) ==> asm_within_own p q
Proof
  BETA_TAC >>
  mp_tac (BETA_RULE (Q.SPEC `asm_within_own` optimize_round_relation)) >>
  (impl_tac >-
    (rpt conj_tac >>
     MAP_FIRST MATCH_ACCEPT_TAC (map (GEN_ALL o BETA_RULE)
       [asm_within_own_trans, prune_unreachable_code_within_own,
        merge_iszero_within_own, merge_jumpdests_within_own,
        prune_inefficient_jumps_within_own, optimize_inefficient_jumps_within_own,
        prune_unused_jumpdests_within_own, stack_peephole_opts_within_own]))) >>
  disch_then ACCEPT_TAC
QED

Theorem asm_opt_finalizer_within_own:
  asm_opt_finalizer policy p = SOME q ==> asm_within_own p q
Proof
  BETA_TAC >>
  mp_tac (BETA_RULE (Q.SPEC `asm_within_own` optimize_rounds_relation)) >>
  (impl_tac >-
    (conj_tac
     >- MATCH_ACCEPT_TAC (GEN_ALL (BETA_RULE asm_within_own_trans)) >>
     MATCH_ACCEPT_TAC (BETA_RULE optimize_round_within_own))) >>
  strip_tac >>
  rw[asm_opt_finalizer_def, optimize_assembly_def] >>
  gvs[AllCaseEqs(), asm_within_own_refl] >> metis_tac[]
QED
