Theory asmOptNonemptyCompose
Ancestors
  asmOptimizer pair

Theorem optimize_round_preserves_predicate:
  (!p. P p ==> P (FST (prune_unreachable_code p))) /\
  (!p. P p ==> P (FST (merge_iszero p))) /\
  (!p. P p ==> P (FST (merge_jumpdests p))) /\
  (!p. P p ==> P (FST (prune_inefficient_jumps p))) /\
  (!p. P p ==> P (FST (optimize_inefficient_jumps p))) /\
  (!p. P p ==> P (FST (prune_unused_jumpdests p))) /\
  (!p q ch. P p /\ stack_peephole_opts p = SOME (q,ch) ==> P q)
  ==>
  !p q ch. P p /\ optimize_round p = SOME (q,ch) ==> P q
Proof
  rpt strip_tac >>
  gvs[optimize_round_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs()] >>
  metis_tac[FST]
QED

Theorem optimize_assembly_rounds_preserves_predicate:
  (!p q ch. P p /\ optimize_round p = SOME (q,ch) ==> P q) ==>
  !n p q. P p /\ optimize_assembly_rounds n p = SOME q ==> P q
Proof
  strip_tac >> Induct >>
  simp[optimize_assembly_rounds_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  metis_tac[]
QED

Theorem asm_opt_finalizer_preserves_predicate:
  (!p q ch. P p /\ optimize_round p = SOME (q,ch) ==> P q) ==>
  !policy p q. P p /\ asm_opt_finalizer policy p = SOME q ==> P q
Proof
  rpt strip_tac >>
  gvs[asm_opt_finalizer_def, optimize_assembly_def, AllCaseEqs()] >>
  drule optimize_assembly_rounds_preserves_predicate >>
  disch_then drule_all >> simp[]
QED
