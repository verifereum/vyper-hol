(* Compose the optimizer's per-rule step bounds over the finalizer. *)
Theory asmOptFinalizerWithin
Ancestors
  asmRefinesWithin asmOptNonemptyCompose asmOptimizer asmOptPruneUnreachable asmOptMergeIszero
  asmOptMergeJumpdests asmOptPruneJumps asmOptInefficientJumps
  asmOptPruneUnused asmOptPeephole

Theorem optimize_round_refines_both[local]:
  (∀p. asm_refines_both p (FST (prune_unreachable_code p))) ∧
  (∀p. asm_refines_both p (FST (merge_iszero p))) ∧
  (∀p. asm_refines_both p (FST (merge_jumpdests p))) ∧
  (∀p. asm_refines_both p (FST (prune_inefficient_jumps p))) ∧
  (∀p. asm_refines_both p (FST (optimize_inefficient_jumps p))) ∧
  (∀p. asm_refines_both p (FST (prune_unused_jumpdests p))) ∧
  (∀p p' c. stack_peephole_opts p = SOME (p', c) ⇒ asm_refines_both p p') ⇒
  ∀p p' c. optimize_round p = SOME (p', c) ⇒ asm_refines_both p p'
Proof
  strip_tac >> qspec_then `asm_refines_both` mp_tac optimize_round_relation >>
  simp[] >> impl_tac
  >- metis_tac[asm_refines_both_trans] >> simp[]
QED

Theorem optimize_assembly_rounds_refines_both[local]:
  (∀p p' c. optimize_round p = SOME (p', c) ⇒ asm_refines_both p p') ⇒
  ∀n p p'. optimize_assembly_rounds n p = SOME p' ⇒ asm_refines_both p p'
Proof
  strip_tac >> qspec_then `asm_refines_both` mp_tac optimize_rounds_relation >>
  simp[] >> impl_tac
  >- metis_tac[asm_refines_both_trans] >> simp[]
QED

Theorem asm_opt_finalizer_refines_both:
  asm_opt_finalizer policy p = SOME q ⇒ asm_refines_both p q
Proof
  mp_tac optimize_round_refines_both >>
  impl_tac
  >- simp[prune_unreachable_code_refines_both, merge_iszero_refines_both,
          merge_jumpdests_refines_both, prune_inefficient_jumps_refines_both,
          optimize_inefficient_jumps_refines_both, prune_unused_jumpdests_refines_both,
          stack_peephole_opts_refines_both] >>
  strip_tac >>
  drule optimize_assembly_rounds_refines_both >> strip_tac >>
  rw[asm_opt_finalizer_def, optimize_assembly_def] >>
  gvs[AllCaseEqs(), asm_refines_both_refl] >> metis_tac[]
QED
