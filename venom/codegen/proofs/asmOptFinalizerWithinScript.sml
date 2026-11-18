(* Compose the optimizer's per-rule step bounds over the finalizer. *)
Theory asmOptFinalizerWithin
Ancestors
  asmRefinesWithin asmOptimizer asmOptPruneUnreachable asmOptMergeIszero
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
  rw[optimize_round_def] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `prune_unreachable_code src = (a1,b1)` >>
  rename1 `merge_iszero a1 = (a2,b2)` >>
  rename1 `merge_jumpdests a2 = (a3,b3)` >>
  rename1 `prune_inefficient_jumps a3 = (a4,b4)` >>
  rename1 `optimize_inefficient_jumps a4 = (a5,b5)` >>
  rename1 `prune_unused_jumpdests a5 = (a6,b6)` >>
  rename1 `stack_peephole_opts a6 = SOME (dest,b7)` >>
  `asm_refines_both src a1 /\ asm_refines_both a1 a2 /\
   asm_refines_both a2 a3 /\ asm_refines_both a3 a4 /\
   asm_refines_both a4 a5 /\ asm_refines_both a5 a6 /\ asm_refines_both a6 dest` by
    (rpt conj_tac >> metis_tac[pairTheory.FST]) >>
  fs[] >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  imp_res_tac asm_refines_both_trans >> first_assum ACCEPT_TAC
QED

Theorem optimize_assembly_rounds_refines_both[local]:
  (∀p p' c. optimize_round p = SOME (p', c) ⇒ asm_refines_both p p') ⇒
  ∀n p p'. optimize_assembly_rounds n p = SOME p' ⇒ asm_refines_both p p'
Proof
  strip_tac >> Induct >> simp[optimize_assembly_rounds_def] >>
  rpt gen_tac >> CASE_TAC >> PairCases_on `x` >> rw[] >>
  metis_tac[asm_refines_both_trans]
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
