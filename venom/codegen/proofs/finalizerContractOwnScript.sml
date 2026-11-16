(* Own-code finalizer composition; both programs read the same bytes.
   The optimizer contract is conditional on its seven rule obligations. *)

Theory finalizerContractOwn
Ancestors
  asmSymOwnCode asmSymSem asmOptimizer finalizerContract

(* ===== Fuel ===== *)

Theorem sym_run_own_less_fuel:
  ∀f1 f2 p env own ss.
    f1 ≤ f2 ⇒
    sym_run_own p env own f1 ss = sym_run_own p env own f2 ss ∨
    sym_run_own p env own f1 ss = SymError "out of fuel"
Proof
  Induct >- (rpt strip_tac >> disj2_tac >> simp[Once sym_run_own_def]) >>
  rpt strip_tac >>
  Cases_on `f2` >> gvs[] >>
  ONCE_REWRITE_TAC[sym_run_own_def] >> simp[] >>
  rw[] >> CASE_TAC >> simp[]
QED

Theorem sym_terminal_own_not_bad:
  sym_terminal (sym_run_own p env own fuel ss) ⇒
  ∀fuel' msg. sym_run_own p env own fuel' ss ≠ SymBad msg
Proof
  rpt strip_tac >>
  Cases_on `fuel' ≤ fuel`
  >- (drule_then (qspecl_then [`p`, `env`, `own`, `ss`] strip_assume_tac)
        sym_run_own_less_fuel >> gvs[sym_terminal_def]) >>
  `fuel ≤ fuel'` by decide_tac >>
  drule_then (qspecl_then [`p`, `env`, `own`, `ss`] strip_assume_tac)
    sym_run_own_less_fuel >> gvs[sym_terminal_def]
QED

Theorem sym_terminal_own_disciplined:
  asm_static_wf p ∧ sym_terminal (sym_run_own p env own fuel (sym_init s)) ⇒
  label_disciplined_own env own p s
Proof
  rw[label_disciplined_own_def] >> metis_tac[sym_terminal_own_not_bad]
QED

(* ===== asm_refines_own ===== *)

Theorem asm_refines_own_refl:
  asm_refines_own p p
Proof
  rw[asm_refines_own_def] >> metis_tac[sym_result_rel_refl]
QED

Theorem asm_refines_own_trans:
  asm_refines_own p1 p2 ∧ asm_refines_own p2 p3 ⇒ asm_refines_own p1 p3
Proof
  rw[asm_refines_own_def] >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule sym_result_rel_terminal >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[sym_result_rel_trans]
QED

(* ===== Finalizers ===== *)

Theorem finalizer_correct_own_identity:
  finalizer_correct_own (K SOME)
Proof
  simp[finalizer_correct_own_def, asm_refines_own_refl]
QED

Theorem finalizer_correct_own_seq:
  finalizer_correct_own f ∧ finalizer_correct_own g ⇒
  finalizer_correct_own (λrp p. OPTION_BIND (f rp p) (g rp))
Proof
  rw[finalizer_correct_own_def] >> Cases_on `f rp p` >> gvs[] >>
  metis_tac[asm_refines_own_trans]
QED

(* The contract as the plan states it: for a label-disciplined input whose
   run ends without error, the output is label-disciplined and its run ends
   the same way. *)
Theorem finalizer_correct_own_run:
  finalizer_correct_own f ∧ f rp p = SOME p' ∧
  label_disciplined_own env own p s ∧
  sym_terminal (sym_run_own p env own fuel (sym_init s)) ⇒
  label_disciplined_own env own p' s ∧
  ∃fuel'. sym_result_rel (sym_run_own p env own fuel (sym_init s))
                         (sym_run_own p' env own fuel' (sym_init s))
Proof
  rw[finalizer_correct_own_def, label_disciplined_own_def] >>
  first_x_assum drule >> rw[asm_refines_own_def] >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule sym_result_rel_terminal >> strip_tac >>
  metis_tac[sym_terminal_own_not_bad]
QED

(* ===== The optimizer, from its rules ===== *)

Theorem optimize_round_refines_own:
  (∀p. asm_refines_own p (FST (prune_unreachable_code p))) ∧
  (∀p. asm_refines_own p (FST (merge_iszero p))) ∧
  (∀p. asm_refines_own p (FST (merge_jumpdests p))) ∧
  (∀p. asm_refines_own p (FST (prune_inefficient_jumps p))) ∧
  (∀p. asm_refines_own p (FST (optimize_inefficient_jumps p))) ∧
  (∀p. asm_refines_own p (FST (prune_unused_jumpdests p))) ∧
  (∀p p' c. stack_peephole_opts p = SOME (p', c) ⇒ asm_refines_own p p') ⇒
  ∀p p' c. optimize_round p = SOME (p', c) ⇒ asm_refines_own p p'
Proof
  rw[optimize_round_def] >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[asm_refines_own_trans, pairTheory.FST]
QED

Theorem optimize_assembly_rounds_refines_own:
  (∀p p' c. optimize_round p = SOME (p', c) ⇒ asm_refines_own p p') ⇒
  ∀n p p'. optimize_assembly_rounds n p = SOME p' ⇒ asm_refines_own p p'
Proof
  strip_tac >> Induct >> simp[optimize_assembly_rounds_def] >>
  rpt gen_tac >> CASE_TAC >> PairCases_on `x` >> rw[] >>
  metis_tac[asm_refines_own_trans]
QED

Theorem asm_opt_finalizer_correct_own:
  (∀p. asm_refines_own p (FST (prune_unreachable_code p))) ∧
  (∀p. asm_refines_own p (FST (merge_iszero p))) ∧
  (∀p. asm_refines_own p (FST (merge_jumpdests p))) ∧
  (∀p. asm_refines_own p (FST (prune_inefficient_jumps p))) ∧
  (∀p. asm_refines_own p (FST (optimize_inefficient_jumps p))) ∧
  (∀p. asm_refines_own p (FST (prune_unused_jumpdests p))) ∧
  (∀p p' c. stack_peephole_opts p = SOME (p', c) ⇒ asm_refines_own p p') ⇒
  finalizer_correct_own asm_opt_finalizer
Proof
  strip_tac >> mp_tac optimize_round_refines_own >> impl_tac >- simp[] >>
  strip_tac >>
  drule optimize_assembly_rounds_refines_own >> strip_tac >>
  rw[finalizer_correct_own_def, asm_opt_finalizer_def, optimize_assembly_def] >>
  Cases_on `rp.rpol_final_assembly = FAP_Optimize` >>
  gvs[asm_refines_own_refl] >> metis_tac[]
QED

(* Every accepted finalizer is correct, given the optimizer's rules. *)
Theorem accepted_finalizers_correct_own:
  (∀p. asm_refines_own p (FST (prune_unreachable_code p))) ∧
  (∀p. asm_refines_own p (FST (merge_iszero p))) ∧
  (∀p. asm_refines_own p (FST (merge_jumpdests p))) ∧
  (∀p. asm_refines_own p (FST (prune_inefficient_jumps p))) ∧
  (∀p. asm_refines_own p (FST (optimize_inefficient_jumps p))) ∧
  (∀p. asm_refines_own p (FST (prune_unused_jumpdests p))) ∧
  (∀p p' c. stack_peephole_opts p = SOME (p', c) ⇒ asm_refines_own p p') ⇒
  ∀f. f ∈ accepted_finalizers ⇒ finalizer_correct_own f
Proof
  strip_tac >> mp_tac asm_opt_finalizer_correct_own >> impl_tac >- simp[] >>
  rw[accepted_finalizers_def] >> simp[finalizer_correct_own_identity]
QED
