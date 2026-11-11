(*
 * Composition lemmas for the finalizer contract (asmSymSem).
 *
 * asm_refines is reflexive and transitive, so the identity finalizer is
 * correct, correct finalizers compose, and the final assembly optimizer is
 * correct once each of its rules refines its input.
 *
 * TOP-LEVEL:
 *   finalizer_correct_identity  — K SOME is correct
 *   finalizer_correct_seq       — sequencing correct finalizers
 *   finalizer_correct_run       — the contract in terms of label_disciplined
 *   optimize_round_refines      — one optimizer round, from its rules
 *   asm_opt_finalizer_correct   — the optimizer, from its rules
 *)

Theory finalizerContract
Ancestors
  asmSymSem asmOptimizer

(* Every opcode asm_step_op dispatches, other than DUPn and SWAPn, has an
   operand count. *)
Theorem asm_op_arity_table_complete:
  EVERY (λ(name, b). IS_SOME (ALOOKUP dup_table name) ∨
                     IS_SOME (ALOOKUP swap_table name) ∨
                     IS_SOME (ALOOKUP asm_op_arity_table name) ∨
                     name = "PUSH0")
    evm_opcode_table
Proof
  EVAL_TAC
QED

(* ===== Fuel ===== *)

Theorem sym_run_less_fuel:
  ∀f1 f2 p env ss.
    f1 ≤ f2 ⇒
    sym_run p env f1 ss = sym_run p env f2 ss ∨
    sym_run p env f1 ss = SymError "out of fuel"
Proof
  Induct >- (rpt strip_tac >> disj2_tac >> simp[Once sym_run_def]) >>
  rpt strip_tac >>
  Cases_on `f2` >> gvs[] >>
  ONCE_REWRITE_TAC[sym_run_def] >> simp[] >>
  rw[] >> CASE_TAC >> simp[]
QED

Theorem sym_terminal_not_bad:
  sym_terminal (sym_run p env fuel ss) ⇒
  ∀fuel' msg. sym_run p env fuel' ss ≠ SymBad msg
Proof
  rpt strip_tac >>
  Cases_on `fuel' ≤ fuel`
  >- (drule_then (qspecl_then [`p`, `env`, `ss`] strip_assume_tac)
        sym_run_less_fuel >> gvs[sym_terminal_def]) >>
  `fuel ≤ fuel'` by decide_tac >>
  drule_then (qspecl_then [`p`, `env`, `ss`] strip_assume_tac)
    sym_run_less_fuel >> gvs[sym_terminal_def]
QED

Theorem sym_terminal_disciplined:
  asm_static_wf p ∧ sym_terminal (sym_run p env fuel (sym_init s)) ⇒
  label_disciplined env p s
Proof
  rw[label_disciplined_def] >> metis_tac[sym_terminal_not_bad]
QED

(* ===== The result relation ===== *)

Theorem sym_result_rel_terminal:
  sym_result_rel r r' ⇒ sym_terminal r ∧ sym_terminal r'
Proof
  Cases_on `r` >> Cases_on `r'` >> simp[sym_result_rel_def, sym_terminal_def]
QED

Theorem sym_result_rel_refl:
  sym_terminal r ⇒ sym_result_rel r r
Proof
  Cases_on `r` >> simp[sym_result_rel_def, sym_terminal_def]
QED

Theorem sym_result_rel_trans:
  sym_result_rel r1 r2 ∧ sym_result_rel r2 r3 ⇒ sym_result_rel r1 r3
Proof
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[sym_result_rel_def]
QED

(* ===== asm_refines ===== *)

Theorem asm_refines_refl:
  asm_refines p p
Proof
  rw[asm_refines_def] >> metis_tac[sym_result_rel_refl]
QED

Theorem asm_refines_trans:
  asm_refines p1 p2 ∧ asm_refines p2 p3 ⇒ asm_refines p1 p3
Proof
  rw[asm_refines_def] >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule sym_result_rel_terminal >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[sym_result_rel_trans]
QED

(* ===== Finalizers ===== *)

Theorem finalizer_correct_identity:
  finalizer_correct (K SOME)
Proof
  simp[finalizer_correct_def, asm_refines_refl]
QED

Theorem finalizer_correct_seq:
  finalizer_correct f ∧ finalizer_correct g ⇒
  finalizer_correct (λrp p. OPTION_BIND (f rp p) (g rp))
Proof
  rw[finalizer_correct_def] >> Cases_on `f rp p` >> gvs[] >>
  metis_tac[asm_refines_trans]
QED

(* The contract as the plan states it: for a label-disciplined input whose
   run ends without error, the output is label-disciplined and its run ends
   the same way. *)
Theorem finalizer_correct_run:
  finalizer_correct f ∧ f rp p = SOME p' ∧
  label_disciplined env p s ∧
  sym_terminal (sym_run p env fuel (sym_init s)) ⇒
  label_disciplined env p' s ∧
  ∃fuel'. sym_result_rel (sym_run p env fuel (sym_init s))
                         (sym_run p' env fuel' (sym_init s))
Proof
  rw[finalizer_correct_def, label_disciplined_def] >>
  first_x_assum drule >> rw[asm_refines_def] >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule sym_result_rel_terminal >> strip_tac >>
  metis_tac[sym_terminal_not_bad]
QED

(* ===== The optimizer, from its rules ===== *)

Theorem optimize_round_refines:
  (∀p. asm_refines p (FST (prune_unreachable_code p))) ∧
  (∀p. asm_refines p (FST (merge_iszero p))) ∧
  (∀p. asm_refines p (FST (merge_jumpdests p))) ∧
  (∀p. asm_refines p (FST (prune_inefficient_jumps p))) ∧
  (∀p. asm_refines p (FST (optimize_inefficient_jumps p))) ∧
  (∀p. asm_refines p (FST (prune_unused_jumpdests p))) ∧
  (∀p p' c. stack_peephole_opts p = SOME (p', c) ⇒ asm_refines p p') ⇒
  ∀p p' c. optimize_round p = SOME (p', c) ⇒ asm_refines p p'
Proof
  rw[optimize_round_def] >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[asm_refines_trans, pairTheory.FST]
QED

Theorem optimize_assembly_rounds_refines:
  (∀p p' c. optimize_round p = SOME (p', c) ⇒ asm_refines p p') ⇒
  ∀n p p'. optimize_assembly_rounds n p = SOME p' ⇒ asm_refines p p'
Proof
  strip_tac >> Induct >> simp[optimize_assembly_rounds_def] >>
  rpt gen_tac >> CASE_TAC >> PairCases_on `x` >> rw[] >>
  metis_tac[asm_refines_trans]
QED

Theorem asm_opt_finalizer_correct:
  (∀p. asm_refines p (FST (prune_unreachable_code p))) ∧
  (∀p. asm_refines p (FST (merge_iszero p))) ∧
  (∀p. asm_refines p (FST (merge_jumpdests p))) ∧
  (∀p. asm_refines p (FST (prune_inefficient_jumps p))) ∧
  (∀p. asm_refines p (FST (optimize_inefficient_jumps p))) ∧
  (∀p. asm_refines p (FST (prune_unused_jumpdests p))) ∧
  (∀p p' c. stack_peephole_opts p = SOME (p', c) ⇒ asm_refines p p') ⇒
  finalizer_correct asm_opt_finalizer
Proof
  strip_tac >> mp_tac optimize_round_refines >> impl_tac >- simp[] >>
  strip_tac >>
  drule optimize_assembly_rounds_refines >> strip_tac >>
  rw[finalizer_correct_def, asm_opt_finalizer_def, optimize_assembly_def] >>
  Cases_on `rp.rpol_final_assembly = FAP_Optimize` >>
  gvs[asm_refines_refl] >> metis_tac[]
QED

(* Every accepted finalizer is correct, given the optimizer's rules. *)
Theorem accepted_finalizers_correct:
  (∀p. asm_refines p (FST (prune_unreachable_code p))) ∧
  (∀p. asm_refines p (FST (merge_iszero p))) ∧
  (∀p. asm_refines p (FST (merge_jumpdests p))) ∧
  (∀p. asm_refines p (FST (prune_inefficient_jumps p))) ∧
  (∀p. asm_refines p (FST (optimize_inefficient_jumps p))) ∧
  (∀p. asm_refines p (FST (prune_unused_jumpdests p))) ∧
  (∀p p' c. stack_peephole_opts p = SOME (p', c) ⇒ asm_refines p p') ⇒
  ∀f. f ∈ accepted_finalizers ⇒ finalizer_correct f
Proof
  strip_tac >> mp_tac asm_opt_finalizer_correct >> impl_tac >- simp[] >>
  rw[accepted_finalizers_def] >> simp[finalizer_correct_identity]
QED
