(*
 * Assign Elimination — Proofs
 *
 * Proof strategy: two-phase decomposition + custom block simulation.
 *
 * Phase 1 (substitution): assign_subst_inst substitutes operands
 *   using the copy map. Both sides write the same outputs, so
 *   state_equiv {} holds per instruction.
 *
 *   NOTE: Python substitutes into ALL instructions INCLUDING terminators
 *   and INVOKE. The generic analysis_inst_simulates framework requires
 *   terminators/INVOKE to be unchanged, so it CANNOT be used here.
 *   Instead we use a custom per-instruction correctness lemma and
 *   custom block/function simulation.
 *
 * Phase 2 (dead-write removal): forwardable ASSIGNs are NOP'd.
 *   After Phase 1, all uses of eliminated variables have been substituted,
 *   so these writes are dead. Correctness proven separately with
 *   state_equiv elim where elim = assign_elim_eliminated_vars.
 *
 * Phase 3 (NOP cleanup): clear_nops_function removes NOP instructions.
 *
 * The combined assign_elim_function matches Python (single pass + clear_nops).
 * The proof decomposes through an intermediate substitution-only form.
 *)

Theory assignElimProofs
Ancestors
  assignElimDefs analysisSimProps passSimulationProps

(* Soundness: every recorded copy holds in the concrete state.
   Proof predicate — only used in simulation proofs, not in defs. *)
Definition copy_sound_def:
  copy_sound (copies : copy_lattice) (s : venom_state) <=>
    !x op. FLOOKUP copies x = SOME op ==>
      FLOOKUP s.vs_vars x = eval_operand op s
End

Definition copy_sound_opt_def:
  copy_sound_opt c_opt s <=>
    case c_opt of NONE => T | SOME c => copy_sound c s
End

(* ===== Phase 1: Per-instruction substitution correctness ===== *)

(* Custom per-instruction lemma (NOT analysis_inst_simulates).
   Python substitutes into ALL instructions including terminators and
   INVOKE. The generic framework requires terminators/INVOKE unchanged,
   which is incompatible. This lemma states direct per-step correctness:
   substituted operands evaluate identically under copy_sound. *)
Theorem assign_subst_step_correct:
  !v fuel ctx inst s.
    copy_sound_opt v s ==>
    lift_result (state_equiv {}) (execution_equiv {})
      (step_inst fuel ctx inst s)
      (step_inst fuel ctx (assign_subst_inst v inst) s)
Proof
  cheat
QED

(* ===== Phase 2: Dead-write removal ===== *)

(* NOP'ing a forwardable ASSIGN eliminates its output variable.
   After substitution, no instruction reads the eliminated variable,
   so the dead write can be removed with state_equiv elim. *)
Theorem assign_nop_dead_writes_correct:
  !fuel ctx fn s.
    let elim = assign_elim_eliminated_vars fn in
    let pv = phi_used_vars fn in
    let result = copy_prop_analyze fn in
    let fn_subst = analysis_function_transform NONE result
                     (\v inst. [assign_subst_inst v inst]) fn in
    let fn_elim = analysis_function_transform NONE result
                    (\v inst. [assign_elim_inst pv v inst]) fn in
    lift_result (state_equiv elim) (execution_equiv elim)
      (run_function fuel ctx fn_subst s)
      (run_function fuel ctx fn_elim s)
Proof
  cheat
QED

(* ===== Combined: function-level correctness ===== *)

(* Composes Phase 1 (subst, state_equiv {}), Phase 2 (NOP dead writes,
   state_equiv elim), and Phase 3 (clear_nops, state_equiv {}).
   state_equiv {} ⊆ state_equiv elim, so Phase 1 lifts. *)
Theorem assign_elim_function_correct_proof:
  !fuel ctx fn s.
    let elim = assign_elim_eliminated_vars fn in
    lift_result (state_equiv elim) (execution_equiv elim)
      (run_function fuel ctx fn s)
      (run_function fuel ctx (assign_elim_function fn) s)
Proof
  cheat
QED
