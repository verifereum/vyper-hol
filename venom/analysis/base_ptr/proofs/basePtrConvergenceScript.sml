(*
 * Base Pointer Analysis — Convergence
 *
 * bp_analyze iterates bp_one_pass from FEMPTY with df_iterate (WHILE).
 * WHILE only satisfies its recursion equation, so nothing is known about
 * bp_analyze unless the iteration reaches a fixpoint.  Under SSA it does.
 *
 * TOP-LEVEL:
 *   bp_analyze_terminates — under ssa_form, bp_analyze is reached after
 *                           finitely many passes and is a fixpoint
 *   bp_analyze_fixpoint   — one more pass leaves bp_analyze unchanged
 *   bp_analyze_invariant  — a property of FEMPTY preserved by every pass
 *                           holds of bp_analyze
 *
 * Without SSA the iteration can diverge: in a block
 *   y = ALLOCA 32; y = ADD x 1; x = ASSIGN y
 * x's offset grows by one on every pass.
 *
 * Intuition (the prover may ignore it): under SSA every variable has one
 * writer.  Along the iteration from FEMPTY each variable's pointer list only
 * grows: its allocations are extended (PHI unions with the recorded set and
 * normalises; ADD/SUB/ASSIGN map their operands' lists, which only grow) and
 * an offset only changes from SOME n to NONE (bp_normalize merges differing
 * offsets of one allocation into NONE).  Allocations are ALLOCA inst_ids of
 * fn and tracked variables are outputs of fn's instructions, so a measure
 * such as the sum over tracked variables of (1 + list length + #NONE
 * offsets) is bounded and strictly increases on every changing pass.  The
 * ADD/SUB Var-Var case keeps the old value when both operands are tracked,
 * and the flips between its branches start from an untracked output.
 *)

Theory basePtrConvergence
Ancestors
  basePtrConvergenceOrbit basePtrDefs dfIterateDefs dfIterateProofs venomWf venomInst
  finite_map list arithmetic

Theorem bp_analyze_terminates:
  !cfg fn.
    ssa_form fn ==>
    ?n. bp_analyze cfg fn =
          FUNPOW (\r. SND (bp_one_pass fn cfg.cfg_dfs_pre r)) n FEMPTY /\
        SND (bp_one_pass fn cfg.cfg_dfs_pre (bp_analyze cfg fn)) =
          bp_analyze cfg fn
Proof
  rpt strip_tac >> simp[bp_analyze_def] >>
  metis_tac[bp_pass_iterate_orbit, bp_pass_iterate_fixpoint]
QED

Theorem bp_analyze_fixpoint:
  !cfg fn.
    ssa_form fn ==>
    SND (bp_one_pass fn cfg.cfg_dfs_pre (bp_analyze cfg fn)) =
      bp_analyze cfg fn
Proof
  metis_tac[bp_analyze_terminates]
QED

Theorem bp_analyze_invariant:
  !cfg fn P.
    ssa_form fn /\ P FEMPTY /\
    (!r. P r ==> P (SND (bp_one_pass fn cfg.cfg_dfs_pre r))) ==>
    P (bp_analyze cfg fn)
Proof
  rpt strip_tac >> drule bp_analyze_terminates >> strip_tac >>
  `!n. P (FUNPOW (\r. SND (bp_one_pass fn cfg.cfg_dfs_pre r)) n FEMPTY)` by
    (Induct >> simp[FUNPOW_SUC]) >>
  metis_tac[]
QED
