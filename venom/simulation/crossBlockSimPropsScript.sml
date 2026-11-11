(*
 * Cross-Block Simulation — Lifting Theorem
 *
 * Per-block resolving_block_sim lifts to function-level pass_correct.
 *
 * TOP-LEVEL:
 *   resolving_block_sim_function — per-block sim ⟹ fn-level termination equiv + lift_result
 *                                  (in proofs/crossBlockSimProofsScript.sml)
 *   resolves_to_lift_result      — lift_result implies resolves_to 0
 *   run_blocks_deterministic     — terminating runs at different fuels give identical results
 *
 * resolves_to_mono and run_blocks_fuel_mono are in proofs/crossBlockSimProofsScript.sml.
 *)

Theory crossBlockSimProps
Ancestors
  crossBlockSimDefs crossBlockSimProofs passSimulationDefs execEquivParamDefs
  stateEquiv stateEquivProps execEquivProps venomExecProps

(* ===== Basic properties ===== *)

(* lift_result is resolves_to at n=0 *)
Theorem resolves_to_lift_result:
  !R_ok R_term bbs1 bbs2 r1 r2.
    lift_result R_ok R_term R_term r1 r2 ==>
    resolves_to R_ok R_term bbs1 bbs2 0 r1 r2
Proof
  simp[resolves_to_def]
QED

(* ===== Determinism ===== *)

(* Determinism: if a run_blocks call terminates at two different fuel
   values, the results are identical. Corollary of fuel monotonicity. *)
Theorem run_blocks_deterministic:
  !fuel fuel' ctx fn s.
    terminates (run_blocks fuel ctx fn s) /\
    terminates (run_blocks fuel' ctx fn s) ==>
    run_blocks fuel ctx fn s = run_blocks fuel' ctx fn s
Proof
  rpt strip_tac >>
  Cases_on `fuel <= fuel'`
  >- (
    `?k. fuel' = fuel + k` by (qexists_tac `fuel' - fuel` >> simp[]) >>
    metis_tac[run_blocks_fuel_mono]
  ) >>
  `?k. fuel = fuel' + k` by (qexists_tac `fuel - fuel'` >> simp[]) >>
  metis_tac[run_blocks_fuel_mono]
QED
