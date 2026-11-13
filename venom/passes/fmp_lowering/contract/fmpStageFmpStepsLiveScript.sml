(*
 * FmpLowering's runner is never live in the source: the lowering takes it
 * fresh from a supply covering every variable the function names, and
 * liveness only reports variables the function names.
 *
 * TOP-LEVEL:
 *   fmp_live_ir_vars          - a live variable is one the function names
 *   fmp_stage_runner_fresh    - the runner is not one the function names
 *   fmp_stage_runner_not_live - the runner is live nowhere in the source
 *)
Theory fmpStageFmpStepsLive
Ancestors
  fmpStageRel fmpStepSupply livenessTerminationProofs livenessInvariantProofs
  livenessDefs venomInst list

Theorem fmp_live_ir_vars:
  MEM v (live_vars_at (liveness_analyze fn) lbl i) ==> MEM v (fn_ir_vars fn)
Proof
  strip_tac >>
  `lv_bounded fn.fn_blocks (liveness_analyze fn)` by
    metis_tac[liveness_recompute_invariant, lv_inv_def, liveness_analyze_def] >>
  `MEM v (livenessDefs$fn_all_vars fn.fn_blocks)` by
    metis_tac[lv_bounded_read, live_vars_at_def] >>
  gvs[livenessDefsTheory.fn_all_vars_def, MEM_FLAT, MEM_MAP,
      fn_ir_vars_member, inst_defs_def] >> metis_tac[]
QED

Theorem fmp_stage_runner_fresh:
  fmp_stage_lowered infos ctx runner fn fn' ==> ~MEM runner (fn_ir_vars fn)
Proof
  strip_tac >> gvs[fmp_stage_lowered_def] >>
  Cases_on `fresh_ir_var sp` >> gvs[] >>
  drule irSupplyTheory.fresh_ir_var_contract >>
  gvs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
      venomFnScheduleRunnerTheory.list_subset_def, EVERY_MEM] >> metis_tac[]
QED

Theorem fmp_stage_runner_not_live:
  fmp_stage_lowered infos ctx runner fn fn' ==>
  ~MEM runner (live_vars_at (liveness_analyze fn) lbl idx)
Proof
  metis_tac[fmp_stage_runner_fresh, fmp_live_ir_vars]
QED
