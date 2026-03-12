(*
 * Dead Store Elimination — Proofs
 *
 * Key lemma: NOP'ing a dead store preserves semantics because
 * the stored value is never read before being overwritten.
 *
 * Uses dse_equiv / dse_all_equiv instead of execution_equiv because
 * DSE may leave different values in the eliminated address space.
 *)

Theory deadStoreElimProofs
Ancestors
  deadStoreElimDefs passSimulationProps

(* Per-space: DSE preserves semantics modulo the target space *)
Theorem dse_function_space_correct_proof:
  !analysis_fn cfg aliases bp space fuel ctx fn s.
    (!fn'. all_dead_stores (analysis_fn space fn')
             (cfg_analyze fn') aliases (bp_analyze ctx (cfg_analyze fn') fn')
             space fn') ==>
    lift_result (dse_equiv space) (dse_equiv space)
      (run_function fuel ctx fn s)
      (run_function fuel ctx (dse_function_space analysis_fn space fn) s)
Proof
  cheat
QED

(* Combined: after all 3 spaces, use dse_all_equiv *)
Theorem dse_function_correct_proof:
  !analysis_fn aliases fuel ctx fn s.
    (!space fn'.
      all_dead_stores (analysis_fn space fn')
        (cfg_analyze fn') aliases (bp_analyze ctx (cfg_analyze fn') fn')
        space fn') ==>
    lift_result dse_all_equiv dse_all_equiv
      (run_function fuel ctx fn s)
      (run_function fuel ctx (dse_function analysis_fn fn) s)
Proof
  cheat
QED
