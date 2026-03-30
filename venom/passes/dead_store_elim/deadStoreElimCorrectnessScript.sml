(*
 * Dead Store Elimination — Correctness Statement
 *
 * If analysis_fn correctly identifies dead stores (output unused,
 * no non-related effects, no aliasing read reachable without
 * intervening clobber), then NOP'ing those stores preserves
 * observable semantics.
 *
 * Uses dse_all_equiv: variables, logs, return data, halt status,
 * and context fields all match. Memory, transient storage, and
 * account storage (vs_accounts) may differ at eliminated locations.
 *
 * This is sound because dead stores are never read:
 * - memSSA treats RETURN/REVERT/LOG/SHA3 as memory reads
 * - stores to the return data region are "live" (not eliminated)
 * - eliminated locations are by definition unobserved
 *)

Theory deadStoreElimCorrectness
Ancestors
  deadStoreElimProofs venomWf basePtrProps

Theorem dse_function_correct:
  !analysis_fn aliases fuel ctx fn s bp.
    bp_ptr_sound bp s /\ bp_ptrs_bounded bp s /\
    (!space fn'.
      all_dead_stores (analysis_fn space fn')
        (cfg_analyze fn') aliases (bp_analyze (cfg_analyze fn') fn')
        space fn') ==>
    lift_result dse_all_equiv dse_all_equiv
      (run_function fuel ctx fn s)
      (run_function fuel ctx (dse_function analysis_fn fn) s)
Proof
  ACCEPT_TAC dse_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem dse_preserves_ssa_form:
  ∀analysis_fn fn. ssa_form fn ⇒ ssa_form (dse_function analysis_fn fn)
Proof
  cheat
QED

Theorem dse_preserves_wf_function:
  ∀analysis_fn fn. wf_function fn ⇒ wf_function (dse_function analysis_fn fn)
Proof
  cheat
QED
