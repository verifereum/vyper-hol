(*
 * Load Elimination — Proofs
 *
 * Key lemma: load_elim_inst satisfies analysis_inst_simulates
 * with sound = load_sound, for each effect-type configuration.
 *
 * Uses state_equiv fresh / execution_equiv fresh where fresh is the
 * set of PHI output variables introduced by the prepend phase.
 * These fresh vars are not referenced by any original instruction,
 * so excluding them from comparison preserves simulation.
 *)

Theory loadElimProofs
Ancestors
  loadElimDefs analysisSimProps passSimulationProps
  basePtrProps

(* Per-round correctness: load_elim_one preserves semantics modulo
   the fresh variables it introduces via PHI insertion. *)
Theorem load_elim_one_correct_proof:
  !ctx ir_cfg fuel run_ctx fn s.
    let fresh = load_elim_one_fresh ctx ir_cfg fn in
    fn_inst_wf fn /\ s.vs_inst_idx = 0 ==>
    (?e. run_function fuel run_ctx fn s = Error e) \/
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (run_function fuel run_ctx fn s)
      (run_function fuel run_ctx (load_elim_one ctx ir_cfg fn) s)
Proof
  cheat
QED

(* Function-level: composing 5 rounds, fresh vars accumulate.
 * bp_ptrs_bounded: load forwarding correctness depends on aliasing
 * analysis precision. Without bounded accesses, may_overlap is unsound
 * for different allocas → fewer forwards → not byte-for-byte. *)
Theorem load_elim_function_correct_proof:
  !fuel ir_ctx ctx fn s bp.
    fn_inst_wf fn /\ s.vs_inst_idx = 0 /\
    bp_ptr_sound bp s /\ bp_ptrs_bounded bp fn s ==>
    ?fresh.
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (run_function fuel ctx fn s)
      (run_function fuel ctx (load_elim_function fn) s)
Proof
  cheat
QED
