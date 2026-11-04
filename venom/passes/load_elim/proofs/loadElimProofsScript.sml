(*
 * Load Elimination — Proofs
 *
 * The pass replaces eliminated loads by ASSIGNs and inserts PHIs whose
 * outputs are "$le_phi_<load id>"; the premise that no variable of fn
 * has that prefix makes them fresh, so the results agree outside those
 * variables.  The premise set is copy_elision_function_correct's (the
 * pass uses the same base-pointer analysis bp_analyze (cfg_analyze fn) fn).
 *
 * Notes for the proof:
 * - load_elim_function computes cfg and bp once on fn but rebuilds the
 *   dfg before each round, so rounds 2-5 see the ASSIGNs and PHIs of
 *   earlier rounds; dfg_assigns_sound and bp_assigns_stable for those
 *   dfgs must be re-established (TLOAD/SLOAD/DLOAD/CALLDATALOAD results
 *   are never pointers in bp).
 * - The five rounds target disjoint load opcodes, so each load is
 *   rewritten in at most one round.
 * - A start state in the middle of fn, or bp not from bp_analyze, or a
 *   non-SSA fn, each make the old statement false (counterexamples in
 *   the PR that introduced this statement).
 *)

Theory loadElimProofs
Ancestors
  loadElimDefs analysisSimProps passSimulationProps
  basePtrProps venomWf venomInst venomMemDefs venomExecSemantics
  cfgTransform dfgCorrectnessProof memoryCopyElisionSound stateEquiv

Theorem load_elim_function_correct_proof:
  !fuel ctx fn s.
    wf_function fn /\
    fn_inst_wf fn /\
    wf_ssa fn /\
    EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    dfg_assigns_sound (dfg_build_function fn) s /\
    bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s /\
    alloca_inv s /\
    allocas_in_word s /\
    bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s /\
    bp_phis_closed (bp_analyze (cfg_analyze fn) fn) fn /\
    bp_assigns_stable (bp_analyze (cfg_analyze fn) fn) (dfg_build_function fn) /\
    (!bb s0 s_phi.
       MEM bb fn.fn_blocks /\
       MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
       eval_phis s0 bb.bb_instructions = OK s_phi /\
       dfg_assigns_sound (dfg_build_function fn) s0 ==>
       dfg_assigns_sound (dfg_build_function fn) s_phi) /\
    (!fuel' run_ctx bb inst s0 s1.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       inst_wf inst /\
       dfg_assigns_sound (dfg_build_function fn) (s0 with vs_inst_idx := 0) /\
       bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) (s0 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s0 with vs_inst_idx := 0) /\
       allocas_in_word (s0 with vs_inst_idx := 0) /\
       bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn (s0 with vs_inst_idx := 0) /\
       step_inst fuel' run_ctx inst s0 = OK s1 ==>
       dfg_assigns_sound (dfg_build_function fn) (s1 with vs_inst_idx := 0) /\
       bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) (s1 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s1 with vs_inst_idx := 0) /\
       allocas_in_word (s1 with vs_inst_idx := 0) /\
       bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn (s1 with vs_inst_idx := 0)) /\
    LENGTH s.vs_memory < dimword (:256) ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {v | isPREFIX "$le_phi_" v})
      (execution_equiv {v | isPREFIX "$le_phi_" v})
      (execution_equiv {v | isPREFIX "$le_phi_" v})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (load_elim_function fn) s)
Proof
  cheat
QED
