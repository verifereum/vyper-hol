(*
 * Common Subexpression Elimination — Single-Pass Correctness Proof
 *
 * Proves cse_single_pass_correct via prefix execution simulation
 * (cse_prefix_simulation_entry in cseHistoryPropsTheory):
 *   1. Each replaced instruction in a reachable block has an available source
 *      birth in the execution prefix (cse_prefix_source_interval) with
 *      root-effect-free suffix survival.
 *   2. Transitive compute_canon equivalence + cse_reachable_wf_ssa align
 *      operand evaluation between source input state u and consumer input
 *      state s (across arbitrary loops and ASSIGN chains), and for commutative
 *      binary opcodes align operands up to transposition.
 *   3. 1-output replacements (mk_assign_inst) copy the preserved source output
 *      binding; 0-output idempotent replacements (mk_nop_inst) leave the state
 *      unchanged because their effects were already established by the source.
 *)

Theory cseProofs
Ancestors
  cseDefs cseCanonProps cseHistoryProps cseBlockSimulationProps
  availExprDefs availExprProofs
  passSharedDefs passSharedProps passSimulationProps
  venomInstProps venomWf venomWfProps

Theorem cse_single_pass_correct:
  !fuel ctx fn s.
    wf_function fn /\ cse_reachable_wf_ssa fn /\ fn_inst_wf fn /\
    EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
    s.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s.vs_current_bb ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (cse_single_pass fn) s)
Proof
  rpt strip_tac >> simp[cse_single_pass_def] >>
  irule cse_prefix_simulation_entry >>
  simp[stateEquivPropsTheory.state_equiv_refl] >>
  qexists_tac `cse_block_transform
    (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
    (dfg_build_function fn) (avail_analyze fn)` >>
  simp[cse_block_lookup, cse_block_phi, stateEquivPropsTheory.state_equiv_refl] >>
  rpt conj_tac
  >- metis_tac[cse_block_instruction]
  >- (rpt strip_tac >> irule cse_prefix_block_replacement >> metis_tac[]) >>
  rpt strip_tac >>
  imp_res_tac stateEquivPropsTheory.state_equiv_empty_eq >>
  gvs[cse_block_phi] >> metis_tac[stateEquivPropsTheory.state_equiv_refl]
QED
