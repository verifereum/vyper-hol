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
 *   non-SSA fn, each make the old statement false; so does exact memory
 *   comparison (mload 0; mstore 0 x: the store is dropped, and only it
 *   grew memory).  Counterexamples in the PR that introduced this.
 *)

Theory loadElimProofs
Ancestors
  loadElimDefs analysisSimProps passSimulationProps
  basePtrProps venomWf venomInst venomMemDefs venomExecSemantics
  cfgTransform dfgCorrectnessProof memoryCopyElisionSound stateEquiv
  stateFrame loadElimFinalIntegration loadElimFiveRoundExecution
  loadElimRoundExecution loadElimIterationReadiness loadElimKeyShapeInvariant
  loadElimMemoryRel loadElimPaddedNoncall loadElimBPEmpty
  loadElimSentinelHelpers loadElimReachableSSA

(* Result relations for load elimination.  A redundant store the pass
   removes may be the one that grew memory (Venom's mload doesn't grow
   it), so memory is compared byte-wise with zero padding, i.e. up to
   trailing zero bytes; everything else as state_equiv/execution_equiv.
   MEMTOP, the only observer of memory length, is excluded by premise:
   the pinned compiler rejects it and lowering never emits it. *)
Definition le_exec_equiv_def:
  le_exec_equiv vars s1 s2 <=>
    (!v. v NOTIN vars ==> lookup_var v s1 = lookup_var v s2) /\
    (!i. read_memory i 1 s1 = read_memory i 1 s2) /\
    execution_frame (s1 with vs_memory := []) =
    execution_frame (s2 with vs_memory := [])
End

Definition le_state_equiv_def:
  le_state_equiv vars s1 s2 <=>
    le_exec_equiv vars s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb
End

Theorem le_exec_equiv_padded:
  le_exec_equiv vars = padded_exec_equiv vars
Proof
  simp[FUN_EQ_THM, le_exec_equiv_def, padded_exec_equiv_def]
QED

Theorem le_state_equiv_padded:
  le_state_equiv vars = le_padded_control vars
Proof
  simp[FUN_EQ_THM, le_state_equiv_def, le_padded_control_def,
       le_exec_equiv_padded]
QED

Theorem load_elim_one_correct_proof:
  !ctx ir_cfg fuel run_ctx fn s.
    wf_function fn /\
    fn_inst_wf fn /\
    wf_ssa fn /\
    le_configured_context ctx /\
    ctx.lctx_dfg = dfg_build_function fn /\
    (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
    wf_alias_sets ctx.lctx_aliases /\
    ir_cfg = cfg_analyze fn /\
    DISJOINT (load_elim_one_fresh ctx ir_cfg fn) (set (fn_all_vars fn)) /\
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> MEMTOP) /\
    EVERY (\f. !inst. MEM inst (fn_insts f) ==> inst.inst_opcode <> MEMTOP)
      run_ctx.ctx_functions /\
    s.vs_inst_idx = 0 /\
    ~s.vs_call_ctx.cc_static /\
    fn_entry_label fn = SOME s.vs_current_bb ==>
    (?e. run_blocks fuel run_ctx fn s = Error e) \/
    lift_result
      (le_state_equiv (load_elim_one_fresh ctx ir_cfg fn))
      (le_exec_equiv (load_elim_one_fresh ctx ir_cfg fn))
      (le_exec_equiv (load_elim_one_fresh ctx ir_cfg fn))
      (run_blocks fuel run_ctx fn s)
      (run_blocks fuel run_ctx (load_elim_one ctx ir_cfg fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[le_state_equiv_padded, le_exec_equiv_padded] >>
  irule le_load_elim_one_run_structural >>
  gvs[listTheory.EVERY_MEM, le_wf_ssa_reachable,
      le_iteration_generated_output, le_padded_control_def,
      padded_exec_equiv_refl] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem load_elim_function_correct_proof:
  !fuel ctx fn s.
    wf_function fn /\
    fn_inst_wf fn /\
    wf_ssa fn /\
    EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> MEMTOP) /\
    EVERY (\f. !inst. MEM inst (fn_insts f) ==> inst.inst_opcode <> MEMTOP)
      ctx.ctx_functions /\
    s.vs_inst_idx = 0 /\
    ~s.vs_call_ctx.cc_static /\
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
    lift_result (le_state_equiv {v | isPREFIX "$le_phi_" v})
      (le_exec_equiv {v | isPREFIX "$le_phi_" v})
      (le_exec_equiv {v | isPREFIX "$le_phi_" v})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (load_elim_function fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  `le_step_preserves (bp_analyze (cfg_analyze fn) fn)
     (dfg_build_function fn) fn` by
    (pure_rewrite_tac[le_step_preserves_def, le_step_invariants_def] >>
     qpat_x_assum `!fuel' run_ctx bb inst s0 s1. _` mp_tac >>
     simp[] >> metis_tac[]) >>
  `!v. bp_get_ptrs (bp_analyze (cfg_analyze fn) fn) v = []` by
    (irule le_step_preserves_analyze_empty >> metis_tac[]) >>
  `le_prefix_run_sim fuel ctx s fn (load_elim_function fn)` by
    (irule le_function_padded_run >>
     gvs[listTheory.EVERY_MEM, le_wf_ssa_reachable, Excl "isPREFIX"] >>
     rpt strip_tac >> metis_tac[]) >>
  pure_rewrite_tac[le_state_equiv_padded, le_exec_equiv_padded] >>
  fs[le_prefix_run_sim_def]
QED
