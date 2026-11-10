(*
 * Load Elimination — Correctness Statement
 *
 * Results agree outside the PHI outputs "$le_phi_<id>" the pass adds,
 * with memory compared up to trailing zero bytes, under
 * copy_elision_function_correct's premises plus freshness of that prefix
 * and no MEMTOP in fn or the functions it can call.
 *)

Theory loadElimCorrectness
Ancestors
  loadElimProofs loadElimWf
  loadElimDefs analysisSimProps passSimulationProps
  basePtrProps venomWf venomInst venomMemDefs venomExecSemantics
  cfgTransform dfgCorrectnessProof memoryCopyElisionSound stateEquiv

Theorem load_elim_function_correct:
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
  ACCEPT_TAC load_elim_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem load_elim_preserves_ssa_form:
  !fn. wf_function fn /\ ssa_form fn /\
       EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) ==>
       ssa_form (load_elim_function fn)
Proof
  ACCEPT_TAC load_elim_function_preserves_ssa
QED

Theorem load_elim_preserves_wf_function:
  !fn. wf_function fn ==> wf_function (load_elim_function fn)
Proof
  ACCEPT_TAC load_elim_function_preserves_wf
QED
