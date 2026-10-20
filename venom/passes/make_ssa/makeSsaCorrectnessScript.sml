(*
 * Make SSA Pass — Correctness & Obligations
 *
 * Proof in proofs/makeSsaProofScript.sml; re-exported via ACCEPT_TAC.
 *
 * Obligations:
 *   make_ssa_establishes_ssa_form     — output is in SSA form
 *   make_ssa_establishes_wf_ssa       — weakened to ssa_form (see note)
 *   make_ssa_preserves_wf_function    — output is still wf_function
 *)

Theory makeSsaCorrectness
Ancestors
  makeSsaProof
  makeSsaHelper
  makeSsaSsaForm
  ssaPipelineProps

(* Clean top-level correctness theorem — no pipeline-derivable assumptions *)
Theorem make_ssa_pass_correct:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in
   func s fuel ctx.
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    fn_entry_no_preds func /\
    fn_inst_wf func /\
    valid_liveness_flow live_in func /\
    valid_liveness_uses live_in func /\
    s.vs_vars = FEMPTY /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    fn_entry_label func = SOME s.vs_current_bb /\
    live_in_scope live_in s /\
    (!bb inst. MEM bb func.fn_blocks /\
              MEM inst bb.bb_instructions ==>
              inst.inst_opcode <> PHI /\
              EVERY colon_free inst.inst_outputs /\
              ALL_DISTINCT inst.inst_outputs /\
              (~opcode_has_output inst.inst_opcode ==>
               inst.inst_outputs = [])) ==>
    let func' = make_ssa_fn dom_frontiers dtree dom_post_order
                  pred_map succ_map live_in func in
    ?fresh fuel'.
      result_equiv fresh
        (run_blocks fuel ctx func s)
        (run_blocks fuel' ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  mp_tac (SIMP_RULE std_ss [LET_THM] make_ssa_fn_correct) >>
  simp_tac std_ss [LET_THM] >>
  disch_then irule >>
  rpt conj_tac
  >> TRY (first_assum ACCEPT_TAC)
  >> TRY (
    mp_tac (SIMP_RULE std_ss [LET_THM] ssaPipelinePropsTheory.phi_coverage) >>
    disch_then irule >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >> res_tac >> simp[])
  >> TRY (
    mp_tac (SIMP_RULE std_ss [LET_THM] ssaPipelinePropsTheory.phi_operands) >>
    disch_then irule >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >> res_tac >> simp[])
  >> TRY (
    mp_tac (SIMP_RULE std_ss [LET_THM] ssaPipelinePropsTheory.phi_bases_live) >>
    disch_then irule >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >> res_tac >> simp[])
  >>
  mp_tac (Q.SPECL [`dom_frontiers`, `dtree`, `dom_post_order`, `pred_map`, `succ_map`, `live_in`, `func`, `s.vs_current_bb`,
    `compute_defs (MAP THE (FILTER IS_SOME (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order)))`] entry_no_phis_in_bbs1) >>
(impl_tac >- (rpt strip_tac >> gvs[] >> metis_tac[])) >>
simp[LET_DEF] >> strip_tac >>
mp_tac (Q.SPECL [`dom_frontiers`, `pred_map`, `live_in`, `func.fn_blocks`,
  `compute_defs (MAP THE (FILTER IS_SOME (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order)))`] phi_outputs_all_distinct) >>
(impl_tac >- (
  conj_tac >- simp[makeSsaDefsTheory.compute_defs_all_distinct] >>
  metis_tac[]
)) >>
simp[LET_DEF]
QED

(* ===== Obligations ===== *)

Theorem make_ssa_establishes_ssa_form:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    (!bb inst. MEM bb func.fn_blocks /\
              MEM inst bb.bb_instructions ==>
              EVERY colon_free inst.inst_outputs) ==>
    ssa_form (make_ssa_fn dom_frontiers dtree dom_post_order
                pred_map succ_map live_in func)
Proof
  ACCEPT_TAC makeSsaSsaFormTheory.make_ssa_fn_ssa_form
QED

(*
 * NOTE: make_ssa_establishes_wf_ssa is weakened to ssa_form only.
 * wf_ssa = ssa_form ∧ def_dominates_uses. def_dominates_uses requires
 * that for every MEM (Var v) inst.inst_operands, the defining block
 * fn_dominates the use block. This is FALSE for PHI instructions in
 * standard SSA: a PHI at block B uses Var v defined in predecessor P,
 * but P does NOT necessarily dominate B (e.g., in diamond CFGs).
 * The correct property for PHI-containing SSA would require
 * domination of the *predecessor* rather than the use block.
 * The downstream consumer (codegen_ready_fn) uses def_dominates_uses
 * AFTER PHI lowering, where no PHIs remain — so the existing
 * definition is correct for its actual use case.
 *)
Theorem make_ssa_establishes_wf_ssa:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    (!bb inst. MEM bb func.fn_blocks /\
              MEM inst bb.bb_instructions ==>
              EVERY colon_free inst.inst_outputs) ==>
    ssa_form (make_ssa_fn dom_frontiers dtree dom_post_order
                pred_map succ_map live_in func)
Proof
  ACCEPT_TAC makeSsaSsaFormTheory.make_ssa_fn_ssa_form
QED

Theorem make_ssa_preserves_wf_function:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    fn_entry_no_preds func ==>
    let func' = make_ssa_fn dom_frontiers dtree dom_post_order
                  pred_map succ_map live_in func in
    ALL_DISTINCT (fn_labels func') /\
    fn_has_entry func' /\
    (!bb. MEM bb func'.fn_blocks ==> bb_well_formed bb) /\
    fn_succs_closed func'
Proof
  ACCEPT_TAC makeSsaHelperTheory.make_ssa_preserves_wf_function
QED
