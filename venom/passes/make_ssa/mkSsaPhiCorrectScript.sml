(*
 * SSA Construction: PHI Insertion + Correctness Wrapper
 *
 * This theory ties together CFG/dominance/PHI placement and
 * exposes a concrete make_ssa definition. Correctness is stated
 * in terms of the existing valid_ssa_transform framework.
 *)

Theory mkSsaPhiCorrect
Ancestors
  mkSsaPhiPlace mkSsaFunction mkSsaStateEquiv mkSsaWellFormed
  phiWellFormed venomSem list pred_set

(* ===== Full make_ssa Transformation (PHI insertion only) ===== *)

Definition make_ssa_def:
  make_ssa live_in fn =
    let preds = compute_preds fn.fn_blocks in
    let entry =
      case fn.fn_blocks of
        [] => ""
      | bb::bbs => bb.bb_label in
    let all_labels = set (MAP (λbb. bb.bb_label) fn.fn_blocks) in
    let doms = compute_dominators preds entry all_labels in
    let idoms = compute_idom doms entry all_labels in
    let df = compute_df preds idoms all_labels in
    let def_sites = compute_def_sites fn.fn_blocks in
    let phi_sites = compute_all_phi_sites df def_sites in
    let (fn_phis, _) = insert_phis phi_sites preds live_in fn 0 in
    fn_phis
End

(* ===== Correctness (via valid_ssa_transform) ===== *)

Theorem step_inst_inserted_phi_identity:
  !preds var id s prev v.
    s.vs_prev_bb = SOME prev /\
    MEM prev preds /\
    lookup_var var s = SOME v ==>
    step_inst (mk_phi_inst id var preds var) s =
      OK (update_var var v s)
Proof
  rpt strip_tac >>
  simp[step_inst_def, mk_phi_inst_def, resolve_phi_mk_phi_operands,
       eval_operand_def, lookup_var_def]
QED

Theorem make_ssa_correct:
  !fuel fn fn_ssa vm s_orig s_ssa result live_in.
    fn_ssa = make_ssa live_in fn /\
    valid_ssa_transform fn fn_ssa vm /\
    ssa_state_equiv vm s_orig s_ssa /\
    run_function fuel fn s_orig = result ==>
    ?result_ssa.
      run_function fuel fn_ssa s_ssa = result_ssa /\
      ssa_result_equiv vm result result_ssa
Proof
  rpt strip_tac >>
  irule ssa_construction_correct >>
  qexistsl_tac [`fn`, `s_orig`] >>
  simp[]
QED

(* ===== wf_ir_fn Connection (phi_elimination) ===== *)

Theorem make_ssa_wf_ir:
  !fn fn_ssa live_in.
    fn_ssa = make_ssa live_in fn /\
    ssa_form fn_ssa /\
    (!bb idx inst.
       MEM bb fn_ssa.fn_blocks /\
       get_instruction bb idx = SOME inst /\
       is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (!bb idx inst.
       MEM bb fn_ssa.fn_blocks /\
       get_instruction bb idx = SOME inst /\
       is_phi_inst inst ==>
       ?out. inst.inst_outputs = [out]) /\
    (fn_ssa.fn_blocks <> [] ==>
       !idx inst.
         get_instruction (HD fn_ssa.fn_blocks) idx = SOME inst ==>
         ~is_phi_inst inst) /\
    (!bb idx inst.
       let dfg = build_dfg_fn fn_ssa in
       MEM bb fn_ssa.fn_blocks /\
       get_instruction bb idx = SOME inst /\
       is_phi_inst inst ==>
       phi_operands_direct dfg inst) /\
    (!bb idx inst prev s e.
       MEM bb fn_ssa.fn_blocks /\
       get_instruction bb idx = SOME inst /\
       is_phi_inst inst /\
       s.vs_prev_bb = SOME prev /\
       step_inst inst s = Error e ==>
       ?val_op. resolve_phi prev inst.inst_operands = SOME val_op)
  ==>
    wf_ir_fn fn_ssa
Proof
  rw[wf_ir_fn_def, LET_DEF]
QED
