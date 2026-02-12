(* 
 * Simplify-CFG PHI Step Correctness
 *
 * Instruction and block-step lemmas for simplify-phi.
 *)

Theory scfgPhiStep
Ancestors
  scfgPhiLemmas scfgEquiv venomSem venomSemProps
Libs
  scfgDefsTheory scfgEquivTheory scfgStateOpsTheory venomSemTheory
  venomInstTheory venomStateTheory listTheory

Theorem simplify_phi_inst_preserves_outputs:
  !preds inst.
    (simplify_phi_inst preds inst).inst_outputs =
    if inst.inst_opcode = PHI /\ NULL (phi_remove_non_preds preds inst.inst_operands) then []
    else inst.inst_outputs
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (
    simp[scfgDefsTheory.simplify_phi_inst_def] >>
    Cases_on `NULL (phi_remove_non_preds preds inst.inst_operands)` >>
    simp[scfgDefsTheory.simplify_phi_inst_def] >>
    Cases_on `LENGTH (phi_remove_non_preds preds inst.inst_operands) = 2` >>
    simp[scfgDefsTheory.simplify_phi_inst_def]
  )
  >- simp[scfgDefsTheory.simplify_phi_inst_def]
QED

Theorem step_inst_simplify_phi_inst:
  !preds preds0 prev inst s.
    inst.inst_opcode = PHI /\
    s.vs_prev_bb = SOME prev /\
    MEM prev preds /\
    (!lbl. MEM lbl preds ==> MEM lbl preds0) /\
    phi_inst_wf preds0 inst ==>
    result_equiv_cfg (step_inst (simplify_phi_inst preds inst) s) (step_inst inst s)
Proof
  rpt strip_tac >>
  `MEM prev preds0` by metis_tac[] >>
  qpat_x_assum `phi_inst_wf preds0 inst` mp_tac >>
  simp[scfgDefsTheory.phi_inst_wf_def] >> strip_tac >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `phi_ops_complete preds0 inst.inst_operands` mp_tac >>
  simp[scfgDefsTheory.phi_ops_complete_def] >> strip_tac >>
  first_x_assum (qspec_then `prev` mp_tac) >> simp[] >> strip_tac >>
  pop_assum strip_assume_tac >>
  `resolve_phi prev (phi_remove_non_preds preds inst.inst_operands) = SOME val_op` by
    (match_mp_tac resolve_phi_remove_non_preds_ok >> simp[phi_resolve_ok_def]) >>
  Cases_on `NULL (phi_remove_non_preds preds inst.inst_operands)`
  >- (Cases_on `phi_remove_non_preds preds inst.inst_operands` >> fs[venomSemTheory.resolve_phi_def])
  >- (
    Cases_on `LENGTH (phi_remove_non_preds preds inst.inst_operands) = 2`
    >- (
      fs[simplify_phi_inst_def, step_inst_def] >>
      Cases_on `phi_remove_non_preds preds inst.inst_operands` >> fs[] >>
      Cases_on `t` >> fs[] >>
      rename1 `h::h2::[]` >>
      Cases_on `h`
      >- fs[resolve_phi_def]
      >- fs[resolve_phi_def]
      >- (
        rename1 `Label lbl` >>
        fs[resolve_phi_def] >>
        Cases_on `lbl = prev`
        >- (
          fs[resolve_phi_def] >>
          Cases_on `eval_operand val_op s` >>
          simp[result_equiv_cfg_def, state_equiv_cfg_refl]
        )
        >- fs[resolve_phi_def]
      )
    )
    >- (
      fs[simplify_phi_inst_def, step_inst_def] >>
      Cases_on `eval_operand val_op s` >>
      simp[result_equiv_cfg_def, state_equiv_cfg_refl]
    )
  )
QED

Theorem step_inst_simplify_phi:
  !preds preds0 bb inst s prev.
    MEM inst bb.bb_instructions /\
    s.vs_prev_bb = SOME prev /\
    MEM prev preds /\
    (!lbl. MEM lbl preds ==> MEM lbl preds0) /\
    phi_block_wf preds0 bb
  ==>
    result_equiv_cfg (step_inst (simplify_phi_inst preds inst) s)
                     (step_inst inst s)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (
    drule_all phi_block_wf_inst >>
    strip_tac >>
    match_mp_tac step_inst_simplify_phi_inst >>
    qexists_tac `preds0` >> qexists_tac `prev` >> simp[]
  )
  >- (
    simp[simplify_phi_inst_def, result_equiv_cfg_def, state_equiv_cfg_refl] >>
    simp[result_equiv_cfg_refl]
  )
QED

Theorem step_inst_simplify_phi_ok:
  !preds preds0 bb inst s prev s'.
    MEM inst bb.bb_instructions /\
    s.vs_prev_bb = SOME prev /\
    MEM prev preds /\
    (!lbl. MEM lbl preds ==> MEM lbl preds0) /\
    phi_block_wf preds0 bb /\
    step_inst inst s = OK s' ==>
    step_inst (simplify_phi_inst preds inst) s = OK s'
Proof
  rpt strip_tac >>
  drule_all step_inst_simplify_phi >> simp[] >>
  strip_tac >>
  Cases_on `step_inst (simplify_phi_inst preds inst) s` >>
  gvs[result_equiv_cfg_def] >>
  rename1 `step_inst (simplify_phi_inst preds inst) s = OK s''` >>
  Cases_on `inst.inst_opcode = PHI`
  >- (
    `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
    `~is_terminator (simplify_phi_inst preds inst).inst_opcode` by
      simp[simplify_phi_inst_is_terminator, is_terminator_def] >>
    imp_res_tac step_inst_preserves_prev_bb >>
    imp_res_tac step_inst_preserves_current_bb >>
    imp_res_tac step_inst_preserves_inst_idx >>
    irule state_equiv_cfg_ctrl_eq >> simp[]
  )
  >- (
    simp[simplify_phi_inst_no_phi] >>
    qpat_x_assum `step_inst (simplify_phi_inst preds inst) s = OK s''` mp_tac >>
    simp[simplify_phi_inst_no_phi] >> strip_tac >>
    metis_tac[]
  )
QED

(* ===== PHI Simplification Preserves Step ===== *)

Theorem simplify_phi_block_label:
  !preds bb. (simplify_phi_block preds bb).bb_label = bb.bb_label
Proof
  rw[simplify_phi_block_def]
QED

Theorem simplify_phi_block_no_phi:
  !preds bb. block_has_no_phi bb ==> simplify_phi_block preds bb = bb
Proof
  rpt strip_tac >>
  simp[simplify_phi_block_def] >>
  Cases_on `bb` >>
  simp[] >>
  simp[basic_block_component_equality] >>
  gvs[block_has_no_phi_def, block_has_phi_def] >>
  Induct_on `l`
  >- simp[]
  >- (
    rpt strip_tac >>
    simp[] >>
    conj_tac
    >- (
      `h.inst_opcode <> PHI` by (
        spose_not_then assume_tac >>
        qpat_x_assum
          `!inst. inst.inst_opcode = PHI ==> ~MEM inst (h::l)`
          (qspec_then `h` mp_tac) >>
        simp[]) >>
      simp[simplify_phi_inst_no_phi])
    >- (
      qpat_x_assum
        `(!inst. inst.inst_opcode = PHI ==> ~MEM inst l) ==> _`
        match_mp_tac >>
      rpt strip_tac >>
      qpat_x_assum
        `!inst. inst.inst_opcode = PHI ==> ~MEM inst (h::l)`
        (qspec_then `inst` drule) >>
      simp[]))
QED

Theorem step_in_block_simplify_phi:
  !fn bb s preds preds0 res is_term prev.
    step_in_block bb s = (res, is_term) /\
    s.vs_prev_bb = SOME prev /\
    preds = pred_labels fn bb.bb_label /\
    MEM prev preds /\
    (!lbl. MEM lbl preds ==> MEM lbl preds0) /\
    phi_block_wf preds0 bb
  ==>
    ?res'. step_in_block (simplify_phi_block preds bb) s = (res', is_term) /\
           result_equiv_cfg res' res
Proof
  rpt strip_tac >>
  qpat_x_assum `step_in_block _ _ = _` mp_tac >>
  simp[step_in_block_def, simplify_phi_block_def] >>
  simp[get_instruction_def] >>
  IF_CASES_TAC >> gvs[]
  >- (
    qabbrev_tac `inst = EL s.vs_inst_idx bb.bb_instructions` >>
    simp[EL_MAP] >>
    simp[simplify_phi_inst_is_terminator] >>
    strip_tac >> Cases_on `step_inst inst s` >> gvs[]
    >- (
      `MEM inst bb.bb_instructions` by
        (simp[MEM_EL] >> qexists_tac `s.vs_inst_idx` >> gvs[Abbr`inst`]) >>
      drule_all step_inst_simplify_phi >> strip_tac >>
      Cases_on `step_inst (simplify_phi_inst (pred_labels fn bb.bb_label) inst) s` >>
      gvs[result_equiv_cfg_def] >>
      IF_CASES_TAC >> gvs[]
      >- (simp[result_equiv_cfg_def] >> gvs[result_equiv_cfg_def] >>
          qpat_x_assum `OK v = _` (SUBST1_TAC o GSYM) >>
          simp[result_equiv_cfg_def])
      >- (simp[result_equiv_cfg_def] >> irule next_inst_state_equiv_cfg >> simp[]))
    >- (
      `MEM inst bb.bb_instructions` by
        (simp[MEM_EL] >> qexists_tac `s.vs_inst_idx` >> gvs[Abbr`inst`]) >>
      drule_all step_inst_simplify_phi >> strip_tac >>
      Cases_on `step_inst (simplify_phi_inst (pred_labels fn bb.bb_label) inst) s` >>
      gvs[result_equiv_cfg_def] >> gvs[result_equiv_cfg_def] >>
      qpat_x_assum `Halt _ = _` (SUBST_ALL_TAC o GSYM) >> fs[result_equiv_cfg_def])
    >- (
      `MEM inst bb.bb_instructions` by
        (simp[MEM_EL] >> qexists_tac `s.vs_inst_idx` >> gvs[Abbr`inst`]) >>
      drule_all step_inst_simplify_phi >> strip_tac >>
      Cases_on `step_inst (simplify_phi_inst (pred_labels fn bb.bb_label) inst) s` >>
      gvs[result_equiv_cfg_def] >> fs[result_equiv_cfg_def] >>
      qpat_x_assum `Revert _ = _` (SUBST_ALL_TAC o GSYM) >> fs[result_equiv_cfg_def])
    >- (
      `MEM inst bb.bb_instructions` by
        (simp[MEM_EL] >> qexists_tac `s.vs_inst_idx` >> gvs[Abbr`inst`]) >>
      drule_all step_inst_simplify_phi >> strip_tac >>
      Cases_on `step_inst (simplify_phi_inst (pred_labels fn bb.bb_label) inst) s` >>
      gvs[result_equiv_cfg_def] >>
      qpat_x_assum `Error _ = _` (SUBST_ALL_TAC o GSYM) >> fs[result_equiv_cfg_def]))
  >- simp[result_equiv_cfg_def]
QED

Theorem step_in_block_simplify_phi_ok:
  !fn bb s preds preds0 s' is_term prev.
    step_in_block bb s = (OK s', is_term) /\
    s.vs_prev_bb = SOME prev /\
    preds = pred_labels fn bb.bb_label /\
    MEM prev preds /\
    (!lbl. MEM lbl preds ==> MEM lbl preds0) /\
    phi_block_wf preds0 bb
  ==>
    step_in_block (simplify_phi_block preds bb) s = (OK s', is_term)
Proof
  rpt strip_tac >>
  qpat_x_assum `step_in_block bb s = _` mp_tac >>
  simp[step_in_block_def, simplify_phi_block_def] >>
  simp[get_instruction_def] >>
  IF_CASES_TAC >> gvs[] >>
  qabbrev_tac `inst = EL s.vs_inst_idx bb.bb_instructions` >>
  simp[EL_MAP] >>
  simp[simplify_phi_inst_is_terminator] >>
  strip_tac >>
  Cases_on `step_inst inst s` >> gvs[] >>
  `MEM inst bb.bb_instructions` by
    (simp[MEM_EL] >> qexists_tac `s.vs_inst_idx` >> gvs[Abbr`inst`]) >>
  drule_all step_inst_simplify_phi_ok >> strip_tac >> gvs[]
QED

val _ = export_theory();
