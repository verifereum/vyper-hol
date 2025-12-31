(* 
 * Simplify-CFG PHI Run-Block Correctness
 *
 * run_block equivalence lemmas for simplify-phi.
 *)

Theory scfgPhiRunBlock
Ancestors
  scfgPhiStep

Theorem run_block_simplify_phi:
  !fn bb s preds preds0 prev.
    s.vs_prev_bb = SOME prev /\
    preds = pred_labels fn bb.bb_label /\
    MEM prev preds /\
    (!lbl. MEM lbl preds ==> MEM lbl preds0) /\
    phi_block_wf preds0 bb
  ==>
    result_equiv_cfg (run_block fn (simplify_phi_block preds bb) s)
                     (run_block fn bb s)
Proof
  ho_match_mp_tac run_block_ind >>
  rpt gen_tac >> strip_tac >>
  rpt strip_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s` >> Cases_on `q` >> simp[] >>
  strip_tac >>
  drule_all step_in_block_simplify_phi >> strip_tac >>
  gvs[] >>
  Cases_on `res'` >> gvs[result_equiv_cfg_def] >>
  rename1 `res' = OK v'` >>
  Cases_on `v.vs_halted` >> gvs[]
  >- (
    qexists_tac `Halt v'` >>
    gvs[result_equiv_cfg_def]
  )
  >- (
    Cases_on `r` >> gvs[]
    >- (
      qexists_tac `OK v'` >>
      gvs[result_equiv_cfg_def]
    )
    >- (
      `v.vs_prev_bb = s.vs_prev_bb` by (
        qpat_x_assum `step_in_block fn bb s = (OK v,F)` mp_tac >>
        simp[step_in_block_def] >>
        Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
        Cases_on `step_inst x s` >> gvs[] >>
        gvs[next_inst_def] >>
        drule_all step_inst_preserves_prev_bb >> simp[]
      ) >>
      `v.vs_current_bb = s.vs_current_bb` by (
        qpat_x_assum `step_in_block fn bb s = (OK v,F)` mp_tac >>
        simp[step_in_block_def] >>
        Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
        Cases_on `step_inst x s` >> gvs[] >>
        gvs[next_inst_def] >>
        drule_all step_inst_preserves_current_bb >> simp[]
      ) >>
      `v.vs_inst_idx = s.vs_inst_idx + 1` by (
        qpat_x_assum `step_in_block fn bb s = (OK v,F)` mp_tac >>
        simp[step_in_block_def] >>
        Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
        Cases_on `step_inst x s` >> gvs[] >>
        gvs[next_inst_def] >>
        drule_all step_inst_preserves_inst_idx >> simp[]
      ) >>
      `v'.vs_prev_bb = s.vs_prev_bb` by (
        qpat_x_assum `step_in_block fn (simplify_phi_block preds bb) s = (OK v',F)` mp_tac >>
        simp[step_in_block_def, simplify_phi_block_def] >>
        Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
        rename1 `get_instruction bb _ = SOME inst` >>
        qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
        simp[get_instruction_def] >> strip_tac >>
        `get_instruction (bb with bb_instructions := MAP (simplify_phi_inst preds) bb.bb_instructions)
                         s.vs_inst_idx = SOME (simplify_phi_inst preds inst)` by
          (rw[get_instruction_def] >> simp[EL_MAP]) >>
        simp[] >>
        Cases_on `step_inst (simplify_phi_inst preds inst) s` >> gvs[] >>
        gvs[next_inst_def] >>
        drule_all step_inst_preserves_prev_bb >> simp[]
      ) >>
      `v'.vs_current_bb = s.vs_current_bb` by (
        qpat_x_assum `step_in_block fn (simplify_phi_block preds bb) s = (OK v',F)` mp_tac >>
        simp[step_in_block_def, simplify_phi_block_def] >>
        Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
        rename1 `get_instruction bb _ = SOME inst` >>
        qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
        simp[get_instruction_def] >> strip_tac >>
        `get_instruction (bb with bb_instructions := MAP (simplify_phi_inst preds) bb.bb_instructions)
                         s.vs_inst_idx = SOME (simplify_phi_inst preds inst)` by
          (rw[get_instruction_def] >> simp[EL_MAP]) >>
        simp[] >>
        Cases_on `step_inst (simplify_phi_inst preds inst) s` >> gvs[] >>
        gvs[next_inst_def] >>
        drule_all step_inst_preserves_current_bb >> simp[]
      ) >>
      `v'.vs_inst_idx = s.vs_inst_idx + 1` by (
        qpat_x_assum `step_in_block fn (simplify_phi_block preds bb) s = (OK v',F)` mp_tac >>
        simp[step_in_block_def, simplify_phi_block_def] >>
        Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
        rename1 `get_instruction bb _ = SOME inst` >>
        qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
        simp[get_instruction_def] >> strip_tac >>
        `get_instruction (bb with bb_instructions := MAP (simplify_phi_inst preds) bb.bb_instructions)
                         s.vs_inst_idx = SOME (simplify_phi_inst preds inst)` by
          (rw[get_instruction_def] >> simp[EL_MAP]) >>
        simp[] >>
        Cases_on `step_inst (simplify_phi_inst preds inst) s` >> gvs[] >>
        gvs[next_inst_def] >>
        drule_all step_inst_preserves_inst_idx >> simp[]
      ) >>
      `v' = v` by (irule state_equiv_cfg_ctrl_eq >> simp[]) >>
      first_x_assum (qspec_then `v` mp_tac) >> simp[]
    )
  )
QED

Theorem run_block_simplify_phi_ok:
  !fn bb s preds preds0 prev s'.
    s.vs_prev_bb = SOME prev /\
    preds = pred_labels fn bb.bb_label /\
    MEM prev preds /\
    (!lbl. MEM lbl preds ==> MEM lbl preds0) /\
    phi_block_wf preds0 bb /\
    run_block fn bb s = OK s' ==>
    run_block fn (simplify_phi_block preds bb) s = OK s'
Proof
  ho_match_mp_tac run_block_ind >> rpt strip_tac >>
  qpat_x_assum `run_block _ _ _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s` >> Cases_on `q` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[] >>
  Cases_on `r` >> simp[] >- (
    (* Terminator case *)
    qpat_x_assum `step_in_block fn bb s = (OK v,T)` mp_tac >>
    drule_all step_in_block_simplify_phi_ok >>
    simp[step_in_block_def]
  ) >>
  (* Non-terminal case *)
  qpat_x_assum `step_in_block fn bb s = (OK v,F)` mp_tac >>
  drule_all step_in_block_simplify_phi_ok >>
  simp[step_in_block_def] >> strip_tac >>
  `v.vs_prev_bb = s.vs_prev_bb` by
    (drule_all step_in_block_preserves_prev_bb >> simp[]) >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[]
QED

val _ = export_theory();
